/**
 * An example of a Type-Handler implementation.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier.IASTEnumerator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTParameterDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTTypeId;
import org.eclipse.cdt.core.dom.ast.IArrayType;
import org.eclipse.cdt.core.dom.ast.IBasicType;
import org.eclipse.cdt.core.dom.ast.ITypedef;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTTypedefNameSpecifier;
import org.eclipse.cdt.internal.core.dom.parser.c.CPointerType;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.SymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 07.02.2012
 */
public class TypeHandler implements ITypeHandler {
    /**
     * Maps the cIdentifier of a struct, enumeration, or union (when this is
     *  implemented) to the ResultType that represents this type at the moment
     */
    private final Map<String, ResultTypes> m_DefinedTypes;
    /**
     * Undefined struct types.
     */
    private HashSet<String> m_IncompleteType;
    /**
     * counting levels of struct declaration.
     */
    private int structCounter;

    /**
     * Constructor.
     */
    public TypeHandler() {
        this.m_DefinedTypes = new HashMap<String, ResultTypes>();
        this.m_IncompleteType = new HashSet<String>();
    }

    @Override
    public boolean isStructDeclaration() {
        assert structCounter >= 0;
        return structCounter != 0;
    }

    @Override
    public Result visit(Dispatcher main, IASTNode node) {
        String msg = "TypeHandler: Not yet implemented: " + node.toString();
        Dispatcher.error(new CACSLLocation(node),
                SyntaxErrorType.UnsupportedSyntax, msg);
        throw new UnsupportedSyntaxException(msg);
    }

    /**
     * @deprecated is not supported in this handler! Do not use!
     */
    @Override
    public Result visit(Dispatcher main, ACSLNode node) {
        throw new UnsupportedOperationException(
                "Implementation Error: use ACSL handler for " + node.getClass());
    }

    @Override
    public Result visit(Dispatcher main, IASTSimpleDeclSpecifier node) {
        ResultTypes result;
        CType cvar = new CPrimitive(node);
        // we have model.boogie.ast.PrimitiveType, which should
        // only contain BOOL, INT, REAL ...
        CACSLLocation loc = new CACSLLocation(node);
		switch (node.getType()) {
            case IASTSimpleDeclSpecifier.t_void:
                // there is no void in Boogie,
                // so we simply have no result variable.
                result = (new ResultTypes(null, false, true, cvar));
                break;
//            case IASTSimpleDeclSpecifier.t_bool:
//                // so bool is clearly a primitive type
//                result = (new ResultTypes(new PrimitiveType(new CACSLLocation(
//                        node), SFO.BOOL), node.isConst(), false, cvar));
//                break;
            case IASTSimpleDeclSpecifier.t_unspecified:
            	Dispatcher.warn(loc, "unspecified type, defaulting to int", 
            			"unspecified type, defaulting to int");
            case IASTSimpleDeclSpecifier.t_bool:
            case IASTSimpleDeclSpecifier.t_int:
                // so int is also a primitive type
                // NOTE: in a extended implementation we should
                // handle here different types of int (short, long,...)
                result = (new ResultTypes(new PrimitiveType(loc, SFO.INT), node.isConst(), false, cvar));
                break;
            case IASTSimpleDeclSpecifier.t_double:
                // floating point number are not supported by Ultimate,
                // somehow we treat it here as REALs
                result = (new ResultTypes(new PrimitiveType(loc, SFO.REAL), node.isConst(), false, cvar));
                break;
            case IASTSimpleDeclSpecifier.t_float:
                // floating point number are not supported by Ultimate,
                // somehow we treat it here as REALs
                result = (new ResultTypes(new PrimitiveType(loc, SFO.REAL), node.isConst(), false, cvar));
                break;
            case IASTSimpleDeclSpecifier.t_char:
                // how to handle chars? Will use int ...
                result = (new ResultTypes(new PrimitiveType(loc, SFO.INT), node.isConst(), false, cvar));
                break;
            default:
                // long, long long, and short are the same as int, iff there are
                // no restrictions / asserts in boogie
                if (node.isLongLong() || node.isLong() || node.isShort()
                        || node.isUnsigned()) {
                    result = (new ResultTypes(new PrimitiveType(
                            loc, SFO.INT), node.isConst(),
                            false, cvar));
                    break;
                }
                // if we do not find a type we cancel with Exception
                String msg = "TypeHandler: We do not support this type!"
                        + node.getType();
                Dispatcher.error(loc,
                        SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
        }
        if (node.getStorageClass() == IASTDeclSpecifier.sc_typedef) {
            // TYPEDEF Simple types
            for (IASTDeclarator cDecl : ((IASTSimpleDeclaration) node
                    .getParent()).getDeclarators()) {
                String typedefId = cDecl.getName().getRawSignature();
                ResultTypes checkedResult = main.cHandler.checkForPointer(main, 
                		cDecl.getPointerOperators(), result, false);
                m_DefinedTypes.put(typedefId, checkedResult);
                
            }
            // TODO : add an axiom for sizeOf(typedefId) == sizeOf(result.t);?
            // I think, the axiom is not required, as we resolve the type
            // anyway?
            return new ResultSkip();
        }
        if (!result.isVoid) {
            main.cHandler.addSizeOfConstants(result.cvar);
        }
        return result;
    }

    @Override
    public Result visit(Dispatcher main, IASTNamedTypeSpecifier node) {
        CACSLLocation loc = new CACSLLocation(node);
        if (node instanceof CASTTypedefNameSpecifier) {
            node = (CASTTypedefNameSpecifier) node;
            String type = node.getName().toString();
            String id;
            if (node.getParent() instanceof IASTSimpleDeclaration) {
                id = ((IASTSimpleDeclaration) node.getParent())
                        .getDeclarators()[0].getName().toString();
            } else if (node.getParent() instanceof IASTParameterDeclaration) {
                id = ((IASTParameterDeclaration) node.getParent())
                        .getDeclarator().getName().toString();
            } else if (node.getParent() instanceof IASTFunctionDefinition) {
                id = ((IASTFunctionDefinition) node.getParent())
                        .getDeclarator().getName().toString();
            } else if (node.getParent() instanceof IASTTypeId) {
                id = ((IASTTypeId) node.getParent()).getAbstractDeclarator()
                        .getName().toString();
            } else {
                String msg = "The context of this IASTNamedTypeSpecifier is unexpected! ["
                        + node.getParent().getClass() + "]";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
            }
            if ((node.getStorageClass() != IASTDeclSpecifier.sc_typedef)) {
                if (!m_DefinedTypes.containsKey(type)) {
                    String msg = "Typedef missing for: " + type;
                    Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
                    throw new IncorrectSyntaxException(msg);
                }
                ResultTypes mapped = m_DefinedTypes.get(type);
                CNamed cvar = new CNamed(node, mapped.cvar);
                assert mapped.typeDeclarations.isEmpty();
                ResultTypes res = new ResultTypes(mapped.getType(),
                        mapped.isConst, mapped.isVoid, cvar);
                if (!res.isVoid) {
                    main.cHandler.addSizeOfConstants(res.cvar);
                }
                return res;
            }
            m_DefinedTypes.put(id, m_DefinedTypes.get(type));
            // TODO : add an axiom for sizeOf(typedefId) == sizeOf(result.t);?
            // I think, the axiom is not required, as we resolve the type
            // anyway?
            return new ResultSkip();
        }
        String msg = "Unknown or unsupported type! " + node.toString();
        Dispatcher.error(new CACSLLocation(node),
                SyntaxErrorType.UnsupportedSyntax, msg);
        throw new UnsupportedSyntaxException(msg);
    }

    @Override
    public Result visit(Dispatcher main, IASTEnumerationSpecifier node) {
        CACSLLocation loc = new CACSLLocation(node);
        String enumId = node.getName().getRawSignature();
        int nrFields = node.getEnumerators().length;
        String[] fNames = new String[nrFields];
        IASTExpression[] fValues = new IASTExpression[nrFields];
        for (int i = 0; i < nrFields; i++) {
            IASTEnumerator e = node.getEnumerators()[i];
            fNames[i] = e.getName().getRawSignature();
            fValues[i] = e.getValue();
        }
        CEnum cEnum = new CEnum(node, enumId, fNames, fValues);
        IType it = new InferredType(Type.Integer);
        ASTType at = new PrimitiveType(loc, it, SFO.INT);
        ResultTypes result = new ResultTypes(at, false, false, cEnum);
        if (!enumId.equals(SFO.EMPTY)) {
            m_DefinedTypes.put(enumId, result);
        }
        main.cHandler.addSizeOfConstants(result.cvar);
        return result;
    }
    
    

    
    
    @Override
    public Result visit(Dispatcher main, IASTElaboratedTypeSpecifier node) {
        CACSLLocation loc = new CACSLLocation(node);
        if (node.getKind() == IASTElaboratedTypeSpecifier.k_struct
                || node.getKind() == IASTElaboratedTypeSpecifier.k_enum
                || node.getKind() == IASTElaboratedTypeSpecifier.k_union) {
            String type = node.getName().getRawSignature();
            String name;
            if (node.getKind() == IASTElaboratedTypeSpecifier.k_struct) {
            	name = "STRUCT~" + type;
            } else if (node.getKind() == IASTElaboratedTypeSpecifier.k_union) {
            	name = "UNION~" + type;
            } else {
            	throw new UnsupportedOperationException("TODO: enums");
            }
            
            if (m_DefinedTypes.containsKey(type)) {
                if (node.getStorageClass() == IASTDeclSpecifier.sc_typedef) {
                    assert node.getParent() instanceof IASTSimpleDeclaration;
                    IASTDeclarator[] decls = ((IASTSimpleDeclaration) node
                            .getParent()).getDeclarators();
                    for (IASTDeclarator decl : decls) {
                        String key = decl.getName().getRawSignature();
                        if (!key.equals(SFO.EMPTY))
                            m_DefinedTypes.put(key, m_DefinedTypes.get(type));
                    }
                    // TODO : add an axiom for sizeOf(typedefId) ==
                    // sizeOf(result.t);?
                    // I think, the axiom is not required, as we resolve the
                    // type anyway?
                    return new ResultSkip();
                }
                ResultTypes originalType = m_DefinedTypes.get(type);
                ResultTypes withoutBoogieTypedef = new ResultTypes(
                		originalType.getType(), originalType.isConst, 
                		originalType.isVoid, originalType.cvar);
                return withoutBoogieTypedef;
            }

            // This is a definition of an incomplete struct or enum.
            m_IncompleteType.add(name);
// 			FIXME : not sure, if null is a good idea!
//            ResultTypes r = new ResultTypes(new NamedType(loc, name,
//                    new ASTType[0]), false, false, null);
            if (node.getKind() == IASTElaboratedTypeSpecifier.k_enum) {
            	throw new UnsupportedOperationException("TODO: support incomplete enums");
            }
            CType ctype;
            if (node.getKind() == IASTElaboratedTypeSpecifier.k_struct) {
            	ctype = new CStruct(node, true);
            } else if (node.getKind() == IASTElaboratedTypeSpecifier.k_union) {
            	ctype = new CUnion(node, true);
            } else {
            	throw new UnsupportedOperationException("TODO: enums");
            }
            ResultTypes r = new ResultTypes(new NamedType(loc, name,
                  new ASTType[0]), false, false, ctype);
            

            m_DefinedTypes.put(type, r);
// 	I think the following is obsolete, we always want to add the defined type.
//  Maybe the following was relevant for enums.             
//            IASTDeclarator[] decls;
//            if (node.getParent() instanceof IASTSimpleDeclaration) {
//                decls = ((IASTSimpleDeclaration) node.getParent())
//                        .getDeclarators();
//            } else if (node.getParent() instanceof IASTParameterDeclaration) {
//                decls = new IASTDeclarator[] { ((IASTParameterDeclaration) node
//                        .getParent()).getDeclarator() };
//            } else {
//                String msg = "Unepected parent for IASTElaboratedTypeSpecifier";
//                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
//                throw new UnsupportedSyntaxException(msg);
//            }
//            for (IASTDeclarator decl : decls) {
//                String key = decl.getName().getRawSignature();
//                if (!key.equals(SFO.EMPTY))
//                    m_DefinedTypes.put(key, r);
//            }
            
            
// do not add incompletes to sizeOf constants!
//          	main.cHandler.addSizeOfConstants(r.cvar);
            return r;
        }
        String msg = "Not yet implemented: Spec [" + node.getKind() + "] of "
                + node.getClass();
        Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
        throw new UnsupportedSyntaxException(msg);
    }
    
  
    
    @Override
    public Result visit(Dispatcher main, IASTCompositeTypeSpecifier node) {
        CACSLLocation loc = new CACSLLocation(node);
        ArrayList<VarList> fields = new ArrayList<VarList>();
        // TODO : include inactives? what are inactives?
        ArrayList<String> fNames = new ArrayList<String>();
        ArrayList<CType> fTypes = new ArrayList<CType>();
        structCounter++;
        for (IASTDeclaration dec : node.getDeclarations(false)) {
            Result r = main.dispatch(dec);
            if (r instanceof ResultExpression) {
                ResultExpression rex = (ResultExpression) r;
                //assert rex.stmt == null || rex.stmt.isEmpty();
                assert rex.lrVal == null;
//                assert rex.expr == null;
                assert rex.declCTypes.size() == rex.decl.size();
                int i = 0;
                for (Declaration field : rex.decl) {
                    if (field instanceof VariableDeclaration) {
                        VariableDeclaration vd = (VariableDeclaration) field;
                        for (VarList vl : vd.getVariables()) {
                            fields.add(vl);
                            assert vl.getIdentifiers().length == 1;
                            // this assert should hold by construction!
                            for (String id : vl.getIdentifiers()) {
                                fNames.add(id);
                                fTypes.add(rex.declCTypes.get(i++));
                            }
                        }
                    } else {
                        String msg = "Unexpected declaration of struct field!";
                        Dispatcher.error(loc,
                                SyntaxErrorType.UnsupportedSyntax, msg);
                        throw new UnsupportedSyntaxException(msg);
                    }
                }
            } else if (r instanceof ResultSkip) { // skip ;)
            } else {
                String msg = "Unexpected syntax in struct declaration!";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
            }
        }
        structCounter--;
        String cId = node.getName().toString();
        String name = "STRUCT~" + cId;
        NamedType namedType = new NamedType(loc, name,
                new ASTType[0]);
                
//        ASTType type = new StructType(loc, fields.toArray(new VarList[0]));
//        TypeDeclaration structDeclaration = new TypeDeclaration(loc, new Attribute[0], false,
//                SFO.POINTER, new String[0], new StructType(loc, fields.toArray(new VarList[0])));
        
        ASTType type = namedType;
        CStruct cvar;
        if (node.getKey() == IASTCompositeTypeSpecifier.k_struct) {
        	cvar = new CStruct(node, fNames.toArray(new String[0]),
                    fTypes.toArray(new CType[0]));
        } else if (node.getKey() == IASTCompositeTypeSpecifier.k_union) {
        	cvar = new CUnion(node, fNames.toArray(new String[0]),
                    fTypes.toArray(new CType[0]));
        } else {
        	throw new UnsupportedOperationException();
        }
        ResultTypes result = new ResultTypes(type, false, false, cvar);
        
        if (node.getStorageClass() == IASTDeclSpecifier.sc_typedef) {
            // TYPEDEF Struct Type
            for (IASTDeclarator cDecl : ((IASTSimpleDeclaration) node
                    .getParent()).getDeclarators()) {
                String typedefId = cDecl.getName().getRawSignature();
                ResultTypes checkedResult = main.cHandler.checkForPointer(main, 
                		cDecl.getPointerOperators(), result, false);
                m_DefinedTypes.put(typedefId, checkedResult);
            }
            if (m_DefinedTypes.containsKey(cId)) {
            	// the type itself was already defined
            	return new ResultSkip();
            }
        }
        ArrayList<TypeDeclaration> tds = new ArrayList<TypeDeclaration>();
        
        if (m_IncompleteType.contains(name)) {
            m_IncompleteType.remove(name);
            ResultTypes incompleteType = m_DefinedTypes.get(cId);
            CStruct incompleteStruct = (CStruct) incompleteType.cvar;
            incompleteStruct.complete(cvar);
//            Matthias: 3.11.2013 I think the following is not supported
//			  because Alex and Jochen have removed type declarations for structs            

        }
        tds.add(new TypeDeclaration(loc, new Attribute[0], false, name,
                new String[0], new StructType(loc, fields.toArray(new VarList[0]))));
        result.addTypeDeclarations(tds);
        
        if (!cId.equals(SFO.EMPTY)) {
            m_DefinedTypes.put(cId, result);
        }
        main.cHandler.addSizeOfConstants(result.cvar);
        return result;
    }

    @Override
    public InferredType visit(Dispatcher main,
            org.eclipse.cdt.core.dom.ast.IType type) {
    	if (type instanceof CPointerType) {
    		return new InferredType(Type.Pointer);
    	} else {
    		// Handle the generic case of IType, if the specific case is not yet
    		// implemented
    		String msg = "TypeHandler: Not yet implemented: "
    				+ type.getClass().toString();
    		// TODO : no idea what location should be set to ...
    		Dispatcher.error(null, SyntaxErrorType.UnsupportedSyntax, msg);
    		return new InferredType(Type.Unknown);
    	}
    }

    @Override
    public InferredType visit(Dispatcher main, ITypedef type) {
        if (!m_DefinedTypes.containsKey(type.getName())) {
            String msg = "Unknown C typedef: " + type.getName();
            // TODO : no idea what location should be set to ...
            Dispatcher.error(null, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
        }
        return new InferredType(m_DefinedTypes.get(type.getName()).getType());
    }

    @Override
    public InferredType visit(final Dispatcher main, final IBasicType type) {
        switch (type.getKind()) {
            case eBoolean:
                return new InferredType(Type.Boolean);
            case eChar:
            case eChar16:
            case eChar32:
            case eInt:
                return new InferredType(Type.Integer);
            case eDouble:
            case eFloat:
                return new InferredType(Type.Real);
            case eWChar: // TODO : verify! Not sure what WChar means!
                return new InferredType(Type.String);
            case eVoid:
                return new InferredType(Type.Void);
            case eUnspecified:
            default:
                return new InferredType(Type.Unknown);
        }
    }

    @Override
    public ASTType getTypeOfStructLHS(final SymbolTable sT,
            final ILocation loc, final StructLHS lhs) {
        String[] flat = BoogieASTUtil.getLHSList(lhs);
        String leftMostId = flat[0];
        assert leftMostId.equals(BoogieASTUtil.getLHSId(lhs));
        assert sT.containsBoogieSymbol(leftMostId);
        String cId = sT.getCID4BoogieID(leftMostId, loc);
        assert sT.containsKey(cId);
        ASTType t = sT.getTypeOfVariable(cId, loc);
        // assert t instanceof StructType;
        return traverseForType(loc, t, flat, 1);
    }

    /**
     * Returns the type of the field in the struct.
     * 
     * @param loc
     *            the location, where errors should be set, if there are any!
     * @param t
     *            the type to process.
     * @param flat
     *            the flattend LHS.
     * @param i
     *            index in flat[].
     * @return the type of the field.
     */
    private static ASTType traverseForType(final ILocation loc,
            final ASTType t, final String[] flat, final int i) {
        assert i > 0 && i <= flat.length;
        if (i >= flat.length)
            return t;
        if (t instanceof ArrayType)
            return traverseForType(loc, ((ArrayType) t).getValueType(), flat, i);
        if (t instanceof StructType) {
            for (VarList vl : ((StructType) t).getFields()) {
                assert vl.getIdentifiers().length == 1;
                // should hold by construction!
                if (vl.getIdentifiers()[0].equals(flat[i])) {
                    // found the field!
                    return traverseForType(loc, vl.getType(), flat, i + 1);
                }
            }
            String msg = "Field '" + flat[i] + "' not found in " + t;
            Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
        }
        String msg = "Something went wrong while determining types!";
        Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
        throw new UnsupportedSyntaxException(msg);
    }

    @Override
    public InferredType visit(Dispatcher main, IArrayType type) {
        return main.dispatch(type.getType());
    }

    @Override
    public Set<String> getUndefinedTypes() {
        return m_IncompleteType;
    }
}
