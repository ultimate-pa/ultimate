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

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.SymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
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
     * Map to resolve typedefs.
     * Matthias: I think this name is misleading. We use this not only to store
     * explicit typedefs, but also to store structs like the following.
     * struct fraction {
	 *   int numerator;
	 *   int denominator;
     * }
     */
    private final Map<String, ResultTypes> typedef;
    /**
     * Undefined struct types.
     */
    private HashSet<String> undefStructs;
    /**
     * counting levels of struct declaration.
     */
    private int structCounter;

    /**
     * Constructor.
     */
    public TypeHandler() {
        this.typedef = new HashMap<String, ResultTypes>();
        this.undefStructs = new HashSet<String>();
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
        switch (node.getType()) {
            case IASTSimpleDeclSpecifier.t_void:
                // there is no void in Boogie,
                // so we simply have no result variable.
                result = (new ResultTypes(null, false, true, cvar));
                break;
            case IASTSimpleDeclSpecifier.t_bool:
                // so bool is clearly a primitive type
                result = (new ResultTypes(new PrimitiveType(new CACSLLocation(
                        node), SFO.BOOL), node.isConst(), false, cvar));
                break;
            case IASTSimpleDeclSpecifier.t_int:
                // so int is also a primitive type
                // NOTE: in a extended implementation we should
                // handle here different types of int (short, long,...)
                result = (new ResultTypes(new PrimitiveType(new CACSLLocation(
                        node), SFO.INT), node.isConst(), false, cvar));
                break;
            case IASTSimpleDeclSpecifier.t_double:
                // floating point number are not supported by Ultimate,
                // somehow we treat it here as REALs
                result = (new ResultTypes(new PrimitiveType(new CACSLLocation(
                        node), SFO.REAL), node.isConst(), false, cvar));
                break;
            case IASTSimpleDeclSpecifier.t_float:
                // floating point number are not supported by Ultimate,
                // somehow we treat it here as REALs
                result = (new ResultTypes(new PrimitiveType(new CACSLLocation(
                        node), SFO.REAL), node.isConst(), false, cvar));
                break;
            case IASTSimpleDeclSpecifier.t_char:
                // how to handle chars? Will use int ...
                result = (new ResultTypes(new PrimitiveType(new CACSLLocation(
                        node), SFO.INT), node.isConst(), false, cvar));
                break;
            default:
                // long, long long, and short are the same as int, iff there are
                // no restrictions / asserts in boogie
                if (node.isLongLong() || node.isLong() || node.isShort()
                        || node.isUnsigned()) {
                    result = (new ResultTypes(new PrimitiveType(
                            new CACSLLocation(node), SFO.INT), node.isConst(),
                            false, cvar));
                    break;
                }
                // if we do not find a type we cancel with Exception
                String msg = "TypeHandler: We do not support this type!"
                        + node.getType();
                Dispatcher.error(new CACSLLocation(node),
                        SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
        }
        if (node.getStorageClass() == IASTDeclSpecifier.sc_typedef) {
            // TYPEDEF Simple types
            for (IASTDeclarator cDecl : ((IASTSimpleDeclaration) node
                    .getParent()).getDeclarators()) {
                String typedefId = cDecl.getName().getRawSignature();
                ResultTypes checkedResult = main.cHandler.checkForPointer(main, cDecl.getPointerOperators(), result);
                typedef.put(typedefId, checkedResult);
                
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
            String type = node.getName().getRawSignature();
            String id;
            if (node.getParent() instanceof IASTSimpleDeclaration) {
                id = ((IASTSimpleDeclaration) node.getParent())
                        .getDeclarators()[0].getName().getRawSignature();
            } else if (node.getParent() instanceof IASTParameterDeclaration) {
                id = ((IASTParameterDeclaration) node.getParent())
                        .getDeclarator().getName().getRawSignature();
            } else if (node.getParent() instanceof IASTFunctionDefinition) {
                id = ((IASTFunctionDefinition) node.getParent())
                        .getDeclarator().getName().getRawSignature();
            } else if (node.getParent() instanceof IASTTypeId) {
                id = ((IASTTypeId) node.getParent()).getAbstractDeclarator()
                        .getName().getRawSignature();
            } else {
                String msg = "The context of this IASTNamedTypeSpecifier is unexpected! ["
                        + node.getParent().getClass() + "]";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
            }
            if ((node.getStorageClass() != IASTDeclSpecifier.sc_typedef)) {
                if (!typedef.containsKey(type)) {
                    String msg = "Typedef missing for: " + type;
                    Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
                    throw new IncorrectSyntaxException(msg);
                }
                ResultTypes mapped = typedef.get(type);
                CNamed cvar = new CNamed(node, mapped.cvar);
                assert mapped.typeDeclarations.isEmpty();
                ResultTypes res = new ResultTypes(mapped.getType(),
                        mapped.isConst, mapped.isVoid, cvar);
                if (!res.isVoid) {
                    main.cHandler.addSizeOfConstants(res.cvar);
                }
                return res;
            }
            typedef.put(id, typedef.get(type));
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
            typedef.put(enumId, result);
        }
        main.cHandler.addSizeOfConstants(result.cvar);
        return result;
    }
    
    

    
    
    @Override
    public Result visit(Dispatcher main, IASTElaboratedTypeSpecifier node) {
        CACSLLocation loc = new CACSLLocation(node);
        if (isSelfReferencingPointerToStruct(node)) {
        	return auxiliaryResultForSelfReferencingStruct(loc, node);
        }
        if (node.getKind() == IASTElaboratedTypeSpecifier.k_struct
                || node.getKind() == IASTElaboratedTypeSpecifier.k_enum) {
            String type = node.getName().getRawSignature();
            if (typedef.containsKey(type)) {
                if (node.getStorageClass() == IASTDeclSpecifier.sc_typedef) {
                    assert node.getParent() instanceof IASTSimpleDeclaration;
                    IASTDeclarator[] decls = ((IASTSimpleDeclaration) node
                            .getParent()).getDeclarators();
                    for (IASTDeclarator decl : decls) {
                        String key = decl.getName().getRawSignature();
                        if (!key.equals(SFO.EMPTY))
                            typedef.put(key, typedef.get(type));
                    }
                    // TODO : add an axiom for sizeOf(typedefId) ==
                    // sizeOf(result.t);?
                    // I think, the axiom is not required, as we resolve the
                    // type anyway?
                    return new ResultSkip();
                }
                return typedef.get(type);
            }
            String name = "STRUCT~" + type;
            undefStructs.add(name);
            ResultTypes r = new ResultTypes(new NamedType(loc, name,
                    new ASTType[0]), false, false, null);
            // FIXME : not sure, if null is a good idea!
            IASTDeclarator[] decls;
            if (node.getParent() instanceof IASTSimpleDeclaration) {
                decls = ((IASTSimpleDeclaration) node.getParent())
                        .getDeclarators();
            } else if (node.getParent() instanceof IASTParameterDeclaration) {
                decls = new IASTDeclarator[] { ((IASTParameterDeclaration) node
                        .getParent()).getDeclarator() };
            } else {
                String msg = "Unepected parent for IASTElaboratedTypeSpecifier";
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
            }
            for (IASTDeclarator decl : decls) {
                String key = decl.getName().getRawSignature();
                if (!key.equals(SFO.EMPTY))
                    typedef.put(key, r);
            }
           	main.cHandler.addSizeOfConstants(r.cvar);
            return r;
        }
        String msg = "Not yet implemented: Spec [" + node.getKind() + "] of "
                + node.getClass();
        Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
        throw new UnsupportedSyntaxException(msg);
    }
    
    /**
     * Returns true if node is a field of struct which points to the struct 
     * itself. E.g.
     * struct listElement {
     *    int data;
     *    struct listElement *le;
     *    }
     */
    private boolean isSelfReferencingPointerToStruct(IASTElaboratedTypeSpecifier node) {
    	if (node.getKind() != IASTElaboratedTypeSpecifier.k_struct) {
    		return false;
    	}
    	if (!(node.getParent().getParent() instanceof IASTCompositeTypeSpecifier)) {
    		return false;
    	}
    	String parentId = ((IASTCompositeTypeSpecifier) 
    			node.getParent().getParent()).getName().getRawSignature();
    	if (parentId.equals(node.getName().getRawSignature())) {
    		return true;
    	}
    	return false;
    }
    
    /**
     * Returns an auxiliary result for the case where we have a field of a 
     * struct that points to the struct itself. E.g.
     * struct listElement {
     *    int data;
     *    struct listElement *le;
     *    }
     * This result is used for the type of the inner element.
     */
    private ResultTypes auxiliaryResultForSelfReferencingStruct(
    				CACSLLocation loc, IASTElaboratedTypeSpecifier node) {
    	String aux = "auxiliaryResultForSelfReferencingStruct";
    	String[] fName = { aux };
    	CType[] ftype = { };
    	CStruct cStruct = new CStruct((IASTDeclSpecifier) 
    			node.getParent().getParent(), fName, ftype);
    	ASTType auxType = new StructType(loc, new VarList[0]);
    	return new ResultTypes(auxType, false, false, cStruct);
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
        ASTType type = new StructType(loc, fields.toArray(new VarList[0]));
        CType cvar = new CStruct(node, fNames.toArray(new String[0]),
                fTypes.toArray(new CType[0]));
        ResultTypes result = new ResultTypes(type, false, false, cvar);
        String cId = node.getName().getRawSignature();
        if (node.getStorageClass() == IASTDeclSpecifier.sc_typedef) {
            // TYPEDEF Struct Type
            for (IASTDeclarator cDecl : ((IASTSimpleDeclaration) node
                    .getParent()).getDeclarators()) {
                String typedefId = cDecl.getName().getRawSignature();
                ResultTypes checkedResult = main.cHandler.checkForPointer(main, 
                		cDecl.getPointerOperators(), result);
                typedef.put(typedefId, checkedResult);
            }
            if (typedef.containsKey(cId)) {
            	// the type itself was already defined
            	return new ResultSkip();
            }
        }
        ArrayList<TypeDeclaration> tds = new ArrayList<TypeDeclaration>();
        String name = "STRUCT~" + cId;
        if (undefStructs.contains(name)) {
            undefStructs.remove(name);
            tds.add(new TypeDeclaration(loc, new Attribute[0], false, name,
                    new String[0], type));
        }
        result.addTypeDeclarations(tds);
        if (!cId.equals(SFO.EMPTY)) {
            typedef.put(cId, result);
        }
        main.cHandler.addSizeOfConstants(result.cvar);
        return result;
    }

    @Override
    public Expression convertArith2Boolean(ILocation loc, ASTType type,
            Expression e) {
        if (e == null) {
            String msg = "Incorrect syntax! An expression is expected here!";
            Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
        }
        if (type != null && type instanceof PrimitiveType) {
            if (((PrimitiveType) type).getName().equals(SFO.BOOL)) {
                if (e instanceof IntegerLiteral) {
                    if (Integer.parseInt(((IntegerLiteral) e).getValue()) == 0)
                        e = new BooleanLiteral(loc, new InferredType(
                                Type.Boolean), false);
                    else
                        e = new BooleanLiteral(loc, new InferredType(
                                Type.Boolean), true);
                } else {
                    IType t = e.getType();
                    if (t != null) {
                        assert t instanceof InferredType;
                        InferredType it = (InferredType) t;
                        switch (it.getType()) {
                            case Boolean:
                                // everything is ok ...
                                break;
                            case Integer:
                            	/*
                                 * try to unwrap formerly introduced
                                 * if-then-else wrapper
                                 */
                                final Expression unwrappedInt =
                                		unwrapInt2Boolean(e);
                                if (unwrappedInt != null) {
                                	e = unwrappedInt;
                                }
                                else {
	                            	e = new BinaryExpression(loc, new InferredType(
	                                        InferredType.Type.Boolean),
	                                        BinaryExpression.Operator.COMPNEQ, e,
	                                        new IntegerLiteral(loc, SFO.NR0));
                                }
                        	    break;
                            case Real:
                                e = new BinaryExpression(loc, new InferredType(
                                        InferredType.Type.Boolean),
                                        BinaryExpression.Operator.COMPNEQ, e,
                                        new RealLiteral(loc, SFO.NR0F));
                                break;
                            case Unknown:
                            default:
                                String msg = "Don't know the type of this expression. Line: "
                                        + e.getLocation().getStartLine();
                                Dispatcher.error(loc, SyntaxErrorType.TypeError,
                                        msg);
                        }
                    } else {
                        String msg = "Don't know the type of this expression. Line: "
                                + e.getLocation().getStartLine();
                        Dispatcher.error(loc, SyntaxErrorType.TypeError, msg);
                    }
                }
            }
        } else if (type != null && type instanceof ArrayType) {
            return convertArith2Boolean(loc,
                    ((ArrayType) type).getValueType(), e);
        }
        return e;
    }

    @Override
    public Expression unwrapInt2Boolean(final Expression expr) {
    	if (expr instanceof IfThenElseExpression) {
			final IfThenElseExpression iteEx = (IfThenElseExpression)expr;
			final Expression thenPart = iteEx.getThenPart();
			if ((thenPart instanceof IntegerLiteral) &&
				(((IntegerLiteral)thenPart).getValue() == SFO.NR1)) {
				final Expression elsePart = iteEx.getElsePart();
				if ((elsePart instanceof IntegerLiteral) &&
						(((IntegerLiteral)elsePart).getValue() == SFO.NR0)) {
					return iteEx.getCondition();
				}
			}
    	}
    	return null;
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
        if (!typedef.containsKey(type.getName())) {
            String msg = "Unknown C typedef: " + type.getName();
            // TODO : no idea what location should be set to ...
            Dispatcher.error(null, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
        }
        return new InferredType(typedef.get(type.getName()).getType());
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
        return undefStructs;
    }
}
