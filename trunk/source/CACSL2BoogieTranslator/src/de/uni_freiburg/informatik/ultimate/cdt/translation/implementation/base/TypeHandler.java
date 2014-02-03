/**
 * An example of a Type-Handler implementation.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTCompositeTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTElaboratedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTEnumerationSpecifier.IASTEnumerator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTNamedTypeSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IArrayType;
import org.eclipse.cdt.core.dom.ast.IBasicType;
import org.eclipse.cdt.core.dom.ast.ITypedef;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTTypedefNameSpecifier;
import org.eclipse.cdt.internal.core.dom.parser.c.CPointerType;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.SymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

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
    private final ScopedHashMap<String, ResultTypes> m_DefinedTypes;
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
        this.m_DefinedTypes = new ScopedHashMap<String, ResultTypes>();
        this.m_IncompleteType = new HashSet<String>();
    }

    @Override
    public boolean isStructDeclaration() {
        assert structCounter >= 0;
        return structCounter != 0;
    }
    
    /**
     * for svcomp2014 hack
     */
    public int getStructCounter() {
    	return structCounter;
    }

    @Override
    public Result visit(Dispatcher main, IASTNode node) {
        String msg = "TypeHandler: Not yet implemented: " + node.toString();
        ILocation loc = new CACSLLocation(node);
        throw new UnsupportedSyntaxException(loc, msg);
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
            case IASTSimpleDeclSpecifier.t_unspecified:
            {
            	String msg = "unspecified type, defaulting to int";
            	Dispatcher.warn(loc, msg);
            }
            case IASTSimpleDeclSpecifier.t_bool:
            case IASTSimpleDeclSpecifier.t_char:
            case IASTSimpleDeclSpecifier.t_int:
                // so int is also a primitive type
                // NOTE: in a extended implementation we should
                // handle here different types of int (short, long,...)
                result = (new ResultTypes(new PrimitiveType(loc, SFO.INT), node.isConst(), false, cvar));
                break;
            case IASTSimpleDeclSpecifier.t_double:
            case IASTSimpleDeclSpecifier.t_float:
                // floating point number are not supported by Ultimate,
                // somehow we treat it here as REALs
                result = (new ResultTypes(new PrimitiveType(loc, SFO.REAL), node.isConst(), false, cvar));
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
                throw new UnsupportedSyntaxException(loc, msg);
        }
        return result;
    }

    @Override
    public Result visit(Dispatcher main, IASTNamedTypeSpecifier node) {
        CACSLLocation loc = new CACSLLocation(node);
        if (node instanceof CASTTypedefNameSpecifier) {
            node = (CASTTypedefNameSpecifier) node;
            String cId = node.getName().toString();
            String bId = main.cHandler.getSymbolTable().get(cId, loc).getBoogieName();
            return new ResultTypes(new NamedType(loc, bId, null), false, false, //TODO: replace constants
            		new CNamed(bId, m_DefinedTypes.get(bId).cType));

        }
        String msg = "Unknown or unsupported type! " + node.toString();
        throw new UnsupportedSyntaxException(loc, msg);
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
        CEnum cEnum = new CEnum(enumId, fNames, fValues);
        IType it = new InferredType(Type.Integer);
        ASTType at = new PrimitiveType(loc, it, SFO.INT);
        ResultTypes result = new ResultTypes(at, false, false, cEnum);
        if (!enumId.equals(SFO.EMPTY)) {
            m_DefinedTypes.put(enumId, result);
        }
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
                ResultTypes originalType = m_DefinedTypes.get(type);
                ResultTypes withoutBoogieTypedef = new ResultTypes(
                		originalType.getType(), originalType.isConst, 
                		originalType.isVoid, originalType.cType);
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
            
            return r;
        }
        String msg = "Not yet implemented: Spec [" + node.getKind() + "] of "
                + node.getClass();
        throw new UnsupportedSyntaxException(loc, msg);
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
            if (r instanceof ResultDeclaration) {
            	ResultDeclaration rdec = (ResultDeclaration) r;
            	for (CDeclaration declaration : rdec.getDeclarations()) {
            		fNames.add(declaration.getName());
            		fTypes.add(declaration.getType());
            		fields.add(new VarList(loc, new String[] {declaration.getName()},
            				this.ctype2asttype(loc, declaration.getType())));
            	}
            } else if (r instanceof ResultSkip) { // skip ;)
            } else {
                String msg = "Unexpected syntax in struct declaration!";
                throw new UnsupportedSyntaxException(loc, msg);
            }
        }
        structCounter--;
        String cId = node.getName().toString();
        String name = "STRUCT~" + cId;
        NamedType namedType = new NamedType(loc, name,
                new ASTType[0]);
       
        ASTType type = namedType;
        CStruct cvar;
        if (node.getKey() == IASTCompositeTypeSpecifier.k_struct) {
        	cvar = new CStruct(fNames.toArray(new String[0]),
                    fTypes.toArray(new CType[0]));
        } else if (node.getKey() == IASTCompositeTypeSpecifier.k_union) {
        	cvar = new CUnion(fNames.toArray(new String[0]),
                    fTypes.toArray(new CType[0]));
        } else {
        	throw new UnsupportedOperationException();
        }
        ResultTypes result = new ResultTypes(type, false, false, cvar);
       
        if (m_IncompleteType.contains(name)) {
            m_IncompleteType.remove(name);
            ResultTypes incompleteType = m_DefinedTypes.get(cId);
            CStruct incompleteStruct = (CStruct) incompleteType.cType;
            incompleteStruct.complete(cvar);
        }
        
        if (!cId.equals(SFO.EMPTY)) {
            m_DefinedTypes.put(cId, result);
        }
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
            Dispatcher.unsupportedSyntax(null, msg);
    		return new InferredType(Type.Unknown);
    	}
    }

    @Override
    public InferredType visit(Dispatcher main, ITypedef type) {
        if (!m_DefinedTypes.containsKey(type.getName())) {
            String msg = "Unknown C typedef: " + type.getName();
            // TODO : no idea what location should be set to ...
            throw new IncorrectSyntaxException(null, msg);
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
        ASTType t = this.ctype2asttype(loc, sT.get(cId, loc).getCVariable());
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
            throw new IncorrectSyntaxException(loc, msg);
        }
        String msg = "Something went wrong while determining types!";
        throw new UnsupportedSyntaxException(loc, msg);
    }

    @Override
    public InferredType visit(Dispatcher main, IArrayType type) {
        return main.dispatch(type.getType());
    }
    
    @Override
    public  ScopedHashMap<String,ResultTypes> getDefinedTypes() {
        return m_DefinedTypes;
    }
    
    @Override
    public Set<String> getUndefinedTypes() {
        return m_IncompleteType;
    }

    @Override
	public ASTType ctype2asttype(ILocation loc, CType cType, boolean isBool, boolean isPointer) {
		if (cType instanceof CPrimitive) {
			switch (((CPrimitive) cType).getType()) {
			case VOID:
				return null; //(alex:) seems to be lindemm's convention, see FunctionHandler.isInParamVoid(..)
			case BOOL:
			case CHAR:
			case CHAR16:
			case CHAR32:
			case WCHAR:
			case INT:
				return new PrimitiveType(loc, SFO.INT);
			case FLOAT:
			case DOUBLE:
				return new PrimitiveType(loc, SFO.REAL);
			default:
				throw new UnsupportedSyntaxException(loc, "unknown primitive type");
			}
		} else if (cType instanceof CPointer) {
			return MemoryHandler.POINTER_TYPE;
		} else if (cType instanceof CArray) {
			CArray cart = (CArray) cType;
			ASTType[] indexTypes = new ASTType[cart.getDimensions().length];
			String[] typeParams = new String[0]; //new String[cart.getDimensions().length];
			for (int i = 0; i < cart.getDimensions().length; i++) {
				indexTypes[i] = new PrimitiveType(loc, SFO.INT);//C only allows integer indices
				
			}
			return new ArrayType(loc, typeParams, indexTypes, this.ctype2asttype(loc, cart.getValueType()));
		} else if (cType instanceof CStruct) {
			CStruct cstruct = (CStruct) cType;
			VarList[] fields = new VarList[cstruct.getFieldCount()];
			for (int i = 0; i < cstruct.getFieldCount(); i++) {
				fields[i] = new VarList(loc, 
						new String[] {cstruct.getFieldIds()[i]}, 
						this.ctype2asttype(loc, cstruct.getFieldTypes()[i])); 
			}
			return new StructType(loc, fields);
		} else if (cType instanceof CNamed) {
//			throw new AssertionError();
			//should work as we save the unique typename we computed in CNamed, not the name from the source c file
			return new NamedType(loc, ((CNamed) cType).getName(), new ASTType[0]);
		} else if (cType instanceof CFunction) {
				throw new UnsupportedSyntaxException(loc, "how to translate function type?");
		}
		throw new UnsupportedSyntaxException(loc, "unknown type");
	}
    
    public void beginScope() {
    	m_DefinedTypes.beginScope();
    }
    
    public void endScope() {
    	m_DefinedTypes.endScope();
    }
    
    @Override
    public void addDefinedType(String id, ResultTypes type) {
    	m_DefinedTypes.put(id, type);
    }

	@Override
	public ASTType ctype2asttype(ILocation loc, CType cType) {
		return this.ctype2asttype(loc, cType, false, false);
	}
}
