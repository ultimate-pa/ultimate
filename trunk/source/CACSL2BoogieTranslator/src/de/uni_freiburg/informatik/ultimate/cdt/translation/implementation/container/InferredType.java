/**
 * Container object to store inferred types.
 * TODO : add a reference to the corresponding CType. That would make type 
 * checking during translation easier!
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;

/**
 * @author Markus Lindenmann
 * @date 16.06.2012
 */
public class InferredType implements IType {
    /**
     * The serial version UID.
     */
    private static final long serialVersionUID = 4825293857474339818L;
    /**
     * The held type.
     */
    private Type type;

    /**
     * @author Markus Lindenmann
     * @date 16.06.2012
     */
    public enum Type {
        /**
         * Integer.
         */
        Integer,
        /**
         * Boolean.
         */
        Boolean,
        /**
         * Reals.
         */
        Real,
        /**
         * Strings.
         */
        String,
        /**
         * Cannot be inferred or not yet inferred.
         */
        Unknown,
        /**
         * Void type!
         */
        Void,
        /**
         * Struct type.
         */
        Struct,
        /**
         * Pointer type.
         */
        Pointer
    }

    /**
     * Constructor.
     * 
     * @param type
     *            the type.
     */
    public InferredType(Type type) {
        this.type = type;
    }

    /**
     * Constructor.
     * 
     * @param at
     *            the primitive type to convert.
     */
    public InferredType(ASTType at) {
        if (at == MemoryHandler.POINTER_TYPE) {
            this.type = Type.Pointer;
        } else if (at instanceof ArrayType) {
            InferredType it = new InferredType(((ArrayType) at).getValueType());
            this.type = it.getType();
        } else if (at instanceof StructType) {
            this.type = Type.Struct;
        } else { // Primitive Type
            if (at == null) {
                this.type = Type.Unknown;
            } else {
                String s = at.toString();
                s = s.replaceFirst(at.getClass().getSimpleName(), SFO.EMPTY);
                s = s.replace("[", SFO.EMPTY);
                s = s.replace("]", SFO.EMPTY);
                if (s.equals(SFO.BOOL)) {
                    this.type = Type.Boolean;
                } else if (s.equals(SFO.INT)) {
                    this.type = Type.Integer;
                } else if (s.equals(SFO.REAL)) {
                    this.type = Type.Real;
                } else {
                    this.type = Type.Unknown;
                }
            }
        }
    }
    
    public InferredType(CType cType) {
    	CType underlyingType = cType;
    	if (underlyingType instanceof CNamed)
    		underlyingType = ((CNamed) cType).getUnderlyingType();
		
		if (underlyingType instanceof CPrimitive) {
			CPrimitive cp = (CPrimitive) cType;
			switch (cp.getType()) {
			case INT:
				type = Type.Integer;
				break;
			case FLOAT:
			case DOUBLE:
				type = Type.Real;
				break;
			case CHAR:
				type = Type.String;
				break;
			default:
				throw new UnsupportedSyntaxException("..");
			}
		} else if (underlyingType instanceof CPointer) {
			type = Type.Pointer;
		} else if (underlyingType instanceof CArray) {
			type = Type.Pointer;
		} else if (underlyingType instanceof CEnum) {
			type = Type.Integer;
		} else if (underlyingType instanceof CStruct) {
			type = Type.Struct;
		} else if (underlyingType instanceof CNamed) {
			assert false : "This should not be the case as we took the underlying type.";
		} else {
			throw new UnsupportedSyntaxException("..");
		}	
    }

    /**
     * Returns the type.
     * 
     * @return the type.
     */
    public Type getType() {
        return type;
    }

    @Override
    public String toString() {
        switch (getType()) {
            case Boolean:
                return SFO.BOOL;
            case Integer:
                return SFO.INT;
            case Real:
                return SFO.REAL;
            case String:
                return SFO.STRING;
            case Pointer:
                return SFO.POINTER;
            case Struct:
            	return Type.Struct.toString();
            case Unknown:
            default:
                break;
        }
        return SFO.UNKNOWN;
    }

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((type == null) ? 0 : type.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		InferredType other = (InferredType) obj;
		if (type != other.type)
			return false;
		return true;
	}
    
    
}
