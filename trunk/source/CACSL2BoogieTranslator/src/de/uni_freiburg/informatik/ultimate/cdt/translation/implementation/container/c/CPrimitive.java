/**
 * Describes a primitive variable given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;

/**
 * @author Markus Lindenmann
 * @date 13.07.2012
 */
public class CPrimitive extends CType {
    /**
     * @author Markus Lindenmann
     * @date 18.09.2012 Describing primitive C types.
     */
    public static enum PRIMITIVE {
        /**
         * C type : int.
         */
        INT,
        /**
         * C type : char.
         */
        CHAR,
        /**
         * C type : float.
         */
        FLOAT,
        /**
         * C type : double.
         */
        DOUBLE,
//        /**
//         * C type : *.
//         */
//        POINTER,
        /**
         * C type : void.
         */
        VOID,
        /**
         * C type : _Bool.
         */
        BOOL,
        /**
         * C type : ?.
         */
        WCHAR,
        /**
         * C type : ?.
         */
        CHAR32,
        /**
         * C type : ?.
         */
        CHAR16,
    }

    /**
     * The C type of the variable.
     */
    private final PRIMITIVE type;
    
    public CPrimitive(PRIMITIVE type) {
    	super(null);
    	this.type = type;
    }

    /**
     * Constructor.
     * 
     * @param cDeclSpec
     *            the C declaration specifier.
     */
    public CPrimitive(IASTDeclSpecifier cDeclSpec) {
        super(cDeclSpec);
        if (cDeclSpec instanceof IASTSimpleDeclSpecifier) {
            IASTSimpleDeclSpecifier sds = (IASTSimpleDeclSpecifier) cDeclSpec;
            switch (sds.getType()) {
                case IASTSimpleDeclSpecifier.t_bool:
                    this.type = PRIMITIVE.BOOL;
                    break;
                case IASTSimpleDeclSpecifier.t_char:
                    this.type = PRIMITIVE.CHAR;
                    break;
                case IASTSimpleDeclSpecifier.t_char16_t:
                    this.type = PRIMITIVE.CHAR16;
                    break;
                case IASTSimpleDeclSpecifier.t_char32_t:
                    this.type = PRIMITIVE.CHAR32;
                    break;
                case IASTSimpleDeclSpecifier.t_double:
                    this.type = PRIMITIVE.DOUBLE;
                    break;
                case IASTSimpleDeclSpecifier.t_float:
                    this.type = PRIMITIVE.FLOAT;
                    break;
                case IASTSimpleDeclSpecifier.t_int:
                    this.type = PRIMITIVE.INT;
                    break;
                case IASTSimpleDeclSpecifier.t_unspecified:
                    this.type = PRIMITIVE.INT;
                    break;
                case IASTSimpleDeclSpecifier.t_void:
                    this.type = PRIMITIVE.VOID;
                    break;
                case IASTSimpleDeclSpecifier.t_wchar_t:
                    this.type = PRIMITIVE.WCHAR;
                    break;
                default:
                    throw new IllegalArgumentException(
                            "Unknown C Decklaration!");
            }
        } else {
            throw new IllegalArgumentException("Unknown C Declaration!");
        }
    }

    /**
     * Getter for the flag long long.
     * 
     * @return whether the variable is specified to be long long.
     */
    public boolean isLongLong() {
        assert super.cDeclSpec instanceof IASTSimpleDeclSpecifier;
        if (super.cDeclSpec instanceof IASTSimpleDeclSpecifier) {
            return ((IASTSimpleDeclSpecifier) super.cDeclSpec).isLongLong();
        }
        return false;
    }

    /**
     * Getter for the flag long.
     * 
     * @return whether the variable is specified to be long.
     */
    public boolean isLong() {
        assert super.cDeclSpec instanceof IASTSimpleDeclSpecifier;
        if (super.cDeclSpec instanceof IASTSimpleDeclSpecifier) {
            return ((IASTSimpleDeclSpecifier) super.cDeclSpec).isLong();
        }
        return false;
    }

    /**
     * Getter for the flag short.
     * 
     * @return whether the varibale is specified to be short.
     */
    public boolean isShort() {
        assert super.cDeclSpec instanceof IASTSimpleDeclSpecifier;
        if (super.cDeclSpec instanceof IASTSimpleDeclSpecifier) {
            return ((IASTSimpleDeclSpecifier) super.cDeclSpec).isShort();
        }
        return false;
    }

    /**
     * Getter for the flag short.
     * 
     * @return whether the varibale is specified to be short.
     */
    public boolean isComplex() {
        assert super.cDeclSpec instanceof IASTSimpleDeclSpecifier;
        if (super.cDeclSpec instanceof IASTSimpleDeclSpecifier) {
            return ((IASTSimpleDeclSpecifier) super.cDeclSpec).isComplex();
        }
        return false;
    }

    /**
     * Getter for the flag short.
     * 
     * @return whether the varibale is specified to be short.
     */
    public boolean isImaginary() {
        assert super.cDeclSpec instanceof IASTSimpleDeclSpecifier;
        if (super.cDeclSpec instanceof IASTSimpleDeclSpecifier) {
            return ((IASTSimpleDeclSpecifier) super.cDeclSpec).isImaginary();
        }
        return false;
    }

    /**
     * Getter for the flag short.
     * 
     * @return whether the varibale is specified to be short.
     */
    public boolean isSigned() {
        assert super.cDeclSpec instanceof IASTSimpleDeclSpecifier;
        if (super.cDeclSpec instanceof IASTSimpleDeclSpecifier) {
            return ((IASTSimpleDeclSpecifier) super.cDeclSpec).isSigned();
        }
        return false;
    }

    /**
     * Getter for the flag short.
     * 
     * @return whether the varibale is specified to be short.
     */
    public boolean isUnsinged() {
        assert super.cDeclSpec instanceof IASTSimpleDeclSpecifier;
        if (super.cDeclSpec instanceof IASTSimpleDeclSpecifier) {
            return ((IASTSimpleDeclSpecifier) super.cDeclSpec).isUnsigned();
        }
        return false;
    }

    /**
     * Getter for the primitive type.
     * 
     * @return the type
     */
    public PRIMITIVE getType() {
        return type;
    }

    @Override
    public String toString() {
        return type.toString();
    }
}
