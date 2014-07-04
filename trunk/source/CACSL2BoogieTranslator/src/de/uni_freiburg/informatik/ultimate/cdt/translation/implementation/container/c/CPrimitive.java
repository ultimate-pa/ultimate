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
     * (updated 10.12.2013 by nutz)
     */
    public static enum PRIMITIVE {
    	/* Integer Types*/
    	/* char */
    	CHAR,
    	/* signed char */
    	SCHAR,
    	/* unsigned char */
    	UCHAR,
    	/* ?? */
        WCHAR,
    	/* ?? */
        CHAR32,
    	/* ?? */
        CHAR16,
    	/* short, short int, signed short, signed short int */
        SHORT,
        /* unsigned short, unsigned short int */
        USHORT,
    	/* int, signed int */
        INT,
    	/* unsigned, unsigned int */
        UINT,
        /* long, long int, signed long, signed long int */
        LONG,
        /* unsigned long, unsigned long int */
        ULONG,
        /* long long, long long int, signed long long, signed long long int */
        LONGLONG,
        /* unsigned long long, unsigned long long int */
        ULONGLONG,
        /* _Bool */
        BOOL,
    	/* Floating Types*/
        /* float */
        FLOAT,
        /* _Complex float */
        COMPLEX_FLOAT,
        /* double */
        DOUBLE,
        /* _Complex double */
        COMPLEX_DOUBLE,
        /* long double */
        LONGDOUBLE,
         /* _Complex long double */
        COMPLEX_LONGDOUBLE,
        //TODO: something with "_imaginary"??
        /*other type(s)*/
        /**
         * C type : void.
         */
        VOID,
    }
    
    public enum GENERALPRIMITIVE {
    	INTTYPE,
    	FLOATTYPE,
    	VOID
    }

    /**
     * The C type of the variable.
     */
    private final PRIMITIVE type;
    
    /**
     * more general type, i.e. inttype, floattype, void -- is derived from
     * type
     */
    private GENERALPRIMITIVE generalType;
    
    public CPrimitive(PRIMITIVE type) {
        super(false, false, false, false); //FIXME: integrate those flags
    	this.type = type;
    	setGeneralType(type);
    }

	private void setGeneralType(PRIMITIVE type) throws AssertionError {
		switch (type) {
		case COMPLEX_DOUBLE:
		case COMPLEX_FLOAT:
		case COMPLEX_LONGDOUBLE:
		case DOUBLE:
		case FLOAT:
			generalType = GENERALPRIMITIVE.FLOATTYPE;
			break;
		case BOOL:
		case CHAR:
		case CHAR16:
		case CHAR32:
		case INT:
		case LONG:
		case LONGDOUBLE:
		case LONGLONG:
		case SCHAR:
		case SHORT:
		case UCHAR:
		case UINT:
		case ULONG:
		case ULONGLONG:
		case USHORT:
		case WCHAR:
			generalType = GENERALPRIMITIVE.INTTYPE;
			break;
		case VOID:
			generalType = GENERALPRIMITIVE.VOID;
			break;
		default:
			throw new AssertionError("case missing");
    	}
	}

    /**
     * Constructor.
     * 
     * @param cDeclSpec
     *            the C declaration specifier.
     */
    public CPrimitive(IASTDeclSpecifier cDeclSpec) {
        super(false, false, false, false); //FIXME: integrate those flags
        if (cDeclSpec instanceof IASTSimpleDeclSpecifier) {
            IASTSimpleDeclSpecifier sds = (IASTSimpleDeclSpecifier) cDeclSpec;
            switch (sds.getType()) {
                case IASTSimpleDeclSpecifier.t_bool:
                    this.type = PRIMITIVE.BOOL;
                    break;
                case IASTSimpleDeclSpecifier.t_char:
                	if (sds.isSigned())
                		this.type = PRIMITIVE.SCHAR;
                	else if (sds.isUnsigned())
                		this.type = PRIMITIVE.UCHAR;
                	else
                		this.type = PRIMITIVE.CHAR;
                    break;
                case IASTSimpleDeclSpecifier.t_char16_t:
                    this.type = PRIMITIVE.CHAR16;
                    break;
                case IASTSimpleDeclSpecifier.t_char32_t:
                    this.type = PRIMITIVE.CHAR32;
                    break;
                case IASTSimpleDeclSpecifier.t_double:
                	if (sds.isComplex())
                		this.type = PRIMITIVE.COMPLEX_DOUBLE;
                	else
                		this.type = PRIMITIVE.DOUBLE;
                    break;
                case IASTSimpleDeclSpecifier.t_float:
                 	if (sds.isComplex())
                		this.type = PRIMITIVE.COMPLEX_FLOAT;
                	else
                		this.type = PRIMITIVE.FLOAT;
                    break;
                case IASTSimpleDeclSpecifier.t_int:
                	if (sds.isUnsigned())
                		if (sds.isLong())
                			this.type = PRIMITIVE.ULONG;
                		else if (sds.isLongLong())
                			this.type = PRIMITIVE.ULONGLONG;
                		else
                			this.type = PRIMITIVE.UINT;
                	else                 		
                		if (sds.isLong())
                			this.type = PRIMITIVE.LONG;
                		else if (sds.isLongLong())
                			this.type = PRIMITIVE.LONGLONG;
                		else
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
    	setGeneralType(type);
    }

    /**
     * Getter for the primitive type.
     * 
     * @return the type
     */
    public PRIMITIVE getType() {
        return type;
    }
    
    public GENERALPRIMITIVE getGeneralType() {
    	return generalType;
    }

    @Override
    public String toString() {
        return type.toString();
    }
    
    @Override
    public boolean equals(Object o) {
        if (!(o instanceof CType)) {
            return false;
        }
        CType oType = ((CType)o).getUnderlyingType();
        if (oType instanceof CPrimitive) {
            return type == ((CPrimitive)oType).type;
        }
        else {
            return false;
        }
    }
}
