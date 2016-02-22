/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Describes a primitive variable given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclSpecifier;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

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
    	CHAR(GENERALPRIMITIVE.INTTYPE),
    	/* signed char */
    	SCHAR(GENERALPRIMITIVE.INTTYPE),
    	/* unsigned char */
    	UCHAR(GENERALPRIMITIVE.INTTYPE),
    	/* ?? */
//        WCHAR,
    	/* ?? */
//        CHAR32,
    	/* ?? */
//        CHAR16,
    	/* short, short int, signed short, signed short int */
        SHORT(GENERALPRIMITIVE.INTTYPE),
        /* unsigned short, unsigned short int */
        USHORT(GENERALPRIMITIVE.INTTYPE),
    	/* int, signed int */
        INT(GENERALPRIMITIVE.INTTYPE),
    	/* unsigned, unsigned int */
        UINT(GENERALPRIMITIVE.INTTYPE),
        /* long, long int, signed long, signed long int */
        LONG(GENERALPRIMITIVE.INTTYPE),
        /* unsigned long, unsigned long int */
        ULONG(GENERALPRIMITIVE.INTTYPE),
        /* long long, long long int, signed long long, signed long long int */
        LONGLONG(GENERALPRIMITIVE.INTTYPE),
        /* unsigned long long, unsigned long long int */
        ULONGLONG(GENERALPRIMITIVE.INTTYPE),
        /* _Bool */
        BOOL(GENERALPRIMITIVE.INTTYPE),
    	/* Floating Types*/
        /* float */
        FLOAT(GENERALPRIMITIVE.FLOATTYPE),
        /* _Complex float */
        COMPLEX_FLOAT(GENERALPRIMITIVE.FLOATTYPE),
        /* double */
        DOUBLE(GENERALPRIMITIVE.FLOATTYPE),
        /* _Complex double */
        COMPLEX_DOUBLE(GENERALPRIMITIVE.FLOATTYPE),
        /* long double */
        LONGDOUBLE(GENERALPRIMITIVE.FLOATTYPE),
         /* _Complex long double */
        COMPLEX_LONGDOUBLE(GENERALPRIMITIVE.FLOATTYPE),
        //TODO: something with "_imaginary"??
        /*other type(s)*/
        /**
         * C type : void.
         */
        VOID(GENERALPRIMITIVE.VOID);
        
        PRIMITIVE(GENERALPRIMITIVE generalprimitive) {
    		m_Generalprimitive = generalprimitive;
    	}
        
    	private final GENERALPRIMITIVE m_Generalprimitive;
    	
    	public boolean isIntegertype() {
    		return m_Generalprimitive == GENERALPRIMITIVE.INTTYPE;
    	}
    	
    	public boolean isFloatingtype() {
    		return m_Generalprimitive == GENERALPRIMITIVE.FLOATTYPE;
    	}
    }
    
    public enum GENERALPRIMITIVE {
    	INTTYPE,
    	FLOATTYPE,
    	VOID
    }
    
    private final boolean isUnsigned;

    /**
     * The C type of the variable.
     */
    private final PRIMITIVE type;
    
    /**
     * more general type, i.e. inttype, floattype, void -- is derived from
     * type
     */
    private final GENERALPRIMITIVE generalType;
    
    public CPrimitive(PRIMITIVE type) {
        super(false, false, false, false); //FIXME: integrate those flags
    	this.type = type;
    	generalType = getGeneralType(type);
    	isUnsigned = isUnsigned(type);
    }

	private GENERALPRIMITIVE getGeneralType(PRIMITIVE type) throws AssertionError {
		final GENERALPRIMITIVE generalType;
		switch (type) {
		case COMPLEX_FLOAT:
		case COMPLEX_DOUBLE:
		case COMPLEX_LONGDOUBLE:
		case FLOAT:
		case DOUBLE:
		case LONGDOUBLE:
			generalType = GENERALPRIMITIVE.FLOATTYPE;
//			throw new UnsupportedSyntaxException(LocationFactory.createIgnoreCLocation(), "we do not support floats");
			break;
		case BOOL:
		case UCHAR:
		case UINT:
		case ULONG:
		case ULONGLONG:
		case USHORT:
		case CHAR:
//		case CHAR16:
//		case CHAR32:
		case INT:
		case LONG:
		case LONGLONG:
		case SCHAR:
		case SHORT:
//		case WCHAR:
			generalType = GENERALPRIMITIVE.INTTYPE;
			break;
		case VOID:
			generalType = GENERALPRIMITIVE.VOID;
			break;
		default:
			throw new AssertionError("case missing");
    	}
		return generalType;
	}
	
	private boolean isUnsigned(PRIMITIVE type) throws AssertionError {
		switch (type) {
		case BOOL:
		case UCHAR:
		case UINT:
		case ULONG:
		case ULONGLONG:
		case USHORT:
			return true;
		case CHAR :
			return !TypeSizes.isCharSigned();
		case COMPLEX_FLOAT:
		case COMPLEX_DOUBLE:
		case COMPLEX_LONGDOUBLE:
		case FLOAT:
		case DOUBLE:
		case LONGDOUBLE:
//		case CHAR16:
//		case CHAR32:
		case INT:
		case LONG:
		case LONGLONG:
		case SCHAR:
		case SHORT:
//		case WCHAR:
		case VOID:
			return false;
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
//                case IASTSimpleDeclSpecifier.t_char16_t:
//                    this.type = PRIMITIVE.CHAR16;
//                    break;
//                case IASTSimpleDeclSpecifier.t_char32_t:
//                    this.type = PRIMITIVE.CHAR32;
//                    break;
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
                		else if (sds.isShort())
                			this.type = PRIMITIVE.USHORT;
                		else
                			this.type = PRIMITIVE.UINT;
                	else                 		
                		if (sds.isLong())
                			this.type = PRIMITIVE.LONG;
                		else if (sds.isLongLong())
                			this.type = PRIMITIVE.LONGLONG;
                		else if (sds.isShort())
                			this.type = PRIMITIVE.SHORT;
                		else
                			this.type = PRIMITIVE.INT;
                    break;
                case IASTSimpleDeclSpecifier.t_unspecified:
                	if (sds.isUnsigned())
                		if (sds.isLong())
                			this.type = PRIMITIVE.ULONG;
                		else if (sds.isLongLong())
                			this.type = PRIMITIVE.ULONGLONG;
                		else if (sds.isShort())
                			this.type = PRIMITIVE.USHORT;
                		else
                			this.type = PRIMITIVE.UINT;
                	else                 		
                		if (sds.isLong())
                			this.type = PRIMITIVE.LONG;
                		else if (sds.isLongLong())
                			this.type = PRIMITIVE.LONGLONG;
                		else if (sds.isShort())
                			this.type = PRIMITIVE.SHORT;
                		else
                			this.type = PRIMITIVE.INT;
                    break;
                case IASTSimpleDeclSpecifier.t_void:
                    this.type = PRIMITIVE.VOID;
                    break;
//                case IASTSimpleDeclSpecifier.t_wchar_t:
//                    this.type = PRIMITIVE.WCHAR;
//                    break;
                default:
                    throw new IllegalArgumentException(
                            "Unknown C Declaration!");
            }
        } else {
            throw new IllegalArgumentException("Unknown C Declaration!");
        }
    	generalType = getGeneralType(type);
    	isUnsigned = isUnsigned(type);
    }
    
    public boolean isUnsigned() {
    	return isUnsigned;
    }

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
    
    @Override
    public int hashCode() {
    	return HashUtils.hashJenkins(31, type);
    }

	@Override
	public boolean isCompatibleWith(CType o) {
//		if (this.type == PRIMITIVE.VOID)
//			return true;
        CType oType = ((CType) o).getUnderlyingType();
        
        if (oType instanceof CEnum 
        		&& this.generalType == GENERALPRIMITIVE.INTTYPE)
        	return true;
        
        if (oType instanceof CPrimitive) {
            return type == ((CPrimitive)oType).type;
        } else {
            return false;
        }
	}
	
	public CPrimitive getCorrespondingUnsignedType() {
		if (!this.isIntegerType()) {
			throw new IllegalArgumentException("no integer type " + this);
		}
		if (this.isUnsigned()) {
			throw new IllegalArgumentException("already unsigned " + this);
		}
		switch (this.getType()) {
		case CHAR:
			if (TypeSizes.isCharSigned()) {
				return new CPrimitive(PRIMITIVE.UCHAR);
			} else {
				throw new UnsupportedOperationException(
						"according to your settings, char is already unsigned");
			}
		case INT:
			return new CPrimitive(PRIMITIVE.UINT);
		case LONG:
			return new CPrimitive(PRIMITIVE.ULONG);
		case LONGLONG:
			return new CPrimitive(PRIMITIVE.ULONGLONG);
		case SCHAR:
			return new CPrimitive(PRIMITIVE.UCHAR);
		case SHORT:
			return new CPrimitive(PRIMITIVE.USHORT);
		default:
			throw new IllegalArgumentException("unsupported type " + this);
		}
		
	}
}
