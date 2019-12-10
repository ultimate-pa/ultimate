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

/**
 * @author Markus Lindenmann
 * @date 13.07.2012
 */
public class CPrimitive extends CType {
	/**
	 * @author Markus Lindenmann
	 * @date 18.09.2012 Describing primitive C types. (updated 10.12.2013 by nutz)
	 */
	public static enum CPrimitives {

		/* char */
		CHAR(CPrimitiveCategory.INTTYPE),
		/* signed char */
		SCHAR(CPrimitiveCategory.INTTYPE),
		/* unsigned char */
		UCHAR(CPrimitiveCategory.INTTYPE),
		/* ?? */
		// WCHAR,
		/* ?? */
		// CHAR32,
		/* ?? */
		// CHAR16,
		/* short, short int, signed short, signed short int */
		SHORT(CPrimitiveCategory.INTTYPE),
		/* unsigned short, unsigned short int */
		USHORT(CPrimitiveCategory.INTTYPE),
		/* int, signed int */
		INT(CPrimitiveCategory.INTTYPE),
		/* unsigned, unsigned int */
		UINT(CPrimitiveCategory.INTTYPE),
		/* long, long int, signed long, signed long int */
		LONG(CPrimitiveCategory.INTTYPE),
		/* unsigned long, unsigned long int */
		ULONG(CPrimitiveCategory.INTTYPE),
		/* long long, long long int, signed long long, signed long long int */
		LONGLONG(CPrimitiveCategory.INTTYPE),
		/* unsigned long long, unsigned long long int */
		ULONGLONG(CPrimitiveCategory.INTTYPE),
		/* _Bool */
		BOOL(CPrimitiveCategory.INTTYPE),

		/**
		 * float
		 *
		 * represented as SMT bitvector, e.g.,
		 *
		 * <code>
		 * type { :bitsize 32 } C_FLOAT = bv32;
		 * </code>
		 */
		FLOAT(CPrimitiveCategory.FLOATTYPE),

		/**
		 * _Complex float
		 */
		COMPLEX_FLOAT(CPrimitiveCategory.FLOATTYPE),

		/**
		 * double
		 */
		DOUBLE(CPrimitiveCategory.FLOATTYPE),

		/**
		 * _Complex double
		 */
		COMPLEX_DOUBLE(CPrimitiveCategory.FLOATTYPE),

		/**
		 * long double
		 */
		LONGDOUBLE(CPrimitiveCategory.FLOATTYPE),

		/**
		 * _Complex long double
		 */
		COMPLEX_LONGDOUBLE(CPrimitiveCategory.FLOATTYPE),

		/**
		 * <code>float</code> represented as SMT floating point, e.g.,
		 *
		 * <code>
		 * type { :builtin "FloatingPoint" } { :indices 8,24 } C_FLOAT;
		 * </code>
		 *
		 * We use this to type the various <code> :builtin </code> functions and procedures.
		 *
		 */
		FLOAT_SMT(CPrimitiveCategory.FLOATTYPE, true),

		/** _Complex float represented as SMT float */
		COMPLEX_FLOAT_SMT(CPrimitiveCategory.FLOATTYPE, true),

		/** double represented as SMT float */
		DOUBLE_SMT(CPrimitiveCategory.FLOATTYPE, true),

		/** _Complex double represented as SMT float */
		COMPLEX_DOUBLE_SMT(CPrimitiveCategory.FLOATTYPE, true),

		/** long double represented as SMT float */
		LONGDOUBLE_SMT(CPrimitiveCategory.FLOATTYPE, true),

		/** _Complex long double represented as SMT float */
		COMPLEX_LONGDOUBLE_SMT(CPrimitiveCategory.FLOATTYPE, true),

		// TODO: something with "_imaginary"??

		/**
		 * C type : void.
		 */
		VOID(CPrimitiveCategory.VOID);

		private final CPrimitiveCategory mPrimitiveCategory;
		private final boolean mIsSmtFloat;

		private CPrimitives(final CPrimitiveCategory generalprimitive) {
			this(generalprimitive, false);
		}

		private CPrimitives(final CPrimitiveCategory generalprimitive, final boolean isSmtFloat) {
			mPrimitiveCategory = generalprimitive;
			mIsSmtFloat = isSmtFloat;
		}

		public boolean isIntegertype() {
			return mPrimitiveCategory == CPrimitiveCategory.INTTYPE;
		}

		public boolean isFloatingtype() {
			return mPrimitiveCategory == CPrimitiveCategory.FLOATTYPE;
		}

		public CPrimitiveCategory getPrimitiveCategory() {
			return mPrimitiveCategory;
		}

		public boolean isSmtFloat() {
			return mIsSmtFloat;
		}

		/**
		 * Returns true iff this type is a complex type according to the definition 6.2.5.11 of the C11 standard.
		 */
		public boolean isComplexFloat() {
			return this == CPrimitives.COMPLEX_FLOAT || this == CPrimitives.COMPLEX_DOUBLE
					|| this == CPrimitives.COMPLEX_LONGDOUBLE || this == COMPLEX_DOUBLE_SMT || this == COMPLEX_FLOAT_SMT
					|| this == COMPLEX_LONGDOUBLE_SMT;
		}

	}

	public enum CPrimitiveCategory {
		INTTYPE, FLOATTYPE, VOID
	}

	/**
	 * The C type of the variable.
	 */
	private final CPrimitives mType;

	/**
	 * more general type, i.e. inttype, floattype, void -- is derived from type
	 */
	private final CPrimitiveCategory mGeneralType;

	public CPrimitive(final CPrimitives type) {
		// FIXME: integrate those flags -- you will also need to change the equals method if you do
		super(false, false, false, false, false, false);
		mType = type;
		mGeneralType = getGeneralType(type);
	}

	private CPrimitive(final boolean isConst, final boolean isInline, final boolean isRestrict,
			final boolean isVolatile, final boolean isExtern, final boolean isSmtFloat, final CPrimitives type) {
		super(isConst, isInline, isRestrict, isVolatile, isExtern, isSmtFloat);
		mType = type;
		mGeneralType = getGeneralType(mType);
	}

	/**
	 * @see CType#isSmtFloat()
	 */
	public CPrimitive setIsSmtFloat(final boolean isSmtFloat) {
		return new CPrimitive(isConst(), isInline(), isRestrict(), isVolatile(), isExtern(), isSmtFloat, getType());
	}

	/**
	 * Constructor.
	 *
	 * @param cDeclSpec
	 *            the C declaration specifier.
	 */
	public CPrimitive(final IASTDeclSpecifier cDeclSpec) {
		// FIXME: integrate those flags -- you will also need to change the equals method if you do
		super(false, false, false, false, false, false);
		if (cDeclSpec instanceof IASTSimpleDeclSpecifier) {
			final IASTSimpleDeclSpecifier sds = (IASTSimpleDeclSpecifier) cDeclSpec;
			switch (sds.getType()) {
			case IASTSimpleDeclSpecifier.t_bool:
				mType = CPrimitives.BOOL;
				break;
			case IASTSimpleDeclSpecifier.t_char:
				if (sds.isSigned()) {
					mType = CPrimitives.SCHAR;
				} else if (sds.isUnsigned()) {
					mType = CPrimitives.UCHAR;
				} else {
					mType = CPrimitives.CHAR;
				}
				break;
			case IASTSimpleDeclSpecifier.t_double:
				if (sds.isComplex()) {
					if (sds.isLong()) {
						mType = CPrimitives.COMPLEX_LONGDOUBLE;
					} else {
						mType = CPrimitives.COMPLEX_DOUBLE;
					}
				} else {
					if (sds.isLong()) {
						mType = CPrimitives.LONGDOUBLE;
					} else {
						mType = CPrimitives.DOUBLE;
					}
				}
				break;
			case IASTSimpleDeclSpecifier.t_float:
				if (sds.isComplex()) {
					mType = CPrimitives.COMPLEX_FLOAT;
				} else {
					mType = CPrimitives.FLOAT;
				}
				break;
			case IASTSimpleDeclSpecifier.t_int:
				if (sds.isUnsigned()) {
					if (sds.isLong()) {
						mType = CPrimitives.ULONG;
					} else if (sds.isLongLong()) {
						mType = CPrimitives.ULONGLONG;
					} else if (sds.isShort()) {
						mType = CPrimitives.USHORT;
					} else {
						mType = CPrimitives.UINT;
					}
				} else if (sds.isLong()) {
					mType = CPrimitives.LONG;
				} else if (sds.isLongLong()) {
					mType = CPrimitives.LONGLONG;
				} else if (sds.isShort()) {
					mType = CPrimitives.SHORT;
				} else {
					mType = CPrimitives.INT;
				}
				break;
			case IASTSimpleDeclSpecifier.t_unspecified:
				if (sds.isUnsigned()) {
					if (sds.isLong()) {
						mType = CPrimitives.ULONG;
					} else if (sds.isLongLong()) {
						mType = CPrimitives.ULONGLONG;
					} else if (sds.isShort()) {
						mType = CPrimitives.USHORT;
					} else {
						mType = CPrimitives.UINT;
					}
				} else if (sds.isLong()) {
					mType = CPrimitives.LONG;
				} else if (sds.isLongLong()) {
					mType = CPrimitives.LONGLONG;
				} else if (sds.isShort()) {
					mType = CPrimitives.SHORT;
				} else {
					mType = CPrimitives.INT;
				}
				break;
			case IASTSimpleDeclSpecifier.t_void:
				mType = CPrimitives.VOID;
				break;
			// case IASTSimpleDeclSpecifier.t_wchar_t:
			// this.type = PRIMITIVE.WCHAR;
			// break;
			default:
				throw new IllegalArgumentException("Unknown C Declaration!");
			}
		} else {
			throw new IllegalArgumentException("Unknown C Declaration!");
		}
		mGeneralType = getGeneralType(mType);
	}

	private static CPrimitiveCategory getGeneralType(final CPrimitives type) throws AssertionError {
		switch (type) {
		case COMPLEX_FLOAT:
		case COMPLEX_DOUBLE:
		case COMPLEX_LONGDOUBLE:
		case FLOAT:
		case DOUBLE:
		case LONGDOUBLE:
		case COMPLEX_DOUBLE_SMT:
		case COMPLEX_FLOAT_SMT:
		case COMPLEX_LONGDOUBLE_SMT:
		case DOUBLE_SMT:
		case FLOAT_SMT:
		case LONGDOUBLE_SMT:
			return CPrimitiveCategory.FLOATTYPE;
		case BOOL:
		case UCHAR:
		case UINT:
		case ULONG:
		case ULONGLONG:
		case USHORT:
		case CHAR:
		case INT:
		case LONG:
		case LONGLONG:
		case SCHAR:
		case SHORT:
			return CPrimitiveCategory.INTTYPE;
		case VOID:
			return CPrimitiveCategory.VOID;
		default:
			throw new UnsupportedOperationException("Unknown case " + type);
		}
	}

	public CPrimitives getType() {
		return mType;
	}

	public CPrimitiveCategory getGeneralType() {
		return mGeneralType;
	}

	@Override
	public String toString() {
		return mType.toString();
	}

	@Override
	public boolean isCompatibleWith(final CType o) {
		final CType oType = o.getUnderlyingType();

		if (oType instanceof CEnum && mGeneralType == CPrimitiveCategory.INTTYPE) {
			return true;
		}

		if (oType instanceof CPrimitive) {
			return mType == ((CPrimitive) oType).mType;
		}
		return false;
	}

	@Override
	public boolean isIncomplete() {
		return mType == CPrimitives.VOID;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((mGeneralType == null) ? 0 : mGeneralType.hashCode());
		result = prime * result + ((mType == null) ? 0 : mType.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object o) {
		if (!(o instanceof CType)) {
			return false;
		}
		final CType oType = ((CType) o).getUnderlyingType();
		if (oType instanceof CPrimitive) {
			return mType == ((CPrimitive) oType).mType;
		}
		return false;
	}
}
