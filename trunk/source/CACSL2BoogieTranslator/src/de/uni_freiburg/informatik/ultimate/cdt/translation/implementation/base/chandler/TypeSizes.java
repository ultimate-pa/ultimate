/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.LinkedHashMap;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.Signedness;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;

/**
 * Provides the information if we want to use fixed sizes for types. If yes an object of this class also provides the
 * bytesize for each type.
 *
 *
 * @author Matthias Heizmann
 */
public class TypeSizes {
	private final boolean mUseFixedTypeSizes;
	private final int mSizeOfPointerType;
	/**
	 * is char (without modifier) schar or uchar?
	 */
	private final Signedness mSignednessOfChar;

	private final LinkedHashMap<CPrimitive.CPrimitives, Integer> mCPrimitiveToTypeSizeConstant;

	private final TranslationSettings mSettings;

	public TypeSizes(final IPreferenceProvider ups, final TranslationSettings settings) {
		mUseFixedTypeSizes = ups.getBoolean(CACSLPreferenceInitializer.LABEL_USE_EXPLICIT_TYPESIZES);
		mSettings = settings;

		final int sizeOfBoolType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_BOOL);
		final int sizeOfCharType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_CHAR);
		final int sizeOfShortType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_SHORT);
		final int sizeOfIntType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_INT);
		final int sizeOfLongType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_LONG);
		final int sizeOfLongLongType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_LONGLONG);
		final int sizeOfFloatType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_FLOAT);
		final int sizeOfDoubleType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_DOUBLE);
		final int sizeOfLongDoubleType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_LONGDOUBLE);
		mSizeOfPointerType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_POINTER);
		mSignednessOfChar = ups.getEnum(CACSLPreferenceInitializer.LABEL_SIGNEDNESS_CHAR, Signedness.class);

		mCPrimitiveToTypeSizeConstant = new LinkedHashMap<>();
		// for pointer arithmetic on a void pointer -- c standard disallows that, but
		// gcc does not..
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.VOID, 1);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.BOOL, sizeOfBoolType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.CHAR, sizeOfCharType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.SCHAR, sizeOfCharType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.UCHAR, sizeOfCharType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.SHORT, sizeOfShortType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.USHORT, sizeOfShortType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.INT, sizeOfIntType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.UINT, sizeOfIntType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.LONG, sizeOfLongType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.ULONG, sizeOfLongType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.LONGLONG, sizeOfLongLongType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.ULONGLONG, sizeOfLongLongType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.DOUBLE, sizeOfDoubleType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.FLOAT, sizeOfFloatType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.LONGDOUBLE, sizeOfLongDoubleType);

		mCPrimitiveToTypeSizeConstant.put(CPrimitives.COMPLEX_DOUBLE, sizeOfDoubleType * 2);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.COMPLEX_FLOAT, sizeOfFloatType * 2);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.COMPLEX_LONGDOUBLE, sizeOfLongDoubleType * 2);

		// Hardcoded to 16 bytes. According to the GNU C is could probably also be larger
		// https://gcc.gnu.org/onlinedocs/gcc/_005f_005fint128.html
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.INT128, 16);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.UINT128, 16);
		// Hardcoded to 16 bytes https://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.FLOAT128, 16);
	}

	public boolean useFixedTypeSizes() {
		return mUseFixedTypeSizes;
	}

	public Integer getSize(final CPrimitives cPrimitive) {
		final Integer result = mCPrimitiveToTypeSizeConstant.get(cPrimitive);
		if (result == null) {
			throw new IllegalArgumentException("unknown type " + cPrimitive);
		}
		return result;
	}

	public int getSizeOfPointer() {
		return mSizeOfPointerType;
	}

	public boolean isUnsigned(final CPrimitive type) {
		return isUnsigned(type.getType());
	}

	public boolean isUnsigned(final CPrimitives type) throws AssertionError {
		switch (type) {
		case BOOL:
		case UCHAR:
		case UINT:
		case ULONG:
		case ULONGLONG:
		case USHORT:
		case UINT128:
			return true;
		case CHAR:
			return mSignednessOfChar == Signedness.UNSIGNED;
		case INT:
		case LONG:
		case LONGLONG:
		case SCHAR:
		case SHORT:
		case INT128:
			return false;
		case COMPLEX_FLOAT:
		case COMPLEX_DOUBLE:
		case COMPLEX_LONGDOUBLE:
		case FLOAT:
		case FLOAT128:
		case DOUBLE:
		case LONGDOUBLE:
			// case CHAR16:
			// case CHAR32:
			// case WCHAR:
		case VOID:
			throw new IllegalArgumentException("attribute signedness not applicable to " + type);
		default:
			throw new AssertionError("case missing");
		}
	}

	public BigInteger getMaxValueOfPrimitiveType(final CPrimitive cPrimitive) {
		final int byteSize = getSize(cPrimitive.getType());
		int exponent;
		if (isUnsigned(cPrimitive)) {
			exponent = byteSize * 8;
		} else {
			exponent = byteSize * 8 - 1;
		}
		return BigInteger.TWO.pow(exponent).subtract(BigInteger.ONE);
	}

	public BigInteger getMinValueOfPrimitiveType(final CPrimitive cPrimitive) {
		if (isUnsigned(cPrimitive)) {
			return BigInteger.ZERO;
		}
		return BigInteger.TWO.pow(getSize(cPrimitive.getType()) * 8 - 1).negate();
	}

	public BigInteger getMaxValueOfPointer() {
		return BigInteger.TWO.pow(mSizeOfPointerType * 8).subtract(BigInteger.ONE);
	}

	/**
	 * @return FloatingPointSize of a float, double, or long double.
	 */
	public FloatingPointSize getFloatingPointSize(final CPrimitives cPrimitive) {
		final int sizeof = getSize(cPrimitive);
		switch (cPrimitive) {
		case FLOAT:
			if (sizeof != 4) {
				throw new UnsupportedOperationException("unsupported sizeof " + cPrimitive + "==" + sizeof);
			}
			return new FloatingPointSize(sizeof, 24, 8);
		case DOUBLE:
			if (sizeof != 8) {
				throw new UnsupportedOperationException("unsupported sizeof " + cPrimitive + "==" + sizeof);
			}
			return new FloatingPointSize(sizeof, 53, 11);
		case LONGDOUBLE:
			// 12 because of 80bit long doubles on linux x86
			if (sizeof != 12 && sizeof != 16) {
				throw new UnsupportedOperationException("unsupported sizeof " + cPrimitive + "==" + sizeof);
			}
			return new FloatingPointSize(sizeof, 113, 15);
		case FLOAT128:
			if (sizeof != 16) {
				throw new UnsupportedOperationException("unsupported sizeof " + cPrimitive + "==" + sizeof);
			}
			return new FloatingPointSize(sizeof, 113, 15);
		default:
			throw new IllegalArgumentException("not real floating type " + cPrimitive);
		}
	}

	public CPrimitive getCorrespondingUnsignedType(final CPrimitive type) {
		if (!type.isIntegerType()) {
			throw new IllegalArgumentException("no integer type " + this);
		}
		if (isUnsigned(type)) {
			throw new IllegalArgumentException("already unsigned " + this);
		}
		switch (type.getType()) {
		case CHAR:
			if (mSignednessOfChar == Signedness.SIGNED) {
				return new CPrimitive(CPrimitives.UCHAR);
			}
			throw new UnsupportedOperationException("according to your settings, char is already unsigned");
		case INT:
			return new CPrimitive(CPrimitives.UINT);
		case LONG:
			return new CPrimitive(CPrimitives.ULONG);
		case LONGLONG:
			return new CPrimitive(CPrimitives.ULONGLONG);
		case SCHAR:
			return new CPrimitive(CPrimitives.UCHAR);
		case SHORT:
			return new CPrimitive(CPrimitives.USHORT);
		case INT128:
			return new CPrimitive(CPrimitives.UINT128);
		default:
			throw new IllegalArgumentException("unsupported type " + this);
		}
	}

	public Signedness getSignednessOfChar() {
		return mSignednessOfChar;
	}

	public CPrimitive getSizeT() {
		return new CPrimitive(CPrimitives.ULONG);
	}

	public CPrimitive getSsizeT() {
		return new CPrimitive(CPrimitives.LONG);
	}

	public Expression constructLiteralForIntegerType(final ILocation loc, final CPrimitive type,
			final BigInteger value) {
		return ISOIEC9899TC3.constructLiteralForCIntegerLiteral(loc, mSettings.isBitvectorTranslation(), this, type,
				value);
	}

	/**
	 * Try to get the value of RValue rval. Returns null if extraction is impossible. Extraction might succeed if rval
	 * represents a constant value. Extraction fails, e.g., if rval represents a variable.
	 *
	 * @param expr
	 *
	 * @return
	 */
	public BigInteger extractIntegerValue(final RValue rval) {
		return extractIntegerValue(rval.getValue(), rval.getCType().getUnderlyingType());
	}

	public BigInteger extractIntegerValue(final Expression expr, final CType cType) {
		if (expr instanceof IntegerLiteral) {
			final BigInteger value = new BigInteger(((IntegerLiteral) expr).getValue());
			final CPrimitive cPrimitive = (CPrimitive) CEnum.replaceEnumWithInt(cType);
			if (!isUnsigned(cPrimitive)) {
				return value;
			}
			// Because of the congruence based transformation we do a modulo operation.
			// Otherwise we do not extract the correct value for negative literals of unsigned type.
			final BigInteger maxValue = getMaxValueOfPrimitiveType(cPrimitive);
			final BigInteger maxValuePlusOne = maxValue.add(BigInteger.ONE);
			return value.mod(maxValuePlusOne);
		}
		if (expr instanceof BitvecLiteral) {
			final BigInteger value = new BigInteger(((BitvecLiteral) expr).getValue());
			final CPrimitive cPrimitive = (CPrimitive) CEnum.replaceEnumWithInt(cType);
			if (isUnsigned(cPrimitive)) {
				if (getMinValueOfPrimitiveType(cPrimitive).compareTo(value) > 0) {
					throw new AssertionError("Value too small for type " + cType);
				}
				if (getMaxValueOfPrimitiveType(cPrimitive).compareTo(value) < 0) {
					throw new AssertionError("Value too large for type " + cType);
				}
				// Return simply the value of the BitvecLiteral.
				return value;
			}
			final int bitsize = 8 * getSize(cPrimitive.getType());
			final BitvectorConstant bc = new BitvectorConstant(value, BigInteger.valueOf(bitsize));
			return bc.toSignedInt();
		}
		return null;
	}

	/**
	 * The size of a real floating point type is defined by a significant and an exponent.
	 */
	public static final class FloatingPointSize {
		private final int mSignificant;
		private final int mExponent;
		private final int mByteSize;

		public FloatingPointSize(final int byteSize, final int significant, final int exponent) {
			mSignificant = significant;
			mExponent = exponent;
			mByteSize = byteSize;
		}

		public int getSignificant() {
			return mSignificant;
		}

		public int getExponent() {
			return mExponent;
		}

		public int getByteSize() {
			return mByteSize;
		}

		/**
		 * @return an int array containing the exponent and the significant
		 */
		public int[] getIndices() {
			return new int[] { getExponent(), getSignificant() };
		}
	}

}
