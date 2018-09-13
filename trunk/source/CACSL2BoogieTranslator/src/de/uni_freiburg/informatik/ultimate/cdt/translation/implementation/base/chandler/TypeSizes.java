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

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationState;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.Signedness;

/**
 * Provides the information if we want to use fixed sizes for types.
 * If yes an object of this class also provides the bytesize for each type.
 *
 *
 * @author Matthias Heizmann
 */
public class TypeSizes {
	private final boolean mUseFixedTypeSizes;

	private final int sizeOfBoolType;
	private final int sizeOfCharType;
	private final int sizeOfShortType;
	private final int sizeOfIntType;
	private final int sizeOfLongType;
	private final int sizeOfLongLongType;
	private final int sizeOfFloatType;
	private final int sizeOfDoubleType;
	private final int sizeOfLongDoubleType;
	private final int sizeOfPointerType;

//	private final int sizeOfWCharType;
//	private final int sizeOfChar16Type;
//	private final int sizeOfChar32Type;

//	for pointer arithmetic on a void pointer -- c standard disallows that, but gcc does not..
	private final int sizeOfVoidType;

	/**
	 * is char (without modifier) schar or uchar?
	 */
	private final Signedness mSignednessOfChar;

	private final LinkedHashMap<CPrimitive.CPrimitives, Integer> CPrimitiveToTypeSizeConstant =
			new LinkedHashMap<>();


	public TypeSizes(final IPreferenceProvider ups, final CTranslationState handlerHandler) {
		handlerHandler.setTypeSizes(this);

		mUseFixedTypeSizes =
				ups.getBoolean(CACSLPreferenceInitializer.LABEL_USE_EXPLICIT_TYPESIZES);
		sizeOfVoidType = 1;
		sizeOfBoolType =
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_BOOL);
		sizeOfCharType =
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_CHAR);
		sizeOfShortType =
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_SHORT);
		sizeOfIntType =
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_INT);
		sizeOfLongType =
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_LONG);
		sizeOfLongLongType =
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_LONGLONG);
		sizeOfFloatType =
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_FLOAT);
		sizeOfDoubleType =
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_DOUBLE);
		sizeOfLongDoubleType =
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_LONGDOUBLE);
		sizeOfPointerType =
				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_POINTER);
		mSignednessOfChar = ups.getEnum(CACSLPreferenceInitializer.LABEL_SIGNEDNESS_CHAR, Signedness.class);
//		this.sizeOfChar16Type =
//				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_CHAR16);
//		this.sizeOfChar32Type =
//				ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_CHAR32);

		CPrimitiveToTypeSizeConstant.put(CPrimitives.VOID, sizeOfVoidType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.BOOL, sizeOfBoolType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.CHAR, sizeOfCharType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.SCHAR, sizeOfCharType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.UCHAR, sizeOfCharType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.SHORT, sizeOfShortType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.USHORT, sizeOfShortType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.INT, sizeOfIntType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.UINT, sizeOfIntType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.LONG, sizeOfLongType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.ULONG, sizeOfLongType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.LONGLONG, sizeOfLongLongType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.ULONGLONG, sizeOfLongLongType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.DOUBLE, sizeOfDoubleType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.FLOAT, sizeOfFloatType);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.LONGDOUBLE, sizeOfLongDoubleType);

		CPrimitiveToTypeSizeConstant.put(CPrimitives.COMPLEX_DOUBLE, sizeOfDoubleType * 2);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.COMPLEX_FLOAT, sizeOfFloatType * 2);
		CPrimitiveToTypeSizeConstant.put(CPrimitives.COMPLEX_LONGDOUBLE, sizeOfLongDoubleType * 2);

//		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.CHAR16, this.sizeOfChar16Type);
//		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.CHAR32, this.sizeOfChar32Type);
//		CPrimitiveToTypeSizeConstant.put(PRIMITIVE.WCHAR, this.sizeOfWCharType);
	}


	public boolean useFixedTypeSizes() {
		return mUseFixedTypeSizes;
	}


	public Integer getSize(final CPrimitives cPrimitive) {
		final Integer result = CPrimitiveToTypeSizeConstant.get(cPrimitive);
		if (result == null) {
			throw new IllegalArgumentException("unknown type " + cPrimitive);
		} else {
			return result;
		}
	}

	public int getSizeOfPointer() {
		return sizeOfPointerType;
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
			return true;
		case CHAR:
			return (mSignednessOfChar == Signedness.UNSIGNED);
		case INT:
		case LONG:
		case LONGLONG:
		case SCHAR:
		case SHORT:
			return false;
		case COMPLEX_FLOAT:
		case COMPLEX_DOUBLE:
		case COMPLEX_LONGDOUBLE:
		case FLOAT:
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

	private boolean isComplex(final CPrimitives type) {
		switch (type) {
		case COMPLEX_FLOAT:
		case COMPLEX_DOUBLE:
		case COMPLEX_LONGDOUBLE:
			return true;
		default:
			return false;
		}
	}

	public BigInteger getMaxValueOfPrimitiveType(final CPrimitive cPrimitive) {
		final int byteSize = getSize(cPrimitive.getType());
		BigInteger maxValue;
		if (isUnsigned(cPrimitive)) {
			maxValue = new BigInteger("2").pow(byteSize * 8);
		} else {
			maxValue = new BigInteger("2").pow(byteSize * 8 - 1);
		}
		maxValue = maxValue.subtract(BigInteger.ONE);
		return maxValue;
	}

	public BigInteger getMinValueOfPrimitiveType(final CPrimitive cPrimitive) {
		final int byteSize = getSize(cPrimitive.getType());
		BigInteger minValue;
		if (isUnsigned(cPrimitive)) {
			minValue = BigInteger.ZERO;
		} else {
			minValue = (new BigInteger("2").pow(byteSize * 8 - 1)).negate();
		}
		return minValue;
	}

	public BigInteger getMaxValueOfPointer() {
		final int byteSize = sizeOfPointerType;
		BigInteger maxValue = new BigInteger("2").pow(byteSize * 8);
		maxValue = maxValue.subtract(BigInteger.ONE);
		return maxValue;
	}

	/**
	 * @return FloatingPointSize of a float, double, or long double.
	 */
	public FloatingPointSize getFloatingPointSize(final CPrimitives cPrimitive) {
		final FloatingPointSize result;
		switch (cPrimitive) {
		case FLOAT: {
			final int sizeof = getSize(cPrimitive);
			if (sizeof == 4) {
				result = new FloatingPointSize(24, 8);
			} else {
				throw new UnsupportedOperationException("unsupported sizeof " + cPrimitive + "==" + sizeof);
			}
		}
		break;
		case DOUBLE: {
			final int sizeof = getSize(cPrimitive);
			if (sizeof == 8) {
				result = new FloatingPointSize(53, 11);
			} else {
				throw new UnsupportedOperationException("unsupported sizeof " + cPrimitive + "==" + sizeof);
			}
		}
		break;
		case LONGDOUBLE: {
			final int sizeof = getSize(cPrimitive);
			if (sizeof == 12 || sizeof == 16) {
				result = new FloatingPointSize(113, 15);
			} else {
				throw new UnsupportedOperationException("unsupported sizeof " + cPrimitive + "==" + sizeof);
			}
		}
		break;
		default:
			throw new IllegalArgumentException("not real floating type " + cPrimitive);
		}
		return result;
	}

	/**
	 * The size of a real floating point type is defined by a significant
	 * and an exponent.
	 */
	public class FloatingPointSize {
		final int mSignificant;
		final int mExponent;
		public FloatingPointSize(final int significant, final int exponent) {
			super();
			mSignificant = significant;
			mExponent = exponent;
		}
		public int getSignificant() {
			return mSignificant;
		}
		public int getExponent() {
			return mExponent;
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
			} else {
				throw new UnsupportedOperationException("according to your settings, char is already unsigned");
			}
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
		default:
			throw new IllegalArgumentException("unsupported type " + this);
		}
	}

	public Signedness getSignednessOfChar() {
		return mSignednessOfChar;
	}
	
	
}
