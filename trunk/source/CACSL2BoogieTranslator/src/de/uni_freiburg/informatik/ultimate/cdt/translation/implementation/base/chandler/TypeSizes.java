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

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
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

/**
 * Provides the information if we want to use fixed sizes for types. If yes an object of this class also provides the
 * bytesize for each type.
 *
 *
 * @author Matthias Heizmann
 */
public class TypeSizes {
	private final boolean mUseFixedTypeSizes;

	private final int mSizeOfBoolType;
	private final int mSizeOfCharType;
	private final int mSizeOfShortType;
	private final int mSizeOfIntType;
	private final int mSizeOfLongType;
	private final int mSizeOfLongLongType;
	private final int mSizeOfFloatType;
	private final int mSizeOfDoubleType;
	private final int mSizeOfLongDoubleType;
	private final int mSizeOfPointerType;

	// for pointer arithmetic on a void pointer -- c standard disallows that, but gcc does not..
	private final int mSizeOfVoidType;

	/**
	 * is char (without modifier) schar or uchar?
	 */
	private final Signedness mSignednessOfChar;

	private final LinkedHashMap<CPrimitive.CPrimitives, Integer> mCPrimitiveToTypeSizeConstant;

	private final FlatSymbolTable mSymboltable;

	private final TranslationSettings mSettings;

	public TypeSizes(final IPreferenceProvider ups, final TranslationSettings settings,
			final FlatSymbolTable symbolTable) {
		mSymboltable = symbolTable;
		mUseFixedTypeSizes = ups.getBoolean(CACSLPreferenceInitializer.LABEL_USE_EXPLICIT_TYPESIZES);
		mSettings = settings;
		mCPrimitiveToTypeSizeConstant = new LinkedHashMap<>();

		mSizeOfVoidType = 1;
		mSizeOfBoolType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_BOOL);
		mSizeOfCharType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_CHAR);
		mSizeOfShortType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_SHORT);
		mSizeOfIntType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_INT);
		mSizeOfLongType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_LONG);
		mSizeOfLongLongType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_LONGLONG);
		mSizeOfFloatType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_FLOAT);
		mSizeOfDoubleType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_DOUBLE);
		mSizeOfLongDoubleType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_LONGDOUBLE);
		mSizeOfPointerType = ups.getInt(CACSLPreferenceInitializer.LABEL_EXPLICIT_TYPESIZE_POINTER);
		mSignednessOfChar = ups.getEnum(CACSLPreferenceInitializer.LABEL_SIGNEDNESS_CHAR, Signedness.class);

		mCPrimitiveToTypeSizeConstant.put(CPrimitives.VOID, mSizeOfVoidType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.BOOL, mSizeOfBoolType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.CHAR, mSizeOfCharType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.SCHAR, mSizeOfCharType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.UCHAR, mSizeOfCharType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.SHORT, mSizeOfShortType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.USHORT, mSizeOfShortType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.INT, mSizeOfIntType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.UINT, mSizeOfIntType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.LONG, mSizeOfLongType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.ULONG, mSizeOfLongType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.LONGLONG, mSizeOfLongLongType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.ULONGLONG, mSizeOfLongLongType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.DOUBLE, mSizeOfDoubleType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.FLOAT, mSizeOfFloatType);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.LONGDOUBLE, mSizeOfLongDoubleType);

		mCPrimitiveToTypeSizeConstant.put(CPrimitives.COMPLEX_DOUBLE, mSizeOfDoubleType * 2);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.COMPLEX_FLOAT, mSizeOfFloatType * 2);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.COMPLEX_LONGDOUBLE, mSizeOfLongDoubleType * 2);
	}

	public TypeSizes(final TypeSizes prerunTypeSizes, final FlatSymbolTable symbolTable) {
		mSymboltable = symbolTable;

		mUseFixedTypeSizes = prerunTypeSizes.mUseFixedTypeSizes;
		mSettings = prerunTypeSizes.mSettings;
		mCPrimitiveToTypeSizeConstant = prerunTypeSizes.mCPrimitiveToTypeSizeConstant;

		mSizeOfVoidType = prerunTypeSizes.mSizeOfVoidType;
		mSizeOfBoolType = prerunTypeSizes.mSizeOfBoolType;
		mSizeOfCharType = prerunTypeSizes.mSizeOfCharType;
		mSizeOfShortType = prerunTypeSizes.mSizeOfShortType;
		mSizeOfIntType = prerunTypeSizes.mSizeOfIntType;
		mSizeOfLongType = prerunTypeSizes.mSizeOfLongType;
		mSizeOfLongLongType = prerunTypeSizes.mSizeOfLongLongType;
		mSizeOfFloatType = prerunTypeSizes.mSizeOfFloatType;
		mSizeOfDoubleType = prerunTypeSizes.mSizeOfDoubleType;
		mSizeOfLongDoubleType = prerunTypeSizes.mSizeOfLongDoubleType;
		mSizeOfPointerType = prerunTypeSizes.mSizeOfPointerType;
		mSignednessOfChar = prerunTypeSizes.mSignednessOfChar;
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
			return true;
		case CHAR:
			return mSignednessOfChar == Signedness.UNSIGNED;
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

	private static boolean isComplex(final CPrimitives type) {
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
			minValue = new BigInteger("2").pow(byteSize * 8 - 1).negate();
		}
		return minValue;
	}

	public BigInteger getMaxValueOfPointer() {
		final int byteSize = mSizeOfPointerType;
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
		default:
			throw new IllegalArgumentException("unsupported type " + this);
		}
	}

	public Signedness getSignednessOfChar() {
		return mSignednessOfChar;
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
	 * @return
	 */
	public BigInteger extractIntegerValue(final RValue rval, final IASTNode hook) {
		return extractIntegerValue(rval.getValue(), rval.getCType().getUnderlyingType(), hook);
	}

	public BigInteger extractIntegerValue(final Expression expr, final CType cType, final IASTNode hook) {
		if (mSettings.isBitvectorTranslation()) {
			return extractIntegerValueBitvector(expr, cType, hook);
		}
		return extractIntegerValueInteger(expr, cType, hook);
	}

	private BigInteger extractIntegerValueInteger(final Expression expr, final CType cType, final IASTNode hook) {
		if (cType.isIntegerType()) {
			if (expr instanceof IntegerLiteral) {
				final BigInteger value = new BigInteger(((IntegerLiteral) expr).getValue());
				if (isUnsigned((CPrimitive) cType)) {
					final BigInteger maxValue = getMaxValueOfPrimitiveType((CPrimitive) cType);
					final BigInteger maxValuePlusOne = maxValue.add(BigInteger.ONE);
					return value.mod(maxValuePlusOne);
				}
				return value;
			} else if (expr instanceof IdentifierExpression) {
				// An IdentifierExpression may be an alias for an integer value, this is stored in the symbol table.
				final String bId = ((IdentifierExpression) expr).getIdentifier();
				final String cId = mSymboltable.getCIdForBoogieId(bId);
				final SymbolTableValue stv = mSymboltable.findCSymbol(hook, cId);
				if (stv.hasConstantValue()) {
					return extractIntegerValue(stv.getConstantValue(), cType, hook);
				}
			} else if (expr instanceof BinaryExpression) {
				final BigInteger leftValue = extractIntegerValue(((BinaryExpression) expr).getLeft(), cType, hook);
				final BigInteger rightValue = extractIntegerValue(((BinaryExpression) expr).getRight(), cType, hook);

				switch (((BinaryExpression) expr).getOperator()) {
				case ARITHDIV:
					return leftValue.divide(rightValue);
				case ARITHMINUS:
					return leftValue.subtract(rightValue);
				case ARITHMOD:
					return leftValue.mod(rightValue);
				case ARITHMUL:
					return leftValue.multiply(rightValue);
				case ARITHPLUS:
					return leftValue.add(rightValue);
				default:
					return null;
				}
			}
			return null;
		}
		return null;
	}

	private BigInteger extractIntegerValueBitvector(final Expression expr, CType cType, final IASTNode hook) {
		if (cType.isIntegerType()) {
			cType = CEnum.replaceEnumWithInt(cType);
			if (expr instanceof BitvecLiteral) {
				final BigInteger value = new BigInteger(((BitvecLiteral) expr).getValue());
				if (isUnsigned((CPrimitive) cType)) {
					if (value.signum() < 0) {
						throw new UnsupportedOperationException("negative value");
					}
					return value;
				}
				return value;
			} else if (expr instanceof IdentifierExpression) {
				// An IdentifierExpression may be an alias for an integer value, this is stored in the symbol table.
				final String bId = ((IdentifierExpression) expr).getIdentifier();
				final String cId = mSymboltable.getCIdForBoogieId(bId);
				final SymbolTableValue stv = mSymboltable.findCSymbol(hook, cId);
				if (stv.hasConstantValue()) {
					return extractIntegerValue(stv.getConstantValue(), cType, hook);
				}
			}
			return null;
		}
		return null;
	}

	/**
	 * The size of a real floating point type is defined by a significant and an exponent.
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

}
