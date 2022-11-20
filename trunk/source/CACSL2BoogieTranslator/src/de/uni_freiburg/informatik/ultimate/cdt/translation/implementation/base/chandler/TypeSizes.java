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

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.Signedness;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.BitvectorConstantOperationResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.BvOp;

/**
 * Provides the information if we want to use fixed sizes for types. If yes an
 * object of this class also provides the bytesize for each type.
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
	private final int mSizeOfInt128Type;

	// for pointer arithmetic on a void pointer -- c standard disallows that, but
	// gcc does not..
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
		// Hardcoded to 16 bytes. According to the GNU C is could probably also be
		// larger
		// https://gcc.gnu.org/onlinedocs/gcc/_005f_005fint128.html
		mSizeOfInt128Type = 16;

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
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.INT128, mSizeOfInt128Type);
		mCPrimitiveToTypeSizeConstant.put(CPrimitives.UINT128, mSizeOfInt128Type);
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
		mSizeOfInt128Type = prerunTypeSizes.mSizeOfInt128Type;
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
				result = new FloatingPointSize(sizeof, 24, 8);
			} else {
				throw new UnsupportedOperationException("unsupported sizeof " + cPrimitive + "==" + sizeof);
			}
		}
			break;
		case DOUBLE: {
			final int sizeof = getSize(cPrimitive);
			if (sizeof == 8) {
				result = new FloatingPointSize(sizeof, 53, 11);
			} else {
				throw new UnsupportedOperationException("unsupported sizeof " + cPrimitive + "==" + sizeof);
			}
		}
			break;
		case LONGDOUBLE: {
			final int sizeof = getSize(cPrimitive);
			// 12 because of 80bit long doubles on linux x86
			if (sizeof == 12 || sizeof == 16) {
				result = new FloatingPointSize(sizeof, 113, 15);
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
	 * Try to get the value of RValue rval. Returns null if extraction is
	 * impossible. Extraction might succeed if rval represents a constant value.
	 * Extraction fails, e.g., if rval represents a variable.
	 *
	 * @param expr
	 * @return
	 */
	public BigInteger extractIntegerValue(final RValue rval, final IASTNode hook) {
		return extractIntegerValue(rval.getValue(), rval.getCType().getUnderlyingType(), hook);
	}

	public BigInteger extractIntegerValue(final Expression expr, final CType cType, final IASTNode hook) {
		final BigInteger tmp = extractIntegerValue(expr, hook);
		if (tmp == null) {
			return null;
		}

		if (!(cType instanceof CPrimitive)) {
			throw new AssertionError("Expected only CPrimitive but got " + cType);
		}
		final CPrimitive cPrimitive = (CPrimitive) cType;
		if (mSettings.isBitvectorTranslation()) {
			if (isUnsigned(cPrimitive)) {
				// my return as is
				if (getMinValueOfPrimitiveType(cPrimitive).compareTo(tmp) > 0) {
					throw new AssertionError("Value too small for type " + cType);
				}
				if (getMaxValueOfPrimitiveType(cPrimitive).compareTo(tmp) < 0) {
					throw new AssertionError("Value too large for type " + cType);
				}
				return tmp;
			} else {
				// is signed
				final Integer bytesize = getSize(cPrimitive.getType());
				final int bitsize = bytesize * 8;
				final BitvectorConstant bc = new BitvectorConstant(tmp, BigInteger.valueOf(bitsize));
				return bc.toSignedInt();
			}
		} else {
			// integer translation
			if (isUnsigned(cPrimitive)) {
				// TODO 20221119 Matthias: Because of the Nutz transformation we do
				// do a modulo operation. It don't think this should be necessary,
				// but it won't hurt and I don't have the time to check.
				final BigInteger maxValue = getMaxValueOfPrimitiveType((CPrimitive) cType);
				final BigInteger maxValuePlusOne = maxValue.add(BigInteger.ONE);
				return tmp.mod(maxValuePlusOne);
			} else {
				return tmp;
			}
		}
	}

	private BigInteger extractIntegerValue(final Expression expr, final IASTNode hook) {
		if (expr instanceof IntegerLiteral) {
			return extractIntegerValueFromIntegerLiteral(expr);
		} else if (expr instanceof BitvecLiteral) {
			return extractIntegerValueFromBitvectorLiteral((BitvecLiteral) expr);
		} else if (expr instanceof IdentifierExpression) {
			return extractIntegerValueFromIdentifierExpression((IdentifierExpression) expr, hook);
		} else if (expr instanceof BinaryExpression) {
			return extractIntegerValueFromBinaryExpression((BinaryExpression) expr, hook);
		} else if (expr instanceof IfThenElseExpression) {
			return extractIntegerValueFromIfThenElseExpression(expr, hook);
		} else if (expr instanceof FunctionApplication) {
			return extractIntegerValueFromBitvectorFunctionApplication(expr, hook);
		} else if (expr instanceof BitVectorAccessExpression) {
			return extractIntegerValueFromBitVectorAccessExpression((BitVectorAccessExpression) expr, hook);
		} else {
			throw new AssertionError("Unknown Expression " + expr.getClass().getSimpleName());
		}
	}

	private BigInteger extractIntegerValueFromBitVectorAccessExpression(final BitVectorAccessExpression expr,
			final IASTNode hook) {
		final Expression operand = expr.getBitvec();
		final BigInteger value = extractIntegerValue(operand, hook);
		if (value == null) {
			return null;
		} else {
			return ExpressionFactory.constructBitvectorAccessExpressionResult(value, expr.getEnd(), expr.getStart());
		}
	}

	private BigInteger extractIntegerValueFromBitvectorFunctionApplication(final Expression expr, final IASTNode hook) {
		final FunctionApplication funApp = (FunctionApplication) expr;
		final Expression[] args = funApp.getArguments();
		// TODO Matthias 20221119 Avoid code duplication in the following two sections
		if (funApp.getIdentifier().startsWith(SFO.AUXILIARY_FUNCTION_PREFIX + BvOp.sign_extend)) {
			// remove the `~sign_extendFrom` it remains a string of the form aTob, where a
			// and b are natural numbers in a decimal representation
			final String range = funApp.getIdentifier().substring(16);
			final String[] res = range.split("To");
			if (res.length != 2) {
				throw new AssertionError();
			}
			final int from = Integer.parseInt(res[0]);
			final int to = Integer.parseInt(res[1]);
			final BigInteger operand = extractIntegerValue(args[0], hook);
			if (operand == null) {
				return null;
			}
			final BitvectorConstant bv = new BitvectorConstant(operand, BigInteger.valueOf(from));
			return BitvectorConstant.sign_extend(bv, BigInteger.valueOf(to - from)).getValue();
		} else if (funApp.getIdentifier().startsWith(SFO.AUXILIARY_FUNCTION_PREFIX + BvOp.zero_extend)) {
			// remove the `~sign_extendFrom` it remains a string of the form aTob, where a
			// and b are natural numbers in a decimal representation
			final String range = funApp.getIdentifier().substring(16);
			final String[] res = range.split("To");
			if (res.length != 2) {
				throw new AssertionError();
			}
			final int from = Integer.parseInt(res[0]);
			final int to = Integer.parseInt(res[1]);
			final BigInteger operand = extractIntegerValue(args[0], hook);
			if (operand == null) {
				return null;
			}
			final BitvectorConstant bv = new BitvectorConstant(operand, BigInteger.valueOf(from));
			return BitvectorConstant.zero_extend(bv, BigInteger.valueOf(to - from)).getValue();
		}

		final BvOp sbo = getBitvectorSmtFunctionNameFromCFunctionName(funApp.getIdentifier());
		if (sbo == null) {
			// not a bitvector function
			return null;
		}
		if (sbo.isBoolean()) {
			throw new AssertionError("Unexpected boolean bitvector op");
		}
		switch (sbo) {
		case sign_extend:
		case zero_extend:
		case extract:
			throw new UnsupportedOperationException(sbo.name() + " not yet supported but can be implemented");
		default:
			final int index = getBitvectorIndexFromCFunctionName(funApp.getIdentifier());
			if (index == -1) {
				return null;
			}
			final BitvectorConstant[] operands = new BitvectorConstant[sbo.getArity()];
			for (int i = 0; i < args.length; ++i) {
				final BigInteger arg = extractIntegerValue(args[i], hook);
				if (arg == null) {
					return null;
				}
				operands[i] = new BitvectorConstant(arg, BigInteger.valueOf(index));
			}
			final BitvectorConstantOperationResult result = BitvectorConstant.apply(sbo, operands);
			if (result.isBoolean()) {
				throw new AssertionError("Need bitvector result");
			}
			return result.getBvResult().getValue();
		}
	}

	private Boolean extractBooleanValueFromBitvectorFunctionApplication(final Expression expr, final IASTNode hook) {
		final FunctionApplication funApp = (FunctionApplication) expr;
		final Expression[] args = funApp.getArguments();

		final BvOp sbo = getBitvectorSmtFunctionNameFromCFunctionName(funApp.getIdentifier());
		if (sbo == null) {
			// not a bitvector function
			return null;
		}
		if (!sbo.isBoolean()) {
			throw new AssertionError("Expected boolean bitvector op");
		}
		final int index = getBitvectorIndexFromCFunctionName(funApp.getIdentifier());
		if (index == -1) {
			return null;
		}
		final BitvectorConstant[] operands = new BitvectorConstant[sbo.getArity()];
		for (int i = 0; i < args.length; ++i) {
			final BigInteger arg = extractIntegerValue(args[i], hook);
			if (arg == null) {
				return null;
			}
			operands[i] = new BitvectorConstant(arg, BigInteger.valueOf(index));
		}
		final BitvectorConstantOperationResult result = BitvectorConstant.apply(sbo, operands);
		if (!result.isBoolean()) {
			throw new AssertionError("Need Boolean result");
		}
		return result.getBooleanResult();

	}

	private BigInteger extractIntegerValueFromIntegerLiteral(final Expression expr) {
		final BigInteger value = new BigInteger(((IntegerLiteral) expr).getValue());
		// TODO Matthias 20221119: Questionable to do apply modulo only for unsigned.
//		if (isUnsigned((CPrimitive) cType)) {
//			final BigInteger maxValue = getMaxValueOfPrimitiveType((CPrimitive) cType);
//			final BigInteger maxValuePlusOne = maxValue.add(BigInteger.ONE);
//			return value.mod(maxValuePlusOne);
//		}
		return value;
	}

	private BigInteger extractIntegerValueFromIfThenElseExpression(final Expression expr, final IASTNode hook) {
		final IfThenElseExpression ifThenElseExpr = (IfThenElseExpression) expr;
		final Boolean condValue = extractBooleanValue(ifThenElseExpr.getCondition(), hook);
		if (condValue != null) {
			if (condValue) {
				return extractIntegerValue(ifThenElseExpr.getThenPart(), hook);
			} else {
				return extractIntegerValue(ifThenElseExpr.getElsePart(), hook);
			}
		}
		return null;
	}

	private BigInteger extractIntegerValueFromBinaryExpression(final BinaryExpression expr, final IASTNode hook) {
		final BigInteger leftValue = extractIntegerValue(expr.getLeft(), hook);
		final BigInteger rightValue = extractIntegerValue(expr.getRight(), hook);
		if (leftValue == null || rightValue == null) {
			return null;
		}
		switch (expr.getOperator()) {
		case ARITHDIV:
			// TODO Matthias 20221119: Division in C may differ from division in Java
			return leftValue.divide(rightValue);
		case ARITHMINUS:
			return leftValue.subtract(rightValue);
		case ARITHMOD:
			// TODO Matthias 20221119: Modulo in C differs from division in Java
			return leftValue.mod(rightValue);
		case ARITHMUL:
			return leftValue.multiply(rightValue);
		case ARITHPLUS:
			return leftValue.add(rightValue);
		case BITVECCONCAT:
			throw new UnsupportedOperationException("BITVECCONCAT not yet supported but can be implemented");
		case COMPEQ:
		case COMPGEQ:
		case COMPGT:
		case COMPLEQ:
		case COMPLT:
		case COMPNEQ:
		case COMPPO:
		case LOGICAND:
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICOR:
			throw new AssertionError("Does not have integer return type: " + expr.getOperator());
		default:
			throw new AssertionError("Unknown operator:" + expr.getOperator());
		}
	}

	private BigInteger extractIntegerValueFromBitvectorLiteral(final BitvecLiteral expr) {
		final BigInteger value = new BigInteger(expr.getValue());
//		if (isUnsigned((CPrimitive) cType)) {
//			if (value.signum() < 0) {
//				throw new UnsupportedOperationException("negative value");
//			}
//			return value;
//		}
		return value;
	}

	private BigInteger extractIntegerValueFromIdentifierExpression(final IdentifierExpression expr,
			final IASTNode hook) {
		// An IdentifierExpression may be an alias for an integer value, this is stored
		// in the symbol table.
		final String bId = expr.getIdentifier();
		final String cId = mSymboltable.getCIdForBoogieId(bId);
		final SymbolTableValue stv = mSymboltable.findCSymbol(hook, cId);
		if (stv != null && stv.hasConstantValue()) {
			return extractIntegerValue(stv.getConstantValue(), hook);
		} else {
			return null;
		}
	}

	/**
	 * Takes an expression and returns its boolean value, if possible. Returns null
	 * otherwise.
	 */
	private Boolean extractBooleanValue(final Expression expr, final IASTNode hook) {
		if (expr instanceof BooleanLiteral) {
			return extractBooleanValueFromBooleanLiteral(expr);
		} else if (expr instanceof BinaryExpression) {
			return extractBooleanValueFromBinaryExpression((BinaryExpression) expr, hook);
		} else if (expr instanceof FunctionApplication) {
			return extractBooleanValueFromBitvectorFunctionApplication(expr, hook);
		} else {
			throw new AssertionError("Unknown Expression " + expr.getClass().getSimpleName());
		}

	}

	private Boolean extractBooleanValueFromBinaryExpression(final BinaryExpression expr, final IASTNode hook) {
		switch (expr.getOperator()) {
		case ARITHDIV:
		case ARITHMINUS:
		case ARITHMOD:
		case ARITHMUL:
		case ARITHPLUS:
		case BITVECCONCAT:
			throw new AssertionError("Not a operation with Boolean return type");
		case COMPEQ:
		case COMPGEQ:
		case COMPGT:
		case COMPLEQ:
		case COMPLT:
		case COMPNEQ: {
			final BigInteger leftValue = extractIntegerValue(expr.getLeft(), hook);
			final BigInteger rightValue = extractIntegerValue(expr.getRight(), hook);
			if (leftValue == null || rightValue == null) {
				return null;
			}
			switch (expr.getOperator()) {
			case COMPEQ:
				return leftValue.compareTo(rightValue) == 0;
			case COMPNEQ:
				return leftValue.compareTo(rightValue) != 0;
			case COMPLT:
				return leftValue.compareTo(rightValue) < 0;
			case COMPGT:
				return leftValue.compareTo(rightValue) > 0;
			case COMPLEQ:
				return leftValue.compareTo(rightValue) <= 0;
			case COMPGEQ:
				return leftValue.compareTo(rightValue) >= 0;
			default:
				throw new AssertionError();
			}
		}
		case COMPPO:
			throw new AssertionError("We do not use COMPPO in our C translation");
		case LOGICAND:
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICOR: {
			final Boolean leftValue = extractBooleanValue(expr.getLeft(), hook);
			final Boolean rightValue = extractBooleanValue(expr.getRight(), hook);
			if (leftValue == null || rightValue == null) {
				return null;
			}
			switch (expr.getOperator()) {
			case LOGICAND:
				return leftValue && rightValue;
			case LOGICIFF:
				return leftValue.equals(rightValue);
			case LOGICIMPLIES:
				return !leftValue || rightValue;
			case LOGICOR:
				return leftValue || rightValue;
			default:
				throw new AssertionError();
			}

		}
		default:
			throw new AssertionError("Unknown operator:" + expr.getOperator());
		}

	}

	private Boolean extractBooleanValueFromBooleanLiteral(final Expression expr) {
		return Boolean.valueOf((((BooleanLiteral) expr).getValue()));
	}

	private static BvOp getBitvectorSmtFunctionNameFromCFunctionName(final String name) {
		final String funName = name.substring(1).replaceAll("\\d+", "");
		try {
			return BitvectorConstant.BvOp.valueOf(funName);
		} catch (final IllegalArgumentException iae) {
			return null;
		}
	}

	private static int getBitvectorIndexFromCFunctionName(final String name) {
		try {
			return Integer.parseInt(name.substring(1).replaceAll("[^0-9]", ""));
		} catch (final NumberFormatException ex) {
			return -1;
		}
	}

	/**
	 * The size of a real floating point type is defined by a significant and an
	 * exponent.
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
