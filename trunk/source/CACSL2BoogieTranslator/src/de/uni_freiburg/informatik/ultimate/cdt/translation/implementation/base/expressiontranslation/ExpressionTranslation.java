/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Thomas Lang
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3.FloatingPointLiteral;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.BvOp;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public abstract class ExpressionTranslation {

	protected final FunctionDeclarations mFunctionDeclarations;
	protected final TypeSizes mTypeSizes;
	protected final ITypeHandler mTypeHandler;
	protected final IPointerIntegerConversion mPointerIntegerConversion;
	protected final FlatSymbolTable mSymboltable;

	protected final TranslationSettings mSettings;

	public ExpressionTranslation(final TypeSizes typeSizes, final TranslationSettings translationSettings,
			final ITypeHandler typeHandler, final FlatSymbolTable symboltable) {

		mSettings = translationSettings;
		mTypeSizes = typeSizes;
		mTypeHandler = typeHandler;
		mSymboltable = symboltable;
		mFunctionDeclarations = new FunctionDeclarations(mTypeHandler, mTypeSizes);

		switch (mSettings.getPointerIntegerCastMode()) {
		case IdentityAxiom:
			throw new UnsupportedOperationException("not yet implemented " + PointerIntegerConversion.IdentityAxiom);
		case NonBijectiveMapping:
			mPointerIntegerConversion = new NonBijectiveMapping(this, mTypeSizes);
			break;
		case NutzBijection:
			throw new UnsupportedOperationException("not yet implemented " + PointerIntegerConversion.NutzBijection);
		case Overapproximate:
			mPointerIntegerConversion = new OverapproximationUF(this, mFunctionDeclarations, mTypeHandler, mTypeSizes);
			break;
		default:
			throw new UnsupportedOperationException("unknown value " + mSettings.getPointerIntegerCastMode());

		}
	}

	public final Expression constructBinaryComparisonExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		// TODO: Check that types coincide
		if (type1.getGeneralType() == CPrimitiveCategory.FLOATTYPE
				|| type2.getGeneralType() == CPrimitiveCategory.FLOATTYPE) {
			return constructBinaryComparisonFloatingPointExpression(loc, nodeOperator, exp1, type1, exp2, type2);
		}
		return constructBinaryComparisonIntegerExpression(loc, nodeOperator, exp1, type1, exp2, type2);
	}

	public final ExpressionResult handleBinaryBitwiseExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2,
			final AuxVarInfoBuilder auxVarInfoBuilder) {
		// TODO: Check that types coincide
		if (type1.getGeneralType() == CPrimitiveCategory.FLOATTYPE
				|| type2.getGeneralType() == CPrimitiveCategory.FLOATTYPE) {
			throw new UnsupportedSyntaxException(LocationFactory.createIgnoreCLocation(), "we do not support floats");
		}
		return handleBinaryBitwiseIntegerExpression(loc, nodeOperator, exp1, type1, exp2, type2, auxVarInfoBuilder);
	}

	public final ExpressionResult handleBitshiftExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2,
			final AuxVarInfoBuilder auxVarInfoBuilder) {
		// TODO: Should we really throw an exception here or just report undefined behavior somehow?
		final BigInteger shiftValue = mTypeSizes.extractIntegerValue(exp2, type2);
		if (shiftValue != null) {
			if (shiftValue.signum() < 0) {
				throw new UnsupportedOperationException("Shift by negative value is not allowed (6.5.7.2)");
			}
			final BigInteger bitNumber = BigInteger.valueOf(8 * mTypeSizes.getSize(type1.getType()));
			if (shiftValue.compareTo(bitNumber) >= 0) {
				throw new UnsupportedOperationException(
						"Shift by too large value " + shiftValue + " is not allowed (6.5.7.2)");
			}
		}
		final ExpressionResult result =
				handleBinaryBitwiseIntegerExpression(loc, nodeOperator, exp1, type1, exp2, type2, auxVarInfoBuilder);
		if (!mSettings.checkSignedIntegerBounds() || !type1.isIntegerType() || mTypeSizes.isUnsigned(type1)) {
			return result;
		}
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		// TODO: Is this really a overflow or some other undefined behavior?
		CExpressionTranslator.addOverflowAssertion(loc,
				constructTypeCheckForShift(loc, exp1, type1, type2, exp2, nodeOperator), builder);
		return builder.addAllIncludingLrValue(result).build();
	}

	// TODO 20221121 Matthias: If types of LHS and RHS differ, we have to extend/reduce the RHS
	private Expression constructTypeCheckForShift(final ILocation loc, final Expression left,
			final CPrimitive resultType, final CPrimitive rhsType, final Expression right, final int operator) {
		Expression rhsNonNegative;
		{
			final Expression zero = constructLiteralForIntegerType(loc, rhsType, BigInteger.ZERO);
			rhsNonNegative = constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, zero, rhsType,
					right, rhsType);
		}
		Expression rhsSmallerBitWidth;
		{
			final BigInteger bitwidthOfLhsAsBigInt = BigInteger.valueOf(8 * mTypeSizes.getSize(resultType.getType()));
			final Expression bitwidthOfLhsAsExpr = constructLiteralForIntegerType(loc, rhsType, bitwidthOfLhsAsBigInt);
			rhsSmallerBitWidth = constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessThan, right,
					resultType, bitwidthOfLhsAsExpr, resultType);
		}
		if (operator == IASTBinaryExpression.op_shiftRight || operator == IASTBinaryExpression.op_shiftRightAssign) {
			return ExpressionFactory.and(loc, List.of(rhsNonNegative, rhsSmallerBitWidth));
		}
		Expression lhsNonNegative;
		{
			final Expression zero = constructLiteralForIntegerType(loc, resultType, BigInteger.ZERO);
			lhsNonNegative = constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, zero,
					resultType, left, resultType);
		}
		return ExpressionFactory.and(loc, List.of(lhsNonNegative, rhsNonNegative, rhsSmallerBitWidth));
	}

	public final Expression constructUnaryExpression(final ILocation loc, final int nodeOperator, final Expression exp,
			final CPrimitive type) {
		if (type.getGeneralType() == CPrimitiveCategory.FLOATTYPE) {
			return constructUnaryFloatingPointExpression(loc, nodeOperator, exp, type);
		}
		return constructUnaryIntegerExpression(loc, nodeOperator, exp, type);
	}

	public final Expression constructArithmeticExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		// TODO: Check that types coincide
		try {
			if (type1.getGeneralType() == CPrimitiveCategory.FLOATTYPE
					|| type2.getGeneralType() == CPrimitiveCategory.FLOATTYPE) {
				return constructArithmeticFloatingPointExpression(loc, nodeOperator, exp1, type1, exp2, type2);
			}
			return constructArithmeticIntegerExpression(loc, nodeOperator, exp1, type1, exp2, type2);
		} catch (final ArithmeticException ex) {
			String msg;
			if (ex.getMessage().contains("divide by zero")) {
				msg = "Division by zero";
			} else {
				msg = ex.getMessage();
			}
			throw new IncorrectSyntaxException(loc, msg);
		}
	}

	public abstract Expression constructBinaryComparisonIntegerExpression(ILocation loc, int nodeOperator,
			Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);

	protected abstract ExpressionResult handleBinaryBitwiseIntegerExpression(ILocation loc, int nodeOperator,
			Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2, AuxVarInfoBuilder auxVarInfoBuilder);

	protected abstract Expression constructUnaryIntegerExpression(ILocation loc, int nodeOperator, Expression exp,
			CPrimitive type);

	public abstract Expression constructArithmeticIntegerExpression(ILocation loc, int nodeOperator, Expression exp1,
			CPrimitive type1, Expression exp2, CPrimitive type2);

	public abstract Expression constructBinaryComparisonFloatingPointExpression(ILocation loc, int nodeOperator,
			Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);

	protected abstract Expression constructUnaryFloatingPointExpression(ILocation loc, int nodeOperator, Expression exp,
			CPrimitive type);

	protected abstract Expression constructArithmeticFloatingPointExpression(ILocation loc, int nodeOperator,
			Expression exp1, CPrimitive type1, Expression exp2, CPrimitive type2);

	public final Expression constructBinaryEqualityExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CType type1, final Expression exp2, final CType type2) {
		if (type1.isRealFloatingType() || type2.isRealFloatingType()) {
			return constructBinaryEqualityExpressionFloating(loc, nodeOperator, exp1, type1, exp2, type2);
		}
		return constructBinaryEqualityExpressionInteger(loc, nodeOperator, exp1, type1, exp2, type2);
	}

	protected abstract Expression constructBinaryEqualityExpressionFloating(ILocation loc, int nodeOperator,
			Expression exp1, CType type1, Expression exp2, CType type2);

	protected abstract Expression constructBinaryEqualityExpressionInteger(ILocation loc, int nodeOperator,
			Expression exp1, CType type1, Expression exp2, CType type2);

	public abstract RValue translateIntegerLiteral(ILocation loc, String val);

	public final RValue translateFloatingLiteral(final ILocation loc, final String val) {
		final FloatingPointLiteral fpl = ISOIEC9899TC3.handleFloatConstant(val, loc);
		final Expression expr =
				constructLiteralForFloatingType(loc, fpl.getCPrimitive(), fpl.getDecimalRepresenation());
		return new RValue(expr, fpl.getCPrimitive());
	}

	public abstract Expression constructLiteralForIntegerType(ILocation loc, CPrimitive type, BigInteger value);

	public abstract Expression constructLiteralForFloatingType(ILocation loc, CPrimitive type, BigDecimal value);

	public FunctionDeclarations getFunctionDeclarations() {
		return mFunctionDeclarations;
	}

	/**
	 * Conversion from some integer type to some integer type which is not _Bool.
	 *
	 * @return
	 */
	protected abstract ExpressionResult convertIntToIntNonBool(ILocation loc, ExpressionResult operand,
			CPrimitive resultType);

	public final ExpressionResult convertIntToInt(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		if (newType.getType() == CPrimitives.BOOL) {
			return convertToBool(loc, rexp);
		}
		return convertIntToIntNonBool(loc, rexp, newType);
	}

	/**
	 * In our Lindenmann-Hoenicke memory model, a pointer is a struct of two integer data types. This method returns the
	 * CType of the structs components.
	 */
	public abstract CPrimitive getCTypeOfPointerComponents();

	public final ExpressionResult convertPointerToInt(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		return mPointerIntegerConversion.convertPointerToInt(loc, rexp, newType);
	}

	public final ExpressionResult convertIntToPointer(final ILocation loc, final ExpressionResult rexp,
			final CPointer newType) {
		return mPointerIntegerConversion.convertIntToPointer(loc, rexp, newType);
	}

	public ExpressionResult convertFloatToInt(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		if (newType.getType() == CPrimitives.BOOL) {
			return convertToBool(loc, rexp);
		}
		return convertFloatToIntNonBool(loc, rexp, newType);
	}

	public abstract ExpressionResult convertFloatToFloat(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType);

	public abstract ExpressionResult convertIntToFloat(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType);

	protected abstract ExpressionResult convertFloatToIntNonBool(ILocation loc, ExpressionResult rexp,
			CPrimitive newType);

	public abstract void declareFloatingPointConstructors(final ILocation loc, final CPrimitive type);

	/**
	 * Convert any scalar type to _Bool. Section 6.3.1.2 of C11 says: When any scalar value is converted to _Bool, the
	 * result is 0 if the value compares equal to 0; otherwise, the result is 1.
	 */
	ExpressionResult convertToBool(final ILocation loc, final ExpressionResult expr) {
		CType underlyingType = expr.getLrValue().getCType().getUnderlyingType();
		underlyingType = CEnum.replaceEnumWithInt(underlyingType);
		final Expression zeroInputType = constructZero(loc, underlyingType);
		final Expression isZero;
		if (underlyingType instanceof CPointer) {
			isZero = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPEQ,
					expr.getLrValue().getValue(), zeroInputType);
		} else if (underlyingType instanceof CPrimitive) {
			isZero = constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_equals,
					expr.getLrValue().getValue(), (CPrimitive) underlyingType, zeroInputType,
					(CPrimitive) underlyingType);
		} else {
			throw new UnsupportedOperationException("unsupported: conversion from " + underlyingType + " to _Bool");
		}
		final Expression zeroBool =
				mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.BOOL), BigInteger.ZERO);
		final Expression oneBool =
				mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.BOOL), BigInteger.ONE);
		final Expression resultExpression =
				ExpressionFactory.constructIfThenElseExpression(loc, isZero, zeroBool, oneBool);
		final RValue rValue = new RValue(resultExpression, new CPrimitive(CPrimitives.BOOL), false, false);
		return new ExpressionResultBuilder().addAllExceptLrValue(expr).setLrValue(rValue).build();
	}

	public abstract void addAssumeValueInRangeStatements(ILocation loc, Expression expr, CType ctype,
			ExpressionResultBuilder expressionResultBuilder);

	public Expression constructNullPointer(final ILocation loc) {
		return constructPointerForIntegerValues(loc, BigInteger.ZERO, BigInteger.ZERO);
	}

	public Expression constructPointerForIntegerValues(final ILocation loc, final BigInteger baseValue,
			final BigInteger offsetValue) {
		final Expression base =
				mTypeSizes.constructLiteralForIntegerType(loc, getCTypeOfPointerComponents(), baseValue);
		final Expression offset =
				mTypeSizes.constructLiteralForIntegerType(loc, getCTypeOfPointerComponents(), offsetValue);
		return MemoryHandler.constructPointerFromBaseAndOffset(base, offset, loc);
	}

	public Expression constructZero(final ILocation loc, final CType cType) {
		final Expression result;
		if (cType instanceof CPrimitive) {
			switch (((CPrimitive) cType).getGeneralType()) {
			case FLOATTYPE:
				result = constructLiteralForFloatingType(loc, (CPrimitive) cType, BigDecimal.ZERO);
				break;
			case INTTYPE:
				result = mTypeSizes.constructLiteralForIntegerType(loc, (CPrimitive) cType, BigInteger.ZERO);
				break;
			case VOID:
				throw new UnsupportedSyntaxException(loc, "no 0 value of type VOID");
			default:
				throw new AssertionError("illegal type");
			}
		} else if (cType instanceof CPointer) {
			result = constructNullPointer(loc);
		} else {
			throw new UnsupportedSyntaxException(loc, "don't know 0 value for type " + cType);
		}
		return result;
	}

	/**
	 * Returns an {@link Expression} that represents the following bits of operand high-1, high-2, ..., low+1, low
	 * (i.e., the bit at the higher index is not included, the bit at the lower index is included).
	 */
	public abstract Expression extractBits(ILocation loc, Expression operand, int high, int low);

	/**
	 * Presume that the input represents an integer that has inputWidth bit. Set all most significant bits to zero
	 * except the remainingWith least significant bits. I.e., the result is input representation that consists only of
	 * the bits. low-1, low-2, ..., 0. If inputWidth and remainingWith are different the result is always positive.
	 */
	public abstract Expression eraseBits(final ILocation loc, final Expression value, final CPrimitive cType,
			final int remainingWith);

	public abstract Expression concatBits(ILocation loc, List<Expression> dataChunks, int size);

	public abstract Expression signExtend(ILocation loc, Expression operand, int bitsBefore, int bitsAfter);

	public abstract ExpressionResult createNanOrInfinity(ILocation loc, String name);

	public ExpressionResult createNan(final ILocation loc, final CPrimitive cPrimitive) {
		if (!cPrimitive.isFloatingType()) {
			throw new IllegalArgumentException("can only create NaN for floating types");
		}
		final String s;
		switch (cPrimitive.getType()) {
		case FLOAT: {
			s = "nanf";
			break;
		}
		case DOUBLE: {
			s = "nan";
			break;
		}
		case LONGDOUBLE: {
			s = "nanl";
			break;
		}
		default:
			throw new IllegalArgumentException("can only create NaN for floating types");
		}
		return createNanOrInfinity(loc, s);
	}

	public abstract Expression getCurrentRoundingMode();

	public abstract RValue constructOtherUnaryFloatOperation(ILocation loc, FloatFunction floatFunction,
			RValue argument);

	public abstract RValue constructOtherBinaryFloatOperation(ILocation loc, FloatFunction floatFunction, RValue first,
			RValue second);

	public abstract void declareFloatConstant(final ILocation loc, final String smtFunctionName, final CPrimitive type);

	public abstract void declareBinaryBitvectorFunctionsForAllIntegerDatatypes(final ILocation loc,
			final BvOp[] importantBvOps);

	public Expression constructOverapproximationFloatLiteral(final ILocation loc, final String val,
			final CPrimitive type) {
		final String functionName = "floatingLiteral_" + makeBoogieIdentifierSuffix(val) + "_" + type;
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
					new Expression[] { ExpressionFactory.createStringLiteral(loc, functionName) });
			final Attribute[] attributes = { attribute };
			final ASTType astType = mTypeHandler.cType2AstType(loc, type);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, astType);
		}
		return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName, new Expression[] {},
				mTypeHandler.getBoogieTypeForCType(type));

	}

	/**
	 * Translate string representation of a C literal to a string representation that is allowed in Boogie identifiers.
	 *
	 * @param val
	 *            string representation of C literal
	 * @return
	 */
	private static String makeBoogieIdentifierSuffix(final String val) {
		return val;
	}

	/**
	 * Check if id is number classification macro according to 7.12.6 of C11.
	 */
	public boolean isNumberClassificationMacro(final String cId) {
		return cId.equals("FP_NAN") || cId.equals("FP_INFINITE") || cId.equals("FP_ZERO") || cId.equals("FP_SUBNORMAL")
				|| cId.equals("FP_NORMAL");
	}

	/**
	 * Translate number classification macros according to 7.12.6 of C11. Although the standard allows any distinct
	 * integers, we take 0,1,2,3,4 because gcc on Matthias' Linux system uses these numbers.
	 */
	public RValue handleNumberClassificationMacro(final ILocation loc, final String cId) {
		final int number;
		switch (cId) {
		case "FP_NAN":
			number = 0;
			break;
		case "FP_INFINITE":
			number = 1;
			break;
		case "FP_ZERO":
			number = 2;
			break;
		case "FP_SUBNORMAL":
			number = 3;
			break;
		case "FP_NORMAL":
			number = 4;
			break;
		default:
			throw new IllegalArgumentException("no number classification macro " + cId);
		}
		final CPrimitive type = new CPrimitive(CPrimitives.INT);
		final Expression expr = mTypeSizes.constructLiteralForIntegerType(loc, type, BigInteger.valueOf(number));
		return new RValue(expr, type);
	}

	/**
	 * Generate the attributes for the Boogie code that make sure that we either - translate to the desired SMT
	 * functions, or - let Ultimate overapproximate
	 */
	protected Attribute[] generateAttributes(final ILocation loc, final boolean overapproximate,
			final String smtlibFunctionName, final int[] indices) {
		Attribute[] attributes;
		if (overapproximate) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
					new Expression[] { ExpressionFactory.createStringLiteral(loc, smtlibFunctionName) });
			attributes = new Attribute[] { attribute };
		} else if (indices == null) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.BUILTIN_IDENTIFIER,
					new Expression[] { ExpressionFactory.createStringLiteral(loc, smtlibFunctionName) });
			attributes = new Attribute[] { attribute };
		} else {
			final Expression[] literalIndices = new IntegerLiteral[indices.length];
			for (int i = 0; i < indices.length; ++i) {
				literalIndices[i] = ExpressionFactory.createIntegerLiteral(loc, String.valueOf(indices[i]));
			}
			final Attribute attribute1 = new NamedAttribute(loc, FunctionDeclarations.BUILTIN_IDENTIFIER,
					new Expression[] { ExpressionFactory.createStringLiteral(loc, smtlibFunctionName) });
			final Attribute attribute2 = new NamedAttribute(loc, FunctionDeclarations.INDEX_IDENTIFIER, literalIndices);
			attributes = new Attribute[] { attribute1, attribute2 };
		}
		return attributes;
	}

	public abstract Expression transformBitvectorToFloat(ILocation loc, Expression bitvector, CPrimitives floatType);

	public abstract Expression transformFloatToBitvector(ILocation loc, Expression value, CPrimitives cprimitive);

	public abstract RValue constructBuiltinFegetround(final ILocation loc);

	public abstract ExpressionResult constructBuiltinFesetround(final ILocation loc, final RValue arg,
			AuxVarInfoBuilder auxVarInfoBuilder);

	public abstract Expression applyWraparound(ILocation loc, CPrimitive cPrimitive, Expression operand);

	public abstract Pair<Expression, Expression> constructOverflowCheckForArithmeticExpression(ILocation loc,
			int operation, CPrimitive resultType, Expression lhsOperand, Expression rhsOperand);

	public abstract Pair<Expression, Expression> constructOverflowCheckForUnaryExpression(ILocation loc, int operation,
			CPrimitive resultType, Expression operand);
}
