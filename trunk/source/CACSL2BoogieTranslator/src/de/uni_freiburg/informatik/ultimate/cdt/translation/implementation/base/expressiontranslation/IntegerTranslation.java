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
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CExpressionTranslator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BitvectorConstant.BvOp;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Thomas Lang
 *
 */
public class IntegerTranslation extends ExpressionTranslation {
	private static final String NOT_IMPLEMENTED = "Operation is not yet implemented in non-bitprecise translation.";

	private final BitabsTranslation mBitabsTranslation;

	public IntegerTranslation(final TypeSizes typeSizeConstants, final TranslationSettings settings,
			final ITypeHandler typeHandler, final FlatSymbolTable symboltable) {
		super(typeSizeConstants, settings, typeHandler, symboltable);
		mBitabsTranslation = new BitabsTranslation(typeSizeConstants);
	}

	@Override
	public RValue translateIntegerLiteral(final ILocation loc, final String val) {
		return ISOIEC9899TC3.handleIntegerConstant(val, loc, false, mTypeSizes);
	}

	@Override
	public Expression constructLiteralForIntegerType(final ILocation loc, final CPrimitive type,
			final BigInteger value) {
		return ISOIEC9899TC3.constructLiteralForCIntegerLiteral(loc, false, mTypeSizes, type, value);
	}

	@Override
	public Expression constructLiteralForFloatingType(final ILocation loc, final CPrimitive type,
			final BigDecimal value) {
		return ExpressionFactory.createRealLiteral(loc, value.toString());
	}

	@Override
	public Expression constructBinaryComparisonIntegerExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		if (!type1.equals(type2)) {
			throw new IllegalArgumentException("incompatible types " + type1 + " and " + type2);
		}
		final Pair<Expression, Expression> wrapped = applyWraparoundsIfNecessary(loc, exp1, type1, exp2, type2);
		return constructBinaryComparison(loc, nodeOperator, wrapped.getFirst(), wrapped.getSecond());
	}

	private static Expression constructBinaryComparison(final ILocation loc, final int nodeOperator,
			final Expression leftExpr, final Expression rightExpr) {
		Operator op;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_equals:
			op = Operator.COMPEQ;
			break;
		case IASTBinaryExpression.op_greaterEqual:
			op = Operator.COMPGEQ;
			break;
		case IASTBinaryExpression.op_greaterThan:
			op = Operator.COMPGT;
			break;
		case IASTBinaryExpression.op_lessEqual:
			op = Operator.COMPLEQ;
			break;
		case IASTBinaryExpression.op_lessThan:
			op = Operator.COMPLT;
			break;
		case IASTBinaryExpression.op_notequals:
			op = Operator.COMPNEQ;
			break;
		default:
			throw new AssertionError("Unknown BinaryExpression operator " + nodeOperator);
		}
		return ExpressionFactory.newBinaryExpression(loc, op, leftExpr, rightExpr);
	}

	@Override
	public Expression applyWraparound(final ILocation loc, final CPrimitive cPrimitive, final Expression operand) {
		if (cPrimitive.getGeneralType() == CPrimitiveCategory.INTTYPE) {
			if (mTypeSizes.isUnsigned(cPrimitive)) {
				final BigInteger maxValuePlusOne =
						mTypeSizes.getMaxValueOfPrimitiveType(cPrimitive).add(BigInteger.ONE);
				return applyEucledeanModulo(loc, operand, maxValuePlusOne);
			}
			throw new AssertionError("wraparound only for unsigned types");
		}
		throw new AssertionError("wraparound only for integer types");
	}

	private static Expression applyEucledeanModulo(final ILocation loc, final Expression operand,
			final BigInteger divisor) {
		return ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMOD, operand,
				ExpressionFactory.createIntegerLiteral(loc, divisor.toString()));
	}

	@Override
	protected ExpressionResult handleBinaryBitwiseIntegerExpression(final ILocation loc, final int op,
			final Expression left, final CPrimitive typeLeft, final Expression right, final CPrimitive typeRight,
			final AuxVarInfoBuilder auxVarInfoBuilder) {
		switch (op) {
		case IASTBinaryExpression.op_binaryAnd:
		case IASTBinaryExpression.op_binaryAndAssign:
			return mBitabsTranslation.abstractAnd(loc, left, right, typeLeft, auxVarInfoBuilder);
		case IASTBinaryExpression.op_binaryOr:
		case IASTBinaryExpression.op_binaryOrAssign:
			return mBitabsTranslation.abstractOr(loc, left, right, typeLeft, auxVarInfoBuilder);
		case IASTBinaryExpression.op_binaryXor:
		case IASTBinaryExpression.op_binaryXorAssign:
			return mBitabsTranslation.abstractXor(loc, left, right, typeLeft, auxVarInfoBuilder);
		case IASTBinaryExpression.op_shiftLeft:
		case IASTBinaryExpression.op_shiftLeftAssign:
			return handleLeftShift(loc, left, typeLeft, right, typeRight, auxVarInfoBuilder);
		case IASTBinaryExpression.op_shiftRight:
		case IASTBinaryExpression.op_shiftRightAssign:
			return mBitabsTranslation.abstractRightShift(loc, left, typeLeft, right, typeRight, auxVarInfoBuilder);
		default:
			throw new UnsupportedSyntaxException(loc, "Unknown or unsupported bitwise expression");
		}
	}

	private ExpressionResult handleLeftShift(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final AuxVarInfoBuilder auxVarInfoBuilder) {
		final ExpressionResult result =
				mBitabsTranslation.abstractLeftShift(loc, left, typeLeft, right, typeRight, auxVarInfoBuilder);
		if (!mSettings.checkSignedIntegerBounds() || !typeLeft.isIntegerType() || mTypeSizes.isUnsigned(typeLeft)) {
			return result;
		}
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		// We need to add the trivial overflow check (one of the arguments is negative or rhs is too big for the type)
		// before the actual result to avoid overapproximations.
		CExpressionTranslator.addOverflowAssertion(loc,
				constructOverflowCheckForLeftShift(loc, left, typeLeft, typeRight, right), builder);
		final Expression expr = result.getLrValue().getValue();
		builder.addAllIncludingLrValue(result);
		CExpressionTranslator.addOverflowAssertion(loc, constructBiggerMinIntExpression(loc, typeLeft, expr), builder);
		CExpressionTranslator.addOverflowAssertion(loc, constructSmallerMaxIntExpression(loc, typeLeft, expr), builder);
		return builder.build();
	}

	@Override
	protected Expression constructUnaryIntegerExpression(final ILocation loc, final int op, final Expression expr,
			final CPrimitive type) {
		switch (op) {
		case IASTUnaryExpression.op_tilde:
			return constructUnaryComplementExpression(loc, expr, type);
		case IASTUnaryExpression.op_minus:
			return constructUnaryMinusExpression(loc, expr, type);
		default:
			throw new UnsupportedSyntaxException(loc, "Unknown or unsupported bitwise expression");
		}
	}

	private Expression constructUnaryComplementExpression(final ILocation loc, final Expression expr,
			final CPrimitive type) {
		// Transform ~x to -1-x or MAX_VALUE-x (for unsigned, we could also return the same)
		final String subtrahendValue =
				mTypeSizes.isUnsigned(type) ? mTypeSizes.getMaxValueOfPrimitiveType(type).toString() : "-1";
		final Expression subtrahend = ExpressionFactory.createIntegerLiteral(loc, subtrahendValue);
		return ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMINUS, subtrahend, expr);
	}

	private static Expression constructUnaryMinusExpression(final ILocation loc, final Expression expr,
			final CPrimitive type) {
		if (type.getGeneralType() == CPrimitiveCategory.INTTYPE
				|| type.getGeneralType() == CPrimitiveCategory.FLOATTYPE) {
			return ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.ARITHNEGATIVE, expr);
		}
		throw new IllegalArgumentException("Unsupported type for unary minus: " + type);
	}

	@Override
	public Expression constructArithmeticIntegerExpression(final ILocation loc, final int nodeOperator,
			final Expression leftExp, final CPrimitive leftType, final Expression rightExp,
			final CPrimitive rightType) {
		assert leftType.getGeneralType() == CPrimitiveCategory.INTTYPE;
		assert rightType.getGeneralType() == CPrimitiveCategory.INTTYPE;

		switch (nodeOperator) {
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_minus:
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_multiply:
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_plus:
			return constructArithmeticExpression(loc, nodeOperator, leftExp, rightExp);
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_divide: {
			final var pair = applyWraparoundsIfNecessary(loc, leftExp, leftType, rightExp, rightType);
			return constructDivExpression(loc, pair.getFirst(), pair.getSecond(), leftType, rightType);
		}
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_modulo: {
			final var pair = applyWraparoundsIfNecessary(loc, leftExp, leftType, rightExp, rightType);
			return constructModExpression(loc, pair.getFirst(), pair.getSecond(), leftType, rightType);
		}
		default:
			throw new UnsupportedSyntaxException(loc, "Unknown or unsupported arithmetic expression");
		}
	}

	private Pair<Expression, Expression> applyWraparoundsIfNecessary(final ILocation loc, final Expression left,
			final CPrimitive leftType, final Expression right, final CPrimitive rightType) {
		if (mTypeSizes.isUnsigned(leftType)) {
			assert mTypeSizes.isUnsigned(rightType) : "incompatible types";
			// Apply wraparound to ensure that Nutz transformation is sound
			return new Pair<>(applyWraparound(loc, leftType, left), applyWraparound(loc, rightType, right));
		}
		return new Pair<>(left, right);
	}

	private Expression constructDivExpression(final ILocation loc, final Expression left, final Expression right,
			final CPrimitive leftType, final CPrimitive rightType) {
		final BigInteger leftValue = mTypeSizes.extractIntegerValue(left, leftType);
		final BigInteger rightValue = mTypeSizes.extractIntegerValue(right, rightType);
		if ((leftValue != null && leftValue.signum() == 0) || BigInteger.ONE.equals(rightValue)) {
			return left;
		}
		if (leftValue != null && rightValue != null) {
			return ExpressionFactory.createIntegerLiteral(loc, leftValue.divide(rightValue).toString());
		}
		final Expression normalDivision = ExpressionFactory.newBinaryExpression(loc, Operator.ARITHDIV, left, right);
		if (mTypeSizes.isUnsigned(leftType) || (leftValue != null && leftValue.signum() > 0)) {
			return normalDivision;
		}
		/*
		 * In C the semantics of integer division is "rounding towards zero". In Boogie euclidian division is used. We
		 * translate a / b into (a < 0 && a%b != 0) ? ( (b < 0) ? (a/b)+1 : (a/b)-1) : a/b
		 */
		final Expression rightSmallerZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, right,
				ExpressionFactory.createIntegerLiteral(loc, SFO.NR0));
		final Expression one = ExpressionFactory.createIntegerLiteral(loc, SFO.NR1);
		final Expression roundTowardsZero = ExpressionFactory.constructIfThenElseExpression(loc, rightSmallerZero,
				ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMINUS, normalDivision, one),
				ExpressionFactory.newBinaryExpression(loc, Operator.ARITHPLUS, normalDivision, one));
		if (leftValue != null) {
			return roundTowardsZero;
		}
		return ExpressionFactory.constructIfThenElseExpression(loc,
				getLeftSmallerZeroAndThereIsRemainder(loc, left, right), roundTowardsZero, normalDivision);
	}

	private Expression constructModExpression(final ILocation loc, final Expression left, final Expression right,
			final CPrimitive leftType, final CPrimitive rightType) {
		final BigInteger leftValue = mTypeSizes.extractIntegerValue(left, leftType);
		if (leftValue != null && leftValue.signum() == 0) {
			return left;
		}
		final BigInteger rightValue = mTypeSizes.extractIntegerValue(right, rightType);
		if (BigInteger.ONE.equals(rightValue)) {
			return ExpressionFactory.createIntegerLiteral(loc, SFO.NR0);
		}
		// modulo on bigInteger does not seem to follow the "multiply, add, and get the result back"-rule, together with
		// its division..
		if (leftValue != null && rightValue != null) {
			final String constantResult;
			if (rightValue.signum() == 0) {
				constantResult = SFO.NR0;
			} else {
				final BigInteger bigIntegerResult = leftValue.abs().mod(rightValue.abs());
				constantResult = (leftValue.signum() >= 0 ? bigIntegerResult : bigIntegerResult.negate()).toString();
			}
			return ExpressionFactory.createIntegerLiteral(loc, constantResult);
		}
		final Expression normalModulo = ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMOD, left, right);
		if (mTypeSizes.isUnsigned(leftType) || (leftValue != null && leftValue.signum() > 0)) {
			return normalModulo;
		}
		/*
		 * In C the semantics of integer division is "rounding towards zero". In Boogie euclidian division is used. We
		 * translate a % b into (a < 0 && a%b != 0) ? ( (b < 0) ? (a%b)-b : (a%b)+b) : a%b
		 */
		final Expression rightSmallerZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, right,
				ExpressionFactory.createIntegerLiteral(loc, SFO.NR0));
		final Expression roundTowardsZero = ExpressionFactory.constructIfThenElseExpression(loc, rightSmallerZero,
				ExpressionFactory.newBinaryExpression(loc, Operator.ARITHPLUS, normalModulo, right),
				ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMINUS, normalModulo, right));
		if (leftValue != null) {
			return roundTowardsZero;
		}
		return ExpressionFactory.constructIfThenElseExpression(loc,
				getLeftSmallerZeroAndThereIsRemainder(loc, left, right), roundTowardsZero, normalModulo);
	}

	private static Expression getLeftSmallerZeroAndThereIsRemainder(final ILocation loc, final Expression exp1,
			final Expression exp2) {
		final Expression leftModRight = ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMOD, exp1, exp2);
		final Expression thereIsRemainder = ExpressionFactory.newBinaryExpression(loc, Operator.COMPNEQ, leftModRight,
				ExpressionFactory.createIntegerLiteral(loc, SFO.NR0));
		final Expression leftSmallerZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, exp1,
				ExpressionFactory.createIntegerLiteral(loc, SFO.NR0));
		return ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, leftSmallerZero, thereIsRemainder);
	}

	@Override
	protected ExpressionResult convertIntToIntNonBool(final ILocation loc, final ExpressionResult operand,
			final CPrimitive resultType) {
		if (resultType.isIntegerType()) {
			final Expression result = convertToIntegerType(loc, operand.getLrValue().getValue(),
					(CPrimitive) operand.getLrValue().getCType().getUnderlyingType(), resultType);
			return new ExpressionResultBuilder().addAllExceptLrValue(operand).setLrValue(new RValue(result, resultType))
					.build();
		}
		throw new UnsupportedOperationException("not yet supported: conversion to " + resultType);
	}

	private Expression convertToIntegerType(final ILocation loc, final Expression operand, final CPrimitive oldType,
			final CPrimitive resultType) {
		assert resultType.isIntegerType();
		if (!oldType.isIntegerType()) {
			throw new UnsupportedOperationException("not yet supported: conversion from " + oldType);
		}
		if (mTypeSizes.isUnsigned(resultType)) {
			if (mTypeSizes.isUnsigned(oldType)
					&& mTypeSizes.getSize(resultType.getType()) > mTypeSizes.getSize(oldType.getType())) {
				// required for sound Nutz transformation
				// (see examples/programs/regression/c/NutzTransformation03.c)
				return applyWraparound(loc, oldType, operand);
			}
			return operand;
		}
		assert !mTypeSizes.isUnsigned(resultType);
		final Expression oldWrappedIfUnsigned;
		if (mTypeSizes.isUnsigned(oldType)) {
			// required for sound Nutz transformation
			// (see examples/programs/regression/c/NutzTransformation01.c)
			oldWrappedIfUnsigned = applyWraparound(loc, oldType, operand);
		} else {
			oldWrappedIfUnsigned = operand;
		}
		if (mTypeSizes.getSize(resultType.getType()) >= mTypeSizes.getSize(oldType.getType())
				&& !mTypeSizes.isUnsigned(oldType)) {
			return oldWrappedIfUnsigned;
		}
		// According to C11 6.3.1.3.3 the result is implementation-defined
		// it the value cannot be represented by the new type
		// We have chosen an implementation that is similar to
		// taking the lowest bits in a two's complement representation:
		// First we take the value modulo the cardinality of the
		// data range (which is 2*(MAX_VALUE+1) for signed )
		// If the number is strictly larger than MAX_VALUE we
		// subtract the cardinality of the data range.
		final CPrimitive correspondingUnsignedType = mTypeSizes.getCorrespondingUnsignedType(resultType);
		final Expression wrapped = applyWraparound(loc, correspondingUnsignedType, oldWrappedIfUnsigned);
		final Expression maxValue = mTypeSizes.constructLiteralForIntegerType(loc, oldType,
				mTypeSizes.getMaxValueOfPrimitiveType(resultType));
		final Expression condition = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, wrapped, maxValue);
		final Expression range = mTypeSizes.constructLiteralForIntegerType(loc, oldType,
				mTypeSizes.getMaxValueOfPrimitiveType(correspondingUnsignedType).add(BigInteger.ONE));
		return ExpressionFactory.constructIfThenElseExpression(loc, condition, wrapped,
				ExpressionFactory.newBinaryExpression(loc, Operator.ARITHMINUS, wrapped, range));
	}

	@Override
	public CPrimitive getCTypeOfPointerComponents() {
		return new CPrimitive(CPrimitives.LONG);
	}

	@Override
	public void addAssumeValueInRangeStatements(final ILocation loc, final Expression expr, final CType cType,
			final ExpressionResultBuilder expressionResultBuilder) {
		if (!mSettings.assumeNondeterministicValuesInRange() || !cType.getUnderlyingType().isIntegerType()) {
			// only integer types can be out of range
			return;
		}
		final CPrimitive cPrimitive = (CPrimitive) CEnum.replaceEnumWithInt(cType.getUnderlyingType());
		if (mTypeSizes.isUnsigned(cPrimitive)) {
			// only signed types can be out of range
			return;
		}
		expressionResultBuilder.addStatement(constructAssumeInRangeStatement(mTypeSizes, loc, expr, cPrimitive));
	}

	/**
	 * Returns "assume (minValue <= lrValue && lrValue <= maxValue)"
	 */
	private AssumeStatement constructAssumeInRangeStatement(final TypeSizes typeSizes, final ILocation loc,
			final Expression expr, final CPrimitive type) {
		final Expression minValue =
				mTypeSizes.constructLiteralForIntegerType(loc, type, typeSizes.getMinValueOfPrimitiveType(type));
		final Expression maxValue =
				mTypeSizes.constructLiteralForIntegerType(loc, type, typeSizes.getMaxValueOfPrimitiveType(type));

		final Expression biggerMinInt =
				constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, minValue, type, expr, type);
		final Expression smallerMaxValue =
				constructBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, expr, type, maxValue, type);
		return new AssumeStatement(loc,
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, biggerMinInt, smallerMaxValue));
	}

	@Override
	public Expression extractBits(final ILocation loc, final Expression operand, final int high, final int low) {
		// we probably also have to provide information if input is signed/unsigned
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression concatBits(final ILocation loc, final List<Expression> dataChunks, final int size) {
		// we probably also have to provide information if input is signed/unsigned
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression signExtend(final ILocation loc, final Expression operand, final int bitsBefore,
			final int bitsAfter) {
		// we probably also have to provide information if input is signed/unsigned
		throw new UnsupportedOperationException(NOT_IMPLEMENTED);
	}

	@Override
	public Expression constructBinaryComparisonFloatingPointExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		if (mSettings.overapproximateFloatingPointOperations()) {
			final String functionName = "someBinary" + type1.toString() + "ComparisonOperation";
			final String prefixedFunctionName = "~" + functionName;
			if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
				final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
						new Expression[] { ExpressionFactory.createStringLiteral(loc, functionName) });
				final Attribute[] attributes = { attribute };
				final ASTType paramAstType = mTypeHandler.cType2AstType(loc, type1);
				final ASTType resultAstType = new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL);
				mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultAstType,
						paramAstType, paramAstType);
			}
			return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
					new Expression[] { exp1, exp2 }, BoogieType.TYPE_BOOL);
		}
		return constructBinaryComparison(loc, nodeOperator, exp1, exp2);
	}

	@Override
	protected Expression constructUnaryFloatingPointExpression(final ILocation loc, final int nodeOperator,
			final Expression exp, final CPrimitive type) {
		if (mSettings.overapproximateFloatingPointOperations()) {
			final String functionName = "someUnary" + type.toString() + "operation";
			final String prefixedFunctionName = "~" + functionName;
			if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
				final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
						new Expression[] { ExpressionFactory.createStringLiteral(loc, functionName) });
				final Attribute[] attributes = { attribute };
				final ASTType astType = mTypeHandler.cType2AstType(loc, type);
				mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, astType, astType);
			}
			return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName, new Expression[] { exp },
					mTypeHandler.getBoogieTypeForCType(type));
		}
		return constructUnaryMinusExpression(loc, exp, type);
	}

	@Override
	protected Expression constructArithmeticFloatingPointExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CPrimitive type1, final Expression exp2, final CPrimitive type2) {
		if (mSettings.overapproximateFloatingPointOperations()) {
			final String functionName = "someBinaryArithmetic" + type1.toString() + "operation";
			final String prefixedFunctionName = "~" + functionName;
			if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
				final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
						new Expression[] { ExpressionFactory.createStringLiteral(loc, functionName) });
				final Attribute[] attributes = { attribute };
				final ASTType astType = mTypeHandler.cType2AstType(loc, type1);
				mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, astType, astType, astType);
			}
			return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
					new Expression[] { exp1, exp2 }, mTypeHandler.getBoogieTypeForCType(type1));
		}
		return constructArithmeticExpression(loc, nodeOperator, exp1, exp2);
	}

	private static Expression constructArithmeticExpression(final ILocation loc, final int nodeOperator,
			final Expression exp1, final Expression exp2) {
		final Operator operator;
		switch (nodeOperator) {
		case IASTBinaryExpression.op_minusAssign:
		case IASTBinaryExpression.op_minus:
			operator = Operator.ARITHMINUS;
			break;
		case IASTBinaryExpression.op_multiplyAssign:
		case IASTBinaryExpression.op_multiply:
			operator = Operator.ARITHMUL;
			break;
		case IASTBinaryExpression.op_divideAssign:
		case IASTBinaryExpression.op_divide:
			operator = Operator.ARITHDIV;
			break;
		case IASTBinaryExpression.op_moduloAssign:
		case IASTBinaryExpression.op_modulo:
			operator = Operator.ARITHMOD;
			break;
		case IASTBinaryExpression.op_plusAssign:
		case IASTBinaryExpression.op_plus:
			operator = Operator.ARITHPLUS;
			break;
		default:
			throw new UnsupportedSyntaxException(loc, "Unknown or unsupported arithmetic expression");
		}
		return ExpressionFactory.newBinaryExpression(loc, operator, exp1, exp2);
	}

	private String declareBinaryFloatComparisonOverApprox(final ILocation loc, final CPrimitive type) {
		final String functionName = "someBinary" + type.toString() + "ComparisonOperation";
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {
			final Attribute attribute = new NamedAttribute(loc, FunctionDeclarations.OVERAPPROX_IDENTIFIER,
					new Expression[] { ExpressionFactory.createStringLiteral(loc, functionName) });
			final Attribute[] attributes = { attribute };
			final ASTType paramAstType = mTypeHandler.cType2AstType(loc, type);
			final ASTType resultAstType = new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL);
			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultAstType, paramAstType,
					paramAstType);
		}
		return prefixedFunctionName;
	}

	@Override
	protected Expression constructBinaryEqualityExpressionFloating(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CType type1, final Expression exp2, final CType type2) {
		final String prefixedFunctionName = declareBinaryFloatComparisonOverApprox(loc, (CPrimitive) type1);
		if (mSettings.overapproximateFloatingPointOperations()) {
			return ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
					new Expression[] { exp1, exp2 }, BoogieType.TYPE_BOOL);
		}
		return constructEquality(loc, nodeOperator, exp1, exp2);
	}

	@Override
	protected Expression constructBinaryEqualityExpressionInteger(final ILocation loc, final int nodeOperator,
			final Expression exp1, final CType type1, final Expression exp2, final CType type2) {
		Expression leftExpr = exp1;
		Expression rightExpr = exp2;
		if (type1 instanceof CPrimitive && type2 instanceof CPrimitive) {
			final Pair<Expression, Expression> wrapped =
					applyWraparoundsIfNecessary(loc, exp1, (CPrimitive) type1, exp2, (CPrimitive) type2);
			leftExpr = wrapped.getFirst();
			rightExpr = wrapped.getSecond();
		}
		return constructEquality(loc, nodeOperator, leftExpr, rightExpr);
	}

	/**
	 * Construct either equals or not-equals relation, depending on nodeOperator.
	 */
	private static Expression constructEquality(final ILocation loc, final int nodeOperator, final Expression leftExpr,
			final Expression rightExpr) {
		if (nodeOperator == IASTBinaryExpression.op_equals) {
			return ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, leftExpr, rightExpr);
		}
		if (nodeOperator == IASTBinaryExpression.op_notequals) {
			return ExpressionFactory.newBinaryExpression(loc, Operator.COMPNEQ, leftExpr, rightExpr);
		}
		throw new IllegalArgumentException("operator is neither equals nor not equals");
	}

	@Override
	public ExpressionResult createNanOrInfinity(final ILocation loc, final String name) {
		throw new UnsupportedOperationException("createNanOrInfinity is unsupported in non-bitprecise translation");
	}

	@Override
	public Expression getCurrentRoundingMode() {
		throw new UnsupportedOperationException("getRoundingMode is unsupported in non-bitprecise translation");
	}

	@Override
	public RValue constructOtherUnaryFloatOperation(final ILocation loc, final FloatFunction floatFunction,
			final RValue argument) {
		throw new UnsupportedOperationException("floating point operation not supported in non-bitprecise translation: "
				+ floatFunction.getFunctionName());
	}

	@Override
	public RValue constructOtherBinaryFloatOperation(final ILocation loc, final FloatFunction floatFunction,
			final RValue first, final RValue second) {
		throw new UnsupportedOperationException("floating point operation not supported in non-bitprecise translation: "
				+ floatFunction.getFunctionName());
	}

	@Override
	public ExpressionResult convertFloatToFloat(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		final RValue oldRValue = (RValue) rexp.getLrValue();
		final RValue rVal = new RValue(oldRValue.getValue(), newType);
		return new ExpressionResultBuilder().addAllExceptLrValue(rexp).setLrValue(rVal).build();
	}

	@Override
	public ExpressionResult convertIntToFloat(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		return doFloatIntAndIntFloatConversion(loc, rexp, newType);
	}

	@Override
	protected ExpressionResult convertFloatToIntNonBool(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		return doFloatIntAndIntFloatConversion(loc, rexp, newType);
	}

	private ExpressionResult doFloatIntAndIntFloatConversion(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		final String prefixedFunctionName =
				declareConversionFunction(loc, (CPrimitive) rexp.getLrValue().getCType().getUnderlyingType(), newType);
		final Expression oldExpression = rexp.getLrValue().getValue();
		final Expression resultExpression = ExpressionFactory.constructFunctionApplication(loc, prefixedFunctionName,
				new Expression[] { oldExpression }, mTypeHandler.getBoogieTypeForCType(newType));
		final RValue rVal = new RValue(resultExpression, newType, false, false);
		return new ExpressionResultBuilder().addAllExceptLrValue(rexp).setLrValue(rVal).build();
	}

	private String declareConversionFunction(final ILocation loc, final CPrimitive oldType, final CPrimitive newType) {

		final String functionName = "convert" + oldType.toString() + "To" + newType.toString();
		final String prefixedFunctionName = "~" + functionName;
		if (!mFunctionDeclarations.getDeclaredFunctions().containsKey(prefixedFunctionName)) {

			final Attribute[] attributes;
			if (newType.isFloatingType()) {
				attributes =
						generateAttributes(loc, mSettings.overapproximateFloatingPointOperations(), "to_real", null);
			} else if (newType.isIntegerType()) {
				attributes =
						generateAttributes(loc, mSettings.overapproximateFloatingPointOperations(), "to_int", null);
			} else {
				throw new AssertionError("unhandled case");
			}
			final ASTType[] params = { mTypeHandler.cType2AstType(loc, oldType) };
			final ASTType resultASTType = mTypeHandler.cType2AstType(loc, newType);

			mFunctionDeclarations.declareFunction(loc, prefixedFunctionName, attributes, resultASTType, params);
		}
		return prefixedFunctionName;
	}

	@Override
	public Expression transformBitvectorToFloat(final ILocation loc, final Expression bitvector,
			final CPrimitives floatType) {
		throw new UnsupportedOperationException(
				"conversion from bitvector to float not supported in non-bitprecise translation");
	}

	@Override
	public Expression transformFloatToBitvector(final ILocation loc, final Expression value,
			final CPrimitives cprimitive) {
		throw new UnsupportedOperationException(
				"conversion from float to bitvector not supported in non-bitprecise translation");
	}

	@Override
	public Expression eraseBits(final ILocation loc, final Expression value, final CPrimitive cType,
			final int remainingWith) {
		return applyEucledeanModulo(loc, value, BigInteger.valueOf(2).pow(remainingWith));
	}

	@Override
	public void declareFloatingPointConstructors(final ILocation loc, final CPrimitive type) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void declareFloatConstant(final ILocation loc, final String smtFunctionName, final CPrimitive type) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void declareBinaryBitvectorFunctionsForAllIntegerDatatypes(final ILocation loc, final BvOp[] bvOps) {
		throw new UnsupportedOperationException();
	}

	@Override
	public RValue constructBuiltinFegetround(final ILocation loc) {
		throw new UnsupportedOperationException("fegetround not supported in non-bitprecise translation");
	}

	@Override
	public ExpressionResult constructBuiltinFesetround(final ILocation loc, final RValue arg,
			final AuxVarInfoBuilder auxVarInfoBuilder) {
		throw new UnsupportedOperationException("fesetround not supported in non-bitprecise translation");
	}

	@Override
	public Pair<Expression, Expression> constructOverflowCheckForArithmeticExpression(final ILocation loc,
			final int operation, final CPrimitive resultType, final Expression lhsOperand,
			final Expression rhsOperand) {
		assert resultType.isIntegerType()
				&& !mTypeSizes.isUnsigned(resultType) : "Overflow check only for signed integer types";
		assert List.of(IASTBinaryExpression.op_multiply, IASTBinaryExpression.op_multiplyAssign,
				IASTBinaryExpression.op_plus, IASTBinaryExpression.op_plusAssign, IASTBinaryExpression.op_minus,
				IASTBinaryExpression.op_minusAssign, IASTBinaryExpression.op_divide,
				IASTBinaryExpression.op_divideAssign).contains(operation);

		final Expression operationResult =
				constructArithmeticExpression(loc, operation, lhsOperand, resultType, rhsOperand, resultType);
		return constructOverflowCheck(loc, resultType, operationResult);
	}

	@Override
	public Pair<Expression, Expression> constructOverflowCheckForUnaryExpression(final ILocation loc,
			final int operation, final CPrimitive resultType, final Expression operand) {
		assert resultType.isIntegerType()
				&& !mTypeSizes.isUnsigned(resultType) : "Overflow check only for signed integer types";
		assert operation == IASTUnaryExpression.op_minus;

		final Expression operationResult = constructUnaryExpression(loc, operation, operand, resultType);
		return constructOverflowCheck(loc, resultType, operationResult);
	}

	private Pair<Expression, Expression> constructOverflowCheck(final ILocation loc, final CPrimitive resultType,
			final Expression operationResult) {
		final Expression largerMinInt = constructBiggerMinIntExpression(loc, resultType, operationResult);
		final Expression smallerMaxInt = constructSmallerMaxIntExpression(loc, resultType, operationResult);
		return new Pair<>(largerMinInt, smallerMaxInt);
	}

	/**
	 * Construct `expression <= maxInt`, where maxInt is the largest value of type primType.
	 */
	private Expression constructSmallerMaxIntExpression(final ILocation loc, final CPrimitive primType,
			final Expression expression) {
		return ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, expression, ExpressionFactory
				.createIntegerLiteral(loc, mTypeSizes.getMaxValueOfPrimitiveType(primType).toString()));
	}

	/**
	 * Construct `expression >= minInt`, where minInt is the smallest value of type primType.
	 */
	private Expression constructBiggerMinIntExpression(final ILocation loc, final CPrimitive primType,
			final Expression expression) {
		return ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, expression, ExpressionFactory
				.createIntegerLiteral(loc, mTypeSizes.getMinValueOfPrimitiveType(primType).toString()));
	}
}
