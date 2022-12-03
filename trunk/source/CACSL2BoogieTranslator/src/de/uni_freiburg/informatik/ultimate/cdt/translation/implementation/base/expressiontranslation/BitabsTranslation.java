/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2021 Cyrus Liu (yliu195@stevens.edu)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Thomas Lang
 * Copyright (C) 2015-2022 University of Freiburg
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

import java.math.BigInteger;
import java.util.Arrays;
import java.util.List;
import java.util.function.BinaryOperator;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class is used to overapproximate bitwise operations for the integer translation.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Cyrus Liu (yliu195@stevens.edu)
 *
 */
public class BitabsTranslation {
	private final TypeSizes mTypeSizes;

	public BitabsTranslation(final TypeSizes typeSizes) {
		mTypeSizes = typeSizes;
	}

	/**
	 * Overapproximates the bitwise {@code and}. Uses the following rules to increase the precision:
	 * <li>0 & a = a & 0 = 0
	 * <li>a & a = a
	 * <li>If a >= 0 or b < 0, then a & b <= a
	 * <li>If a < 0 or b >= 0, then a & b <= b
	 * <li>If a >= b or b >= 0, then a & b >= 0
	 * <li>If a < 0 or b < 0, then a & b > a + b
	 *
	 * Additionally evaluates the operation precisely for literals.
	 */
	public ExpressionResult abstractAnd(final ILocation loc, final Expression left, final Expression right,
			final CPrimitive type, final AuxVarInfoBuilder auxVarInfoBuilder) {
		// 0 & a = a & 0 = 0
		if (isZero(left)) {
			return new ExpressionResult(new RValue(left, type));
		}
		if (isZero(right)) {
			return new ExpressionResult(new RValue(right, type));
		}
		if (left instanceof IntegerLiteral && right instanceof IntegerLiteral) {
			return handleConstants((IntegerLiteral) left, (IntegerLiteral) right, BigInteger::and, loc, type);
		}
		final Expression zero = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		final AuxVarInfo auxvarinfo = auxVarInfoBuilder.constructAuxVarInfo(loc, type, SFO.AUXVAR.NONDET);

		final Expression auxvar = applyWraparoundIfNecessary(loc, auxvarinfo.getExp(), type);
		final Expression leftWrapped = applyWraparoundIfNecessary(loc, left, type);
		final Expression rightWrapped = applyWraparoundIfNecessary(loc, right, type);

		final Expression smallerLeft =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar, leftWrapped);
		final Expression smallerRight =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar, rightWrapped);

		final List<Expression> assumptions;
		if (mTypeSizes.isUnsigned(type)) {
			assumptions = List.of(smallerLeft, smallerRight);
		} else {
			final Expression leftNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, left, zero);
			final Expression rightNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, right, zero);
			final Expression bothNonNegative = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND,
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, left, zero),
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, right, zero));
			final Expression bothNegative =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, leftNegative, rightNegative);

			final Expression sum = ExpressionFactory.newBinaryExpression(loc, Operator.ARITHPLUS, left, right);

			// If a >= 0 or b < 0, then a & b <= a
			final Expression rightNonNegative =
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, right, zero);
			final Expression smallerLeftImplication = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, leftNegative, rightNonNegative),
					smallerLeft);

			// If a < 0 or b >= 0, then a & b <= b
			final Expression leftNonNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, left, zero);
			final Expression smallerRightImplication = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, leftNonNegative, rightNegative),
					smallerRight);

			// If a >= b or b >= 0, then a & b >= 0
			final Expression nonNegative = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, bothNegative,
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, auxvar, zero));

			// If a < 0 or b < 0, then a & b > a + b
			final Expression greaterSum = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, bothNonNegative,
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, auxvar, sum));
			final BigInteger minValue = mTypeSizes.getMinValueOfPrimitiveType(type);
			final Expression greaterMinValue = ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, auxvar,
					ExpressionFactory.createIntegerLiteral(loc, minValue.toString()));
			assumptions =
					List.of(smallerLeftImplication, smallerRightImplication, nonNegative, greaterSum, greaterMinValue);
		}

		// 0 & a = a & 0 = 0
		// a & a = a
		final Expression leftEqualsZero =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, leftWrapped, zero);
		final Expression rightEqualsZero =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, rightWrapped, zero);
		final Expression leftEqualsRight =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, leftWrapped, rightWrapped);
		final Expression leftOrRightEqualsZero =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftEqualsZero, rightEqualsZero);

		final List<Pair<Expression, Expression>> exactCases =
				List.of(new Pair<>(leftOrRightEqualsZero, zero), new Pair<>(leftEqualsRight, left));
		return buildExpressionResult(loc, "bitwiseAnd", type, auxvarinfo, exactCases, assumptions);
	}

	/**
	 * Overapproximates the bitwise {@code or}. Uses the following rules to increase the precision:
	 * <li>0 | a = a | 0 = a
	 * <li>a | a = a
	 * <li>If a >= 0 or b < 0, then a | b >= b
	 * <li>If a < 0 or b >= 0, then a & b >= a
	 * <li>If a >= 0 or b >= 0, then a | b <= a + b
	 * <li>If a < 0 or b < 0, then a | b < 0
	 *
	 * Additionally evaluates the operation precisely for literals.
	 */
	public ExpressionResult abstractOr(final ILocation loc, final Expression left, final Expression right,
			final CPrimitive type, final AuxVarInfoBuilder auxVarInfoBuilder) {
		// 0 | a = a | 0 = a
		if (isZero(left)) {
			return new ExpressionResult(new RValue(right, type));
		}
		if (isZero(right)) {
			return new ExpressionResult(new RValue(left, type));
		}
		if (left instanceof IntegerLiteral && right instanceof IntegerLiteral) {
			return handleConstants((IntegerLiteral) left, (IntegerLiteral) right, BigInteger::or, loc, type);
		}

		final Expression zero = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		final AuxVarInfo auxvarinfo = auxVarInfoBuilder.constructAuxVarInfo(loc, type, SFO.AUXVAR.NONDET);
		final Expression auxvar = applyWraparoundIfNecessary(loc, auxvarinfo.getExp(), type);
		final Expression leftWrapped = applyWraparoundIfNecessary(loc, left, type);
		final Expression rightWrapped = applyWraparoundIfNecessary(loc, right, type);

		final Expression greaterLeft =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, auxvar, leftWrapped);
		final Expression greaterRight =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, auxvar, rightWrapped);
		final Expression sum = applyWraparoundIfNecessary(loc,
				ExpressionFactory.newBinaryExpression(loc, Operator.ARITHPLUS, left, right), type);
		final Expression leqSum = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar, sum);

		final List<Expression> assumptions;
		if (mTypeSizes.isUnsigned(type)) {
			assumptions = List.of(greaterLeft, greaterRight, leqSum);
		} else {
			final Expression leftNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, left, zero);
			final Expression rightNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, right, zero);

			final Expression oneNegative =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftNegative, rightNegative);
			final Expression bothNonNegative = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND,
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, left, zero),
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, right, zero));

			// If a >= 0 or b < 0, then a | b >= b
			final Expression rightNonNegative =
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, right, zero);
			final Expression greaterRightImplication = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, leftNegative, rightNonNegative),
					greaterRight);

			// If a < 0 or b >= 0, then a & b >= a
			final Expression leftNonNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, left, zero);
			final Expression greaterLeftImplication = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, leftNonNegative, rightNegative),
					greaterLeft);

			// If a >= 0 or b >= 0, then a | b <= a + b
			final Expression leqSumImplication =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative, leqSum);

			// If a < 0 or b < 0, then a | b < 0
			final Expression negative = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, bothNonNegative,
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, auxvar, zero));
			final BigInteger maxValue = mTypeSizes.getMaxValueOfPrimitiveType(type);
			final Expression smallerMaxValue = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar,
					ExpressionFactory.createIntegerLiteral(loc, maxValue.toString()));
			assumptions = List.of(greaterRightImplication, greaterLeftImplication, leqSumImplication, negative,
					smallerMaxValue);
		}

		// 0 | a = a | 0 = a
		// a | a = a
		final Expression leftEqualsZero =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, leftWrapped, zero);
		final Expression rightEqualsZero =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, rightWrapped, zero);
		final Expression leftEqualsRight =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, leftWrapped, rightWrapped);
		final Expression leftEqualsZeroOrRight =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftEqualsZero, leftEqualsRight);

		final List<Pair<Expression, Expression>> exactCases =
				List.of(new Pair<>(leftEqualsZeroOrRight, right), new Pair<>(rightEqualsZero, left));
		return buildExpressionResult(loc, "bitwiseOr", type, auxvarinfo, exactCases, assumptions);
	}

	/**
	 * Overapproximates the bitwise {@code xor}. Uses the following rules to increase the precision:
	 * <li>0 ^ a = a ^ 0 = 0
	 * <li>a ^ a = 0
	 * <li>If a and b have the same sign (i.e. both are positive or both are negative), then a ^ b > 0
	 * <li>Otherwise a ^ b < 0
	 * <li>If a >= 0 or b >= 0, then a ^ b <= a + b
	 *
	 * Additionally evaluates the operation precisely for literals.
	 */
	public ExpressionResult abstractXor(final ILocation loc, final Expression left, final Expression right,
			final CPrimitive type, final AuxVarInfoBuilder auxVarInfoBuilder) {
		// 0 ^ a = a ^ 0 = 0
		if (isZero(left)) {
			return new ExpressionResult(new RValue(right, type));
		}
		if (isZero(right)) {
			return new ExpressionResult(new RValue(left, type));
		}
		if (left instanceof IntegerLiteral && right instanceof IntegerLiteral) {
			return handleConstants((IntegerLiteral) left, (IntegerLiteral) right, BigInteger::xor, loc, type);
		}

		final Expression zero = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		final AuxVarInfo auxvarinfo = auxVarInfoBuilder.constructAuxVarInfo(loc, type, SFO.AUXVAR.NONDET);
		final Expression auxvar = applyWraparoundIfNecessary(loc, auxvarinfo.getExp(), type);
		final Expression leftWrapped = applyWraparoundIfNecessary(loc, left, type);
		final Expression rightWrapped = applyWraparoundIfNecessary(loc, right, type);

		final Expression sum = applyWraparoundIfNecessary(loc,
				ExpressionFactory.newBinaryExpression(loc, Operator.ARITHPLUS, left, right), type);
		final Expression leqSum = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar, sum);

		List<Expression> assumptions;

		if (mTypeSizes.isUnsigned(type)) {
			assumptions = List.of(leqSum);
		} else {
			final Expression leftNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, left, zero);
			final Expression rightNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, right, zero);
			final Expression leftNonNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, left, zero);
			final Expression rightNonNegative =
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, right, zero);

			final Expression oneNegative =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftNegative, rightNegative);

			final Expression onePositive = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, left, zero),
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, right, zero));
			final Expression negative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, auxvar, zero);

			// If a and b have the same sign (i.e. both are positive or both are negative), then a ^ b > 0
			final Expression positive = ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, auxvar, zero);
			final Expression positiveCase1 =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative, positive);
			final Expression positiveCase2 =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, onePositive, positive);
			// Otherwise a ^ b < 0
			final Expression negativeCase1 =
					ExpressionFactory.or(loc, List.of(leftNegative, rightNonNegative, negative));
			final Expression negativeCase2 =
					ExpressionFactory.or(loc, List.of(leftNonNegative, rightNegative, negative));
			// If a >= 0 or b >= 0, then a ^ b <= a + b
			final Expression leqSumImplication =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative, leqSum);
			final BigInteger minValue = mTypeSizes.getMinValueOfPrimitiveType(type);
			final Expression greaterMinValue = ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, auxvar,
					ExpressionFactory.createIntegerLiteral(loc, minValue.toString()));
			final BigInteger maxValue = mTypeSizes.getMaxValueOfPrimitiveType(type);
			final Expression smallerMaxValue = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar,
					ExpressionFactory.createIntegerLiteral(loc, maxValue.toString()));
			assumptions = List.of(positiveCase1, positiveCase2, negativeCase1, negativeCase2, leqSumImplication,
					greaterMinValue, smallerMaxValue);
		}

		// 0 ^ a = a ^ 0 = a
		// a ^ a = 0
		final Expression leftEqualsZero =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, leftWrapped, zero);
		final Expression rightEqualsZero =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, rightWrapped, zero);
		final Expression leftEqualsRight =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, leftWrapped, rightWrapped);
		final List<Pair<Expression, Expression>> exactCases = List.of(new Pair<>(leftEqualsZero, right),
				new Pair<>(rightEqualsZero, left), new Pair<>(leftEqualsRight, zero));
		return buildExpressionResult(loc, "bitwiseOr", type, auxvarinfo, exactCases, assumptions);
	}

	/**
	 * Overapproximates the bitwise left-shift. Uses the following rules to increase the precision:
	 * <li>If a=0 or b=0, then a<<b = a
	 * <li>Otherwise a<<b > a
	 * <li>In general a<<b = a * 2**b, therefore we return this expression if b is a constant.
	 */
	public ExpressionResult abstractLeftShift(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final AuxVarInfoBuilder auxVarInfoBuilder) {
		return abstractShift(loc, left, typeLeft, right, typeRight, auxVarInfoBuilder, "shiftLeft", Operator.ARITHMUL,
				Operator.COMPGT);
	}

	/**
	 * Overapproximates the bitwise right-shift. Uses the following rules to increase the precision:
	 * <li>If a=0 or b=0, then a>>b = a
	 * <li>Otherwise a>>b < a
	 * <li>In general a>>b = a / 2**b, therefore we return this expression if b is a constant.
	 */
	public ExpressionResult abstractRightShift(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final AuxVarInfoBuilder auxVarInfoBuilder) {
		return abstractShift(loc, left, typeLeft, right, typeRight, auxVarInfoBuilder, "shiftRight", Operator.ARITHDIV,
				Operator.COMPLT);
	}

	public ExpressionResult abstractShift(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final AuxVarInfoBuilder auxVarInfoBuilder,
			final String functionName, final Operator shiftOperator, final Operator compOperator) {
		if (isZero(left) || isZero(right)) {
			return new ExpressionResult(new RValue(left, typeLeft));
		}
		if (right instanceof IntegerLiteral) {
			final BigInteger shiftValue = new BigInteger(((IntegerLiteral) right).getValue());
			final Expression value =
					constructShiftWithLiteralOptimization(loc, left, typeRight, shiftValue, shiftOperator);
			return new ExpressionResult(new RValue(value, typeLeft));
		}
		final AuxVarInfo auxVar = auxVarInfoBuilder.constructAuxVarInfo(loc, typeLeft, SFO.AUXVAR.NONDET);
		final Expression zero = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		final Expression leftWrapped = applyWraparoundIfNecessary(loc, left, typeLeft);
		final Expression leftEqualsZero =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, leftWrapped, zero);
		final Expression rightEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ,
				applyWraparoundIfNecessary(loc, right, typeRight), zero);
		final Expression leftOrRightEqualsZero =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftEqualsZero, rightEqualsZero);
		final Expression compLeft = ExpressionFactory.newBinaryExpression(loc, compOperator,
				applyWraparoundIfNecessary(loc, auxVar.getExp(), typeLeft), leftWrapped);
		return buildExpressionResult(loc, functionName, typeLeft, auxVar,
				List.of(new Pair<>(leftOrRightEqualsZero, left)), List.of(compLeft));
	}

	private Expression constructShiftWithLiteralOptimization(final ILocation loc, final Expression left,
			final CPrimitive typeRight, final BigInteger integerLiteralValue, final Operator op1) {
		final int exponent;
		try {
			exponent = integerLiteralValue.intValueExact();
		} catch (final ArithmeticException ae) {
			throw new UnsupportedOperationException("RHS of shift is larger than C standard allows " + ae);
		}
		final BigInteger shiftFactorBigInt = BigInteger.valueOf(2).pow(exponent);
		final Expression shiftFactorExpr = mTypeSizes.constructLiteralForIntegerType(loc, typeRight, shiftFactorBigInt);
		return ExpressionFactory.newBinaryExpression(loc, op1, left, shiftFactorExpr);
	}

	private Expression applyWraparoundIfNecessary(final ILocation loc, final Expression expr, final CPrimitive type) {
		if (!mTypeSizes.isUnsigned(type)) {
			return expr;
		}
		final BigInteger maxValuePlusOne = mTypeSizes.getMaxValueOfPrimitiveType(type).add(BigInteger.ONE);
		return ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.ARITHMOD, expr,
				ExpressionFactory.createIntegerLiteral(loc, maxValuePlusOne.toString()));
	}

	private static boolean isZero(final Expression expr) {
		return expr instanceof IntegerLiteral && "0".equals(((IntegerLiteral) expr).getValue());
	}

	private static ExpressionResult handleConstants(final IntegerLiteral left, final IntegerLiteral right,
			final BinaryOperator<BigInteger> operator, final ILocation loc, final CPrimitive type) {
		// TODO: Can we rely on the semantics for the BigInteger-operator?
		final BigInteger leftValue = new BigInteger(left.getValue());
		final BigInteger rightValue = new BigInteger(right.getValue());
		final BigInteger result = operator.apply(leftValue, rightValue);
		return new ExpressionResult(new RValue(new IntegerLiteral(loc, BoogieType.TYPE_INT, result.toString()), type));
	}

	private static ExpressionResult buildExpressionResult(final ILocation loc, final String functionName,
			final CPrimitive resultType, final AuxVarInfo auxvarinfo,
			final List<Pair<Expression, Expression>> exactCases,
			final List<Expression> assumptionsForOverapproximation) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addDeclaration(auxvarinfo.getVarDec());
		builder.addAuxVar(auxvarinfo);
		final IdentifierExpression auxvar = auxvarinfo.getExp();
		builder.setLrValue(new RValue(auxvar, resultType));
		final VariableLHS auxvarLhs = auxvarinfo.getLhs();

		final Overapprox overapprox = new Overapprox(functionName, loc);
		Statement[] resultStatements = new Statement[assumptionsForOverapproximation.size()];
		// TODO: Is it better to have the one assume with the conjunction instead of multiple assumes?
		for (int i = 0; i < assumptionsForOverapproximation.size(); i++) {
			final Statement assume = new AssumeStatement(loc, assumptionsForOverapproximation.get(i));
			overapprox.annotate(assume);
			resultStatements[i] = assume;
		}
		for (int i = exactCases.size() - 1; i >= 0; i--) {
			final Pair<Expression, Expression> pair = exactCases.get(i);
			final Statement assignment =
					StatementFactory.constructAssignmentStatement(loc, auxvarLhs, pair.getSecond());
			final Statement ifStatement = StatementFactory.constructIfStatement(loc, pair.getFirst(),
					new Statement[] { assignment }, resultStatements);
			resultStatements = new Statement[] { ifStatement };
		}
		return builder.addStatements(Arrays.asList(resultStatements)).build();
	}
}
