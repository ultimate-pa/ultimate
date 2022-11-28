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

import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
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
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Cyrus Liu (yliu195@stevens.edu)
 *
 */
public class BitabsTranslationNew {
	public static ExpressionResult abstractAnd(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final AuxVarInfoBuilder auxVarInfoBuilder) {
		// 0 & a = a & 0 = 0
		if (isZero(left)) {
			return new ExpressionResult(new RValue(left, typeLeft));
		}
		if (isZero(right)) {
			return new ExpressionResult(new RValue(right, typeRight));
		}
		// a & a = a
		if (areEqualLiterals(left, right)) {
			return new ExpressionResult(new RValue(left, typeLeft));
		}
		// TODO: Should we evaluate all combinations of constants?
		final Expression zero = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		final AuxVarInfo auxvarinfo = auxVarInfoBuilder.constructAuxVarInfo(loc, typeLeft, SFO.AUXVAR.NONDET);
		final IdentifierExpression auxvar = auxvarinfo.getExp();

		final Expression leftEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, zero);
		final Expression rightEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, right, zero);
		final Expression leftEqualsRight = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, right);

		final Expression leftNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, left, zero);
		final Expression rightNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, right, zero);

		final Expression oneNegative =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftNegative, rightNegative);
		final Expression bothNonNegative = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, left, zero),
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, right, zero));
		final Expression bothNegative =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, leftNegative, rightNegative);

		final Expression sum = ExpressionFactory.newBinaryExpression(loc, Operator.ARITHPLUS, left, right);
		final Expression oneEqualsZero =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftEqualsZero, rightEqualsZero);

		final Expression lessThanEqualBoth = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar, left),
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar, right));

		// If a >= 0 and b >= 0, then a & b <= a and a & b <= b
		final Expression maximum =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative, lessThanEqualBoth);
		// If a >= b or b >= 0, then a & b >= 0
		final Expression nonNegative = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, bothNegative,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, auxvar, zero));
		// If a < 0 or b < 0, then a & b > a + b
		final Expression greaterSum = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, bothNonNegative,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, auxvar, sum));

		// 0 & a = a & 0 = 0
		// a & a = a
		final List<Pair<Expression, Expression>> exactCases =
				List.of(new Pair<>(oneEqualsZero, zero), new Pair<>(leftEqualsRight, left));
		final List<Expression> assumptions = List.of(maximum, nonNegative, greaterSum);
		return buildExpressionResult(loc, "bitwiseAnd", typeLeft, auxvarinfo, exactCases, assumptions);
	}

	public static ExpressionResult abstractOr(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final AuxVarInfoBuilder auxVarInfoBuilder) {
		// 0 | a = a | 0 = a
		if (isZero(left)) {
			return new ExpressionResult(new RValue(right, typeRight));
		}
		if (isZero(right)) {
			return new ExpressionResult(new RValue(left, typeLeft));
		}
		// a | a = a
		if (areEqualLiterals(left, right)) {
			return new ExpressionResult(new RValue(left, typeLeft));
		}

		// TODO: Should we evaluate all combinations of constants?

		final Expression zero = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");

		final AuxVarInfo auxvarinfo = auxVarInfoBuilder.constructAuxVarInfo(loc, typeLeft, SFO.AUXVAR.NONDET);
		final IdentifierExpression auxvar = auxvarinfo.getExp();

		final Expression leftEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, zero);
		final Expression rightEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, right, zero);
		final Expression leftEqualsRight = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, right);

		final Expression leftNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, left, zero);
		final Expression rightNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, right, zero);

		final Expression oneNegative =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftNegative, rightNegative);
		final Expression bothNonNegative = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, left, zero),
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, right, zero));

		final Expression sum = ExpressionFactory.newBinaryExpression(loc, Operator.ARITHPLUS, left, right);
		final Expression leftEqualsZeroOrRight =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftEqualsZero, leftEqualsRight);
		// If a >= 0 and b >= 0, then a | b >= a and a | b >= b
		final Expression greaterEqualBoth = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, auxvar, left),
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, auxvar, right));
		final Expression minimum =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative, greaterEqualBoth);
		// Otherwise a | b < 0
		final Expression negative = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, bothNonNegative,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, auxvar, zero));
		// If a >= 0 or b >= 0, then a | b <= a + b
		final Expression leqSum = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar, sum));

		// 0 | a = a | 0 = a
		// a | a = a
		final List<Pair<Expression, Expression>> exactCases =
				List.of(new Pair<>(leftEqualsZeroOrRight, right), new Pair<>(rightEqualsZero, left));
		final List<Expression> assumptions = List.of(minimum, negative, leqSum);
		return buildExpressionResult(loc, "bitwiseOr", typeLeft, auxvarinfo, exactCases, assumptions);
	}

	public static ExpressionResult abstractXor(final ILocation loc, final Expression left, final CPrimitive typeLeft,
			final Expression right, final CPrimitive typeRight, final AuxVarInfoBuilder auxVarInfoBuilder) {
		// 0 ^ a = a ^ 0 = 0
		if (isZero(left)) {
			return new ExpressionResult(new RValue(right, typeRight));
		}
		if (isZero(right)) {
			return new ExpressionResult(new RValue(left, typeLeft));
		}
		// a ^ a = 0
		final Expression zero = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		if (areEqualLiterals(left, right)) {
			return new ExpressionResult(new RValue(zero, typeLeft));
		}

		// TODO: Should we evaluate all combinations of constants?
		final AuxVarInfo auxvarinfo = auxVarInfoBuilder.constructAuxVarInfo(loc, typeLeft, SFO.AUXVAR.NONDET);
		final IdentifierExpression auxvar = auxvarinfo.getExp();

		final Expression leftEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, zero);
		final Expression rightEqualsZero = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, right, zero);
		final Expression leftEqualsRight = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, left, right);

		final Expression leftNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, left, zero);
		final Expression rightNegative = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT, right, zero);

		final Expression oneNegative =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, leftNegative, rightNegative);

		final Expression sum = ExpressionFactory.newBinaryExpression(loc, Operator.ARITHPLUS, left, right);

		final Expression positive = ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, auxvar, zero);
		final Expression onePositive = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, left, zero),
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, right, zero));

		// If a and b have the same sign (i.e. both are positive or both are negative), then a ^ b > 0
		final Expression positiveCase1 =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative, positive);
		final Expression positiveCase2 =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, onePositive, positive);
		// If a >= 0 or b >= 0, then a ^ b <= a + b
		final Expression leqSum = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, oneNegative,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPLEQ, auxvar, sum));
		// 0 ^ a = a ^ 0 = a
		// a ^ a = 0
		final List<Pair<Expression, Expression>> exactCases = List.of(new Pair<>(leftEqualsZero, right),
				new Pair<>(rightEqualsZero, left), new Pair<>(leftEqualsRight, zero));
		final List<Expression> assumptions = List.of(positiveCase1, positiveCase2, leqSum);
		return buildExpressionResult(loc, "bitwiseOr", typeLeft, auxvarinfo, exactCases, assumptions);
	}

	public static ExpressionResult abstractCompl(final ILocation loc, final Expression expr, final CPrimitive type,
			final AuxVarInfoBuilder auxVarInfoBuilder) {
		// TODO: We could add another assumption for signed integer
		// TODO: Should we evaluate this for constants?
		final AuxVarInfo auxvarinfo = auxVarInfoBuilder.constructAuxVarInfo(loc, type, SFO.AUXVAR.NONDET);
		final IdentifierExpression auxvar = auxvarinfo.getExp();

		// ~a != a
		final Expression neq = ExpressionFactory.newBinaryExpression(loc, Operator.COMPNEQ, auxvar, expr);
		// If a < 0, then ~a > 0
		final Expression zero = new IntegerLiteral(loc, BoogieType.TYPE_INT, "0");
		final Expression signum = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGEQ, expr, zero),
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPGT, auxvar, zero));
		final List<Expression> assumptions = List.of(neq, signum);
		return buildExpressionResult(loc, "bitwiseComplement", type, auxvarinfo, List.of(), assumptions);
	}

	private static boolean isZero(final Expression expr) {
		return expr instanceof IntegerLiteral && "0".equals(((IntegerLiteral) expr).getValue());
	}

	private static boolean areEqualLiterals(final Expression left, final Expression right) {
		return left instanceof IntegerLiteral && right instanceof IntegerLiteral
				&& ((IntegerLiteral) left).getValue().equals(((IntegerLiteral) right).getValue());
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
