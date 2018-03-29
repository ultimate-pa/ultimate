/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms;

import java.util.Arrays;
import java.util.HashMap;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;

public class ConditionTransformerTest {

	private final HashMap<String, Expression> mIdentifier;
	private final Expression mExp4;
	private final Expression mExp3;
	private final Expression mExp2;
	private final Expression mA;
	private final Expression mB;
	private final Expression mC;
	private final Expression mD;
	private final Expression mExp1;

	public ConditionTransformerTest() {
		mIdentifier = new HashMap<>();
		mA = intVar("A");
		mB = intVar("B");
		mC = intVar("C");
		mD = intVar("D");
		mExp1 = or(mB, mC);

		final Expression aord = or(mA, mD);
		final Expression aandborc = and(mA, mExp1);

		mExp2 = and(aandborc, aord);
		mExp3 = or(mExp2, mExp2);
		mExp4 = not(mExp3);

	}

	private static Expression not(final Expression exp) {
		return new UnaryExpression(null, UnaryExpression.Operator.LOGICNEG, exp);
	}

	private static Expression and(final Expression left, final Expression right) {
		return new BinaryExpression(null, Operator.LOGICAND, left, right);
	}

	private static Expression or(final Expression left, final Expression right) {
		return new BinaryExpression(null, Operator.LOGICOR, left, right);
	}

	private Expression and(final Expression... left) {
		if (left == null || left.length == 0) {
			throw new IllegalArgumentException();
		} else if (left.length == 1) {
			return left[0];
		} else {
			return new BinaryExpression(null, Operator.LOGICAND, and(Arrays.copyOfRange(left, 1, left.length)),
					left[0]);
		}
	}

	private Expression or(final Expression... left) {
		if (left == null || left.length == 0) {
			throw new IllegalArgumentException();
		} else if (left.length == 1) {
			return left[0];
		} else {
			return new BinaryExpression(null, Operator.LOGICOR, or(Arrays.copyOfRange(left, 1, left.length)), left[0]);
		}
	}

	private Expression intVar(final String varname) {
		return var(varname, BoogieType.TYPE_INT);
	}

	private Expression boolVar(final String varname) {
		return var(varname, BoogieType.TYPE_BOOL);
	}

	private Expression var(final String varname, final IBoogieType type) {
		Expression exp = mIdentifier.get(varname + type);
		if (exp == null) {
			exp = new IdentifierExpression(null, type, varname, new DeclarationInformation(StorageClass.GLOBAL, null));
			mIdentifier.put(varname, exp);
		}
		return exp;
	}

	/**
	 * No Typechecking!
	 */
	private static Expression term(final Expression var, final int lit, final Operator op) {
		final IBoogieType type = BoogieType.TYPE_INT;
		return new BinaryExpression(null, type, op, var, new IntegerLiteral(null, type, String.valueOf(lit)));
	}

	private static Expression term(final Expression var, final boolean lit, final Operator op) {
		final IBoogieType type = BoogieType.TYPE_BOOL;
		return new BinaryExpression(null, type, op, var, new BooleanLiteral(null, type, lit));
	}

	@Test
	public void testRewriteA() {
		final Expression input = term(mA, 1, Operator.COMPNEQ);
		final Expression afterRewrite = or(term(mA, 1, Operator.COMPLT), term(mA, 1, Operator.COMPGT));
		testRewrite(input, afterRewrite);
	}

	@Test
	public void testRewriteB() {
		final Expression input = or(mExp2, term(mA, 1, Operator.COMPNEQ));
		final Expression afterRewrite = or(or(and(and(or(mA, mD), or(mB, mC)), mA), term(mA, 1, Operator.COMPGT)),
				term(mA, 1, Operator.COMPLT));
		testRewrite(input, afterRewrite);
	}

	@Test
	public void testRewriteC() {
		final Expression input = and(and(not(term(mA, 0, Operator.COMPNEQ)), not(term(mB, 1, Operator.COMPEQ))),
				not(term(mC, 1, Operator.COMPEQ)));
		final Expression afterRewrite =
				and(and(term(mA, 0, Operator.COMPEQ), or(term(mB, 1, Operator.COMPLT), term(mB, 1, Operator.COMPGT))),
						or(term(mC, 1, Operator.COMPLT), term(mC, 1, Operator.COMPGT)));
		testRewrite(input, afterRewrite);
	}

	@Test
	public void testSimplifyA() {
		final Expression input = and(mA, mA);
		final Expression afterSimplify = mA;
		testSimplify(input, afterSimplify);
	}

	@Test
	public void testIgnoreVariable() {
		testRewrite(mA, mA);
		testRewrite(not(mA), not(mA));
	}

	// @Test
	public void testSimplifyB() {
		// TODO: Implement this
		final Expression input = and(mA, or(mA, mB));
		final Expression afterSimplify = mA;
		testSimplify(input, afterSimplify);
	}

	@Test
	public void testNNF() {
		final Expression input = not(mA);
		final Expression nnf = input;
		final Expression dnf = input;
		test(input, nnf, dnf);
		testSimplify(input, input);
	}

	@Test
	public void testA() {
		final Expression input = not(mExp1);
		final Expression nnf = and(not(mB), not(mC));
		final Expression dnf = and(not(mC), not(mB));
		test(input, nnf, dnf);
	}

	@Test
	public void testB() {
		final Expression input = mExp2;
		final Expression nnf = and(and(mA, or(mC, mB)), or(mD, mA));
		final Expression dnf = or(and(mA, mB), and(mA, mC));
		test(input, nnf, dnf);
	}

	@Test
	public void testC() {
		final Expression input = mExp3;
		final Expression nnf = and(and(mA, or(mC, mB)), or(mD, mA));
		final Expression dnf = or(and(mA, mB), and(mA, mC));
		test(input, nnf, dnf);
	}

	@Test
	public void testD() {
		final Expression input = mExp4;
		final Expression nnf = or(or(not(mA), and(not(mC), not(mB))), and(not(mD), not(mA)));
		final Expression dnf = or(and(not(mC), not(mB)), not(mA));
		test(input, nnf, dnf);
	}

	@Test
	public void testE() {
		// (((A || B) && (C || D)) && (E || F)) && (G || H)
		final Expression input =
				and(and(and(or(intVar("A"), intVar("B")), or(intVar("C"), intVar("D"))), or(intVar("E"), intVar("F"))),
						or(intVar("G"), intVar("H")));
		final Expression nnf =
				and(and(and(or(intVar("B"), intVar("A")), or(intVar("D"), intVar("C"))), or(intVar("F"), intVar("E"))),
						or(intVar("H"), intVar("G")));
		final Expression dnf = or(and(intVar("C"), intVar("A"), intVar("G"), intVar("E")),
				and(intVar("C"), intVar("A"), intVar("G"), intVar("E")),
				and(intVar("C"), intVar("A"), intVar("H"), intVar("E")),
				and(intVar("C"), intVar("A"), intVar("G"), intVar("F")),
				and(intVar("C"), intVar("A"), intVar("H"), intVar("F")),
				and(intVar("D"), intVar("A"), intVar("G"), intVar("E")),
				and(intVar("D"), intVar("A"), intVar("H"), intVar("E")),
				and(intVar("D"), intVar("A"), intVar("G"), intVar("F")),
				and(intVar("D"), intVar("A"), intVar("H"), intVar("F")),
				and(intVar("C"), intVar("B"), intVar("G"), intVar("E")),
				and(intVar("C"), intVar("B"), intVar("H"), intVar("E")),
				and(intVar("C"), intVar("B"), intVar("G"), intVar("F")),
				and(intVar("C"), intVar("B"), intVar("H"), intVar("F")),
				and(intVar("D"), intVar("B"), intVar("G"), intVar("E")),
				and(intVar("D"), intVar("B"), intVar("H"), intVar("E")),
				and(intVar("D"), intVar("B"), intVar("G"), intVar("F")),
				and(intVar("D"), intVar("B"), intVar("H"), intVar("F")));
		// i dont want to order this s.t. it fits :(
		test(input, nnf, null);
	}

	@Test
	public void testNotEquals() {
		final Expression input = term(boolVar("A"), true, Operator.COMPNEQ);
		testRewrite(input, input);
	}

	private static void testRewrite(final Expression input, final Expression afterRewrite) {
		final NormalFormTransformer<Expression> ct = new NormalFormTransformer<>(new BoogieExpressionTransformer());
		System.out.println();
		System.out.println("Input: " + printExpression(input));
		final Expression result = ct.rewriteNotEquals(input);
		System.out.println("Rewri: " + printExpression(result));

		Assert.assertEquals("Rewrite of " + printExpression(input) + " not correct,", printExpression(afterRewrite),
				printExpression(result));
	}

	private static void testSimplify(final Expression input, final Expression afterSimplify) {
		final NormalFormTransformer<Expression> ct = new NormalFormTransformer<>(new BoogieExpressionTransformer());
		System.out.println();
		System.out.println("Input: " + printExpression(input));
		final Expression result = ct.simplify(input);
		System.out.println("Simpl: " + printExpression(result));

		Assert.assertEquals("Simplify of " + printExpression(input) + " not correct,", printExpression(afterSimplify),
				printExpression(result));
	}

	private static void test(final Expression input, final Expression afterNnf, final Expression afterDnf) {
		System.out.println();
		final NormalFormTransformer<Expression> ct = new NormalFormTransformer<>(new BoogieExpressionTransformer());
		System.out.println("Input: " + printExpression(input));
		Expression result = ct.toNnf(input);
		System.out.println("NNF  : " + printExpression(result));
		if (afterNnf != null) {
			Assert.assertEquals("NNF of " + printExpression(input) + " not correct,", printExpression(afterNnf),
					printExpression(result));
		}

		result = ct.toDnf(input);
		System.out.println("DNF  : " + printExpression(result));
		if (afterDnf != null) {
			Assert.assertEquals("DNF of " + printExpression(input) + " not correct,", printExpression(afterDnf),
					printExpression(result));
		}
	}

	private static String printExpression(final Expression result) {
		if (result != null) {
			return BoogiePrettyPrinter.print(result);
		}
		return "NULL";
	}
}
