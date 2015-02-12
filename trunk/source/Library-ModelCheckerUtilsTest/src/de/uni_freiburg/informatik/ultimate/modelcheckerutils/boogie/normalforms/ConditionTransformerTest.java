package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms;

import java.util.HashMap;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;

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
		mA = var("A");
		mB = var("B");
		mC = var("C");
		mD = var("D");
		mExp1 = or(mB, mC);

		Expression aord = or(mA, mD);
		Expression aandborc = and(mA, mExp1);

		mExp2 = and(aandborc, aord);
		mExp3 = or(mExp2, mExp2);
		mExp4 = not(mExp3);

	}

	private Expression not(Expression exp) {
		return new UnaryExpression(null, UnaryExpression.Operator.LOGICNEG, exp);
	}

	private Expression and(Expression left, Expression right) {
		return new BinaryExpression(null, Operator.LOGICAND, left, right);
	}

	private Expression or(Expression left, Expression right) {
		return new BinaryExpression(null, Operator.LOGICOR, left, right);
	}

	private Expression var(String varname) {
		Expression exp = mIdentifier.get(varname);
		if (exp == null) {
			exp = new IdentifierExpression(null, varname);
			mIdentifier.put(varname, exp);
		}
		return exp;
	}

	/**
	 * No Typechecking!
	 */
	private Expression term(Expression var, int lit, Operator op) {
		return new BinaryExpression(null, op, var, new IntegerLiteral(null, String.valueOf(lit)));
	}

	@Test
	public void TestRewriteA() {
		Expression input = term(mA, 1, Operator.COMPNEQ);
		Expression afterRewrite = or(term(mA, 1, Operator.COMPLT), term(mA, 1, Operator.COMPGT));
		TestRewrite(input, afterRewrite);
	}

	@Test
	public void TestRewriteB() {
		Expression input = or(mExp2, term(mA, 1, Operator.COMPNEQ));
		Expression afterRewrite = or(or(and(and(or(mA, mD), or(mB, mC)), mA), term(mA, 1, Operator.COMPGT)),
				term(mA, 1, Operator.COMPLT));
		TestRewrite(input, afterRewrite);
	}

	@Test
	public void TestRewriteC() {
		Expression input = and(and(not(term(mA, 0, Operator.COMPNEQ)), not(term(mB, 1, Operator.COMPEQ))),
				not(term(mC, 1, Operator.COMPEQ)));
		Expression afterRewrite = and(
				and(term(mA, 0, Operator.COMPEQ), or(term(mB, 1, Operator.COMPLT), term(mB, 1, Operator.COMPGT))),
				or(term(mC, 1, Operator.COMPLT), term(mC, 1, Operator.COMPGT)));
		TestRewrite(input, afterRewrite);
	}

	@Test
	public void TestSimplifyA() {
		Expression input = and(mA, mA);
		Expression afterSimplify = mA;
		TestSimplify(input, afterSimplify);
	}

	// @Test
	public void TestSimplifyB() {
		// TODO: Implement this
		Expression input = and(mA, or(mA, mB));
		Expression afterSimplify = mA;
		TestSimplify(input, afterSimplify);
	}

	@Test
	public void TestA() {
		Expression input = not(mExp1);
		Expression nnf = and(not(mB), not(mC));
		Expression dnf = and(not(mC), not(mB));
		Test(input, nnf, dnf);
	}

	@Test
	public void TestB() {
		Expression input = mExp2;
		Expression nnf = and(and(mA, or(mC, mB)), or(mD, mA));
		Expression dnf = or(and(mA, mB), and(mA, mC));
		Test(input, nnf, dnf);
	}

	@Test
	public void TestC() {
		Expression input = mExp3;
		Expression nnf = and(and(mA, or(mC, mB)), or(mD, mA));
		Expression dnf = or(and(mA, mB), and(mA, mC));
		Test(input, nnf, dnf);
	}

	@Test
	public void TestD() {
		Expression input = mExp4;
		Expression nnf = or(or(not(mA), and(not(mC), not(mB))), and(not(mD), not(mA)));
		Expression dnf = or(and(not(mC), not(mB)), not(mA));
		Test(input, nnf, dnf);
	}

	@Test
	public void TestE() {
		// (((A || B) && (C || D)) && (E || F)) && (G || H)
		Expression input = and(and(and(or(var("A"), var("B")), or(var("C"), var("D"))), or(var("E"), var("F"))),
				or(var("G"), var("H")));
		Expression afterNNF = and(and(and(or(var("B"), var("A")), or(var("D"), var("C"))), or(var("F"), var("E"))),
				or(var("H"), var("G")));
		ConditionTransformer<Expression> ct = new ConditionTransformer<>(new BoogieConditionWrapper());
		input = ct.rewriteNotEquals(input);
		
		Test(input, afterNNF, input);
	}

	private void TestRewrite(Expression input, Expression afterRewrite) {

		ConditionTransformer<Expression> ct = new ConditionTransformer<>(new BoogieConditionWrapper());
		System.out.println();
		System.out.println("Input: " + printExpression(input));
		ct.simplify(input);
		Expression result = ct.rewriteNotEquals(input);
		System.out.println("Rewri: " + printExpression(result));

		Assert.assertEquals("Rewrite of " + printExpression(input) + "not correct,", printExpression(result),
				printExpression(afterRewrite));

	}

	private void TestSimplify(Expression input, Expression afterSimplify) {

		ConditionTransformer<Expression> ct = new ConditionTransformer<>(new BoogieConditionWrapper());
		System.out.println();
		System.out.println("Input: " + printExpression(input));
		ct.simplify(input);
		Expression result = ct.simplify(input);
		System.out.println("Simpl: " + printExpression(result));

		Assert.assertEquals("Simplify of " + printExpression(input) + "not correct,", printExpression(result),
				printExpression(afterSimplify));

	}

	private void Test(Expression input, Expression afterNnf, Expression afterDnf) {
		System.out.println();
		ConditionTransformer<Expression> ct = new ConditionTransformer<>(new BoogieConditionWrapper());
		System.out.println("Input: " + printExpression(input));
		Expression result = ct.toNnf(input);
		System.out.println("NNF  : " + printExpression(result));
		if (afterNnf != null) {
			Assert.assertEquals("NNF of " + printExpression(input) + "not correct,", printExpression(result),
					printExpression(afterNnf));
		}

		result = ct.toDnf(input);
		System.out.println("DNF  : " + printExpression(result));
		if (afterDnf != null) {
			Assert.assertEquals("DNF of " + printExpression(input) + " not correct,", printExpression(result),
					printExpression(afterDnf));
		}
	}

	private String printExpression(Expression result) {
		if (result != null) {
			return BoogiePrettyPrinter.print(result);
		} else {
			return "NULL";
		}
	}
}
