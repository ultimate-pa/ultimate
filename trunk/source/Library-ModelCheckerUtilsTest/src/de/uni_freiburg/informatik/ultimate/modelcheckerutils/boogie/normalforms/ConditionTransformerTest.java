package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;

public class ConditionTransformerTest {

	private final Expression mExp4;
	private final Expression mExp3;
	private final Expression mExp2;
	private final Expression mA;
	private final Expression mB;
	private final Expression mC;
	private final Expression mD;
	private final Expression mExp1;

	public ConditionTransformerTest() {
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
		return new IdentifierExpression(null, varname);
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
