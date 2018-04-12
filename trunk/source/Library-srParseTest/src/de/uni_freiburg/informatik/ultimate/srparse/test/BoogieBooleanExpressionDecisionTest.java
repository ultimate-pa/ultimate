package de.uni_freiburg.informatik.ultimate.srparse.test;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.pea.BoogieBooleanExpressionDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

/**
 *
 * @author VL
 * @TODO put into the right testing project
 *
 */
public class BoogieBooleanExpressionDecisionTest {

	/**
	 * Test CDD together with BoogieBooleanExpressionDecision, especially if negation and logic operations work
	 * properly.
	 */
	@Test
	public void testBoogieBooleanExpressinDecision() {
		final ILocation dummyLocation = new BoogieLocation("test", 0, 0, 0, 0);

		final Expression e = new BinaryExpression(dummyLocation, BinaryExpression.Operator.COMPEQ,
				new IdentifierExpression(dummyLocation, "crew"), new IntegerLiteral(dummyLocation, "47"));

		final Expression e2 = new BinaryExpression(dummyLocation, BinaryExpression.Operator.COMPLT,
				new IdentifierExpression(dummyLocation, "test"), new RealLiteral(dummyLocation, "5.0"));

		final Expression e3 = new BinaryExpression(dummyLocation, BinaryExpression.Operator.COMPNEQ,
				new IdentifierExpression(dummyLocation, "answer"), new BooleanLiteral(dummyLocation, true));

		CDD cdd = BoogieBooleanExpressionDecision.create(e); // (crew == 47)
		cdd = cdd.negate(); // !(crew == 47)
		cdd = cdd.and(BoogieBooleanExpressionDecision.create(e2)); // !(crew == 47)∧(test <= 5.0)
		cdd = cdd.or(BoogieBooleanExpressionDecision.create(e3)); // (answer != true)∨(!(crew == 47)∧(test <= 5.0))
		Assert.assertEquals("(answer != true ∨ (!(crew == 47) ∧ test < 5.0))", cdd.toString(true));

		cdd = cdd.negate();
		Assert.assertEquals("(!(answer != true) ∧ (crew == 47 ∨ !(test < 5.0)))", cdd.toString());
	}

	@Test
	public void testBoogieBooleanExpressionDecisionIt() {
		final ILocation dummyLocation = new BoogieLocation("test", 0, 0, 0, 0);
		// signle boolean expression
		final Expression e = new IdentifierExpression(dummyLocation, "e");
		CDD cdd = BoogieBooleanExpressionDecision.create(e);
		Assert.assertEquals("e", cdd.toString(true));
		cdd = cdd.negate();
		Assert.assertEquals("!e", cdd.toString(true));
		// conjunction of two boolean expressions
		final Expression e2 = new IdentifierExpression(dummyLocation, "f");
		cdd = cdd.and(BoogieBooleanExpressionDecision.create(e2));
		Assert.assertEquals("(!e ∧ f)", cdd.toString(true));
		cdd = cdd.negate();
		Assert.assertEquals("(e ∨ !f)", cdd.toString(true));
		cdd = cdd.negate();
		Assert.assertEquals("(!e ∧ f)", cdd.toString(true));
		final Expression f = new IdentifierExpression(dummyLocation, "f");
		cdd = cdd.and(BoogieBooleanExpressionDecision.create(f));
		Assert.assertEquals("(!e ∧ f)", cdd.toString(true));
		// conjuction disjunction
		final Expression e3 = new IdentifierExpression(dummyLocation, "g");
		cdd = cdd.or(BoogieBooleanExpressionDecision.create(e3));
		Assert.assertEquals("(g ∨ (!e ∧ (f ∨ g)))", cdd.toString(true));
		cdd = cdd.negate();
		Assert.assertEquals("((e ∧ !g) ∨ (!f ∧ !g))", cdd.toString(true));
	}

}
