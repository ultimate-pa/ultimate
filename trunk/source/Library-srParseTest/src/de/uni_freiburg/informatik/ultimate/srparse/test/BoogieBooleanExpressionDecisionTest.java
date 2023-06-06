/*
 * Copyright (C) 2019 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-srParse plug-in.
 *
 * The ULTIMATE Library-srParse plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-srParse plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-srParse plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-srParse plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-srParse plug-in grant you additional permission
 * to convey the resulting work.
 */
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
		cdd = cdd.and(BoogieBooleanExpressionDecision.create(e2)); // !(crew == 47)&&(test <= 5.0)
		cdd = cdd.or(BoogieBooleanExpressionDecision.create(e3)); // (answer != true)||(!(crew == 47)&&(test <= 5.0))
		Assert.assertEquals("(answer != true || (!(crew == 47) && test < 5.0))", cdd.toString(true));

		cdd = cdd.negate();
		Assert.assertEquals("(!(answer != true) && (crew == 47 || !(test < 5.0)))", cdd.toString());
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
		Assert.assertEquals("(!e && f)", cdd.toString(true));
		cdd = cdd.negate();
		Assert.assertEquals("(e || !f)", cdd.toString(true));
		cdd = cdd.negate();
		Assert.assertEquals("(!e && f)", cdd.toString(true));
		final Expression f = new IdentifierExpression(dummyLocation, "f");
		cdd = cdd.and(BoogieBooleanExpressionDecision.create(f));
		Assert.assertEquals("(!e && f)", cdd.toString(true));
		// conjunction disjunction
		final Expression e3 = new IdentifierExpression(dummyLocation, "g");
		cdd = cdd.or(BoogieBooleanExpressionDecision.create(e3));
		Assert.assertEquals("(g || (!e && (f || g)))", cdd.toString(true));
		cdd = cdd.negate();
		Assert.assertEquals("((e && !g) || (!f && !g))", cdd.toString(true));
	}

}
