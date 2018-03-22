/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie;

import org.hamcrest.core.Is;
import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.lib.pea.BoogieBooleanExpressionDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.CDDTranslator;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class Cdd2BoogieTestsuite {

	private static final BoogieLocation LOC = new BoogieLocation("test", 0, 0, 0, 0);

	@Test
	public void testCdd2Boogie() {
		final CDD A = CDD.create(new BooleanDecision("A"), CDD.TRUE_CHILDS);
		final CDD B = CDD.create(new BooleanDecision("B"), CDD.TRUE_CHILDS);
		final CDD C = CDD.create(new BooleanDecision("C"), CDD.TRUE_CHILDS);
		final CDD notC = BoogieBooleanExpressionDecision.createWithoutReduction(
				ExpressionFactory.constructUnaryExpression(LOC, Operator.LOGICNEG, new IdentifierExpression(LOC,
						BoogieType.TYPE_BOOL, "C", new DeclarationInformation(StorageClass.GLOBAL, null))));
		final CDD notCCreate = BoogieBooleanExpressionDecision
				.create(ExpressionFactory.constructUnaryExpression(LOC, Operator.LOGICNEG, new IdentifierExpression(LOC,
						BoogieType.TYPE_BOOL, "C", new DeclarationInformation(StorageClass.GLOBAL, null))));

		final CDD eqAZero = RangeDecision.create("A", RangeDecision.OP_EQ, 0);
		final CDD gtAOne = RangeDecision.create("A", RangeDecision.OP_GT, 1);
		final CDD ltAZero = RangeDecision.create("A", RangeDecision.OP_LT, 0);
		final CDD geqAOne = RangeDecision.create("A", RangeDecision.OP_GTEQ, 1);
		// final CDD gtAOne = RangeDecision.create("A", RangeDecision.OP_GTEQ, 1);

		test(CDD.TRUE, "true");
		test(CDD.FALSE, "false");
		test(eqAZero, "A == 0.0");
		test(eqAZero.negate(), "A > 0.0 || A < 0.0");
		test(eqAZero.and(gtAOne), "false");
		test(gtAOne, "A > 1.0");
		test(gtAOne.negate(), "A <= 1.0");
		test(geqAOne, "A >= 1.0");
		test(ltAZero, "A < 0.0");
		test(ltAZero.negate(), "A >= 0.0");
		test(ltAZero.and(gtAOne.negate()), "A < 0.0");
		test(ltAZero.or(eqAZero), "A <= 0.0");
		test(ltAZero.negate().and(gtAOne.negate()), "0.0 <= A && A <= 1.0");
		test(ltAZero.and(B).or(gtAOne.negate()), "A <= 1.0");
		test(ltAZero.and(B.or(gtAOne.negate())), "A < 0.0");
		test(ltAZero.or(B.and(gtAOne.negate())), "A < 0.0 || (B && A <= 1.0)");
		test(geqAOne.negate().and(ltAZero.or(eqAZero).negate()), "0.0 < A && A < 1.0");
		test(A.and(B).or(B.and(A.negate())), "B");
		test(A.and(B).or(B.negate().and(A)), "A");

		test(A, "A");
		test(B, "B");
		test(notC, "!C");
		test(notC.and(notC.negate()), "false");
		test(C.and(notC), "!C && C");
		test(C.and(notCCreate), "false");
		test(A.negate(), "!A");
		test(A.or(B), "B || A");
		test(A.and(B), "A && B");
		test(A.and(B.negate()), "A && !B");
		test(A.negate().and(B), "!A && B");
		test(A.negate().and(B.negate()), "!A && !B");
		test(A.negate().and(B.negate()).negate(), "B || A");
	}

	private static void test(final CDD input, final String expected) {
		final Expression exprNotA = new CDDTranslator().toBoogie(input, LOC);
		Assert.assertThat(BoogiePrettyPrinter.print(exprNotA), Is.is(expected));
	}
}
