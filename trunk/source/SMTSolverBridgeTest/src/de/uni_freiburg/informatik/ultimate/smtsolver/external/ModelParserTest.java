/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE SMTSolverBridge.
 *
 * The ULTIMATE SMTSolverBridge is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SMTSolverBridge is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SMTSolverBridge. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SMTSolverBridge, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SMTSolverBridge grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.smtsolver.external;

import java.math.BigInteger;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class ModelParserTest {

	private Script mScript;

	@Before
	public void setUp() {
		mScript = UltimateMocks.createZ3Script();
	}

	@Test
	public void testSimpleIntModel() {
		mScript.setLogic("LIA");
		mScript.setOption(SMTLIBConstants.PRODUCE_MODELS, true);
		mScript.declareFun("x", Script.EMPTY_SORT_ARRAY, mScript.sort("Int"));
		final ApplicationTerm x = (ApplicationTerm) mScript.term("x");
		mScript.assertTerm(mScript.term(">=", x, mScript.numeral(BigInteger.ZERO)));
		mScript.checkSat();
		final var model = mScript.getModel();
		final var term = model.getFunctionDefinition(x.getFunction()).getSubterm();

		assert term instanceof ConstantTerm;
		final var constant = (ConstantTerm) term;

		final var value = constant.getValue();
		assert value instanceof Rational;

		final var rat = (Rational) value;
		assert rat.isIntegral() && !rat.isNegative();
	}

	@Test
	public void testSimpleHorn() {
		mScript.setLogic(Logics.HORN);
		mScript.setOption(SMTLIBConstants.PRODUCE_MODELS, true);
		mScript.declareFun("P", new Sort[] { mScript.sort("Int") }, mScript.sort("Bool"));

		final var x = mScript.variable("x", mScript.sort("Int"));
		final var p = (ApplicationTerm) mScript.term("P", x);
		// x = 0 -> P(x)
		mScript.assertTerm(mScript.quantifier(QuantifiedFormula.FORALL, new TermVariable[] { x },
				mScript.term("=>", mScript.term("=", x, mScript.numeral(BigInteger.ZERO)), p)));
		// P(x) /\ x >= 1 -> false
		mScript.assertTerm(mScript.quantifier(QuantifiedFormula.FORALL, new TermVariable[] { x },
				mScript.term("=>", mScript.term("and", p, mScript.term(">=", x, mScript.numeral(BigInteger.ONE))),
						mScript.term("false"))));
		mScript.checkSat();
		final var model = mScript.getModel();

		final var app = model.getFunctionDefinition(p.getFunction()).getSubterm();
		assert "(= x!0 0)".equals(app.toString());
	}

	@Test
	public void testDoubleHorn() {
		mScript.setLogic(Logics.HORN);
		mScript.setOption(SMTLIBConstants.PRODUCE_MODELS, true);
		mScript.declareFun("P", new Sort[] { mScript.sort("Int") }, mScript.sort("Bool"));
		mScript.declareFun("Q", new Sort[] { mScript.sort("Int") }, mScript.sort("Bool"));

		final var x = mScript.variable("x", mScript.sort("Int"));
		final var p = (ApplicationTerm) mScript.term("P", x);
		final var q = (ApplicationTerm) mScript.term("Q", x);

		// x >= 0 -> P(x)
		mScript.assertTerm(mScript.quantifier(QuantifiedFormula.FORALL, new TermVariable[] { x },
				mScript.term("=>", mScript.term(">=", x, mScript.numeral(BigInteger.ZERO)), p)));
		// x <= 0 -> Q(x)
		mScript.assertTerm(mScript.quantifier(QuantifiedFormula.FORALL, new TermVariable[] { x },
				mScript.term("=>", mScript.term("<=", x, mScript.numeral(BigInteger.ZERO)), q)));
		// P(x) /\ Q(x) /\ x =/= 0 -> false
		mScript.assertTerm(mScript.quantifier(QuantifiedFormula.FORALL, new TermVariable[] { x },
				mScript.term("=>",
						mScript.term("and", p, q, mScript.term("distinct", x, mScript.numeral(BigInteger.ZERO))),
						mScript.term("false"))));
		mScript.checkSat();
		final var model = mScript.getModel();

		final var appP = model.getFunctionDefinition(p.getFunction()).getSubterm();
		assert "(>= x!0 0)".equals(appP.toString());

		final var appQ = model.getFunctionDefinition(q.getFunction()).getSubterm();
		assert "(<= x!0 0)".equals(appQ.toString());
	}
}
