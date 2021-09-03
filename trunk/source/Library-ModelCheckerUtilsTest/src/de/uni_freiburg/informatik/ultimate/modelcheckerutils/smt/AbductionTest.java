/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtilsTest Library.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Collections;
import java.util.Set;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.abduction.Abducer;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class AbductionTest {
	private static final long TEST_TIMEOUT_MILLISECONDS = 10_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:1000 -memory:2024 -smt2 -in";

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LOG_LEVEL);
		mServices.getProgressMonitorService().setDeadline(System.currentTimeMillis() + TEST_TIMEOUT_MILLISECONDS);

		mScript = new HistoryRecordingScript(UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL));
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	@Test
	public void noSolution() {
		final Term premise = TermParseUtils.parseTerm(mScript, "false");
		final Term conclusion = parseWithVariables("(>= x 0)", "(x Int)");
		runAbductionTest(premise, conclusion, null);
	}

	@Test
	public void simpleInequalities() {
		final Term premise = parseWithVariables("(>= x 0)", "(x Int)");
		final Term conclusion = parseWithVariables("(>= (+ x y) 0)", "(x Int)", "(y Int)");
		final Term expected = parseWithVariables("(>= y 0)", "(y Int)");
		runAbductionTest(premise, conclusion, expected);
	}

	@Test
	public void transformulaNaive() {
		final Term premise = parseWithVariables("(= x1 (+ x0 y0))", "(x0 Int)", "(y0 Int)", "(x1 Int)");
		final Term conclusion = parseWithVariables("(>= x1 0)", "(x1 Int)");
		final Term expected = parseWithVariables("(>= x1 0)", "(x1 Int)");
		runAbductionTest(premise, conclusion, expected);
	}

	@Test
	public void transformulaPre() {
		final Term premise = parseWithVariables("(= x1 (+ x0 y0))", "(x0 Int)", "(y0 Int)", "(x1 Int)");
		final Term conclusion = parseWithVariables("(>= x1 0)", "(x1 Int)");
		final Term expected = parseWithVariables("(>= (+ x0 y0) 0)", "(x0 Int)", "(y0 Int)");
		final TermVariable outVar = mScript.variable("x1", mScript.sort("Int"));
		runAbductionTest(premise, conclusion, Collections.singleton(outVar), expected, false);
	}

	@Test
	public void commutingStores() {
		final Term premise = parseWithVariables("(= arr2 (store (store arr0 i 2) j 3))", "(i Int)", "(j Int)",
				"(arr0 (Array Int Int))", "(arr2 (Array Int Int))");
		final Term conclusion = parseWithVariables("(= arr2 (store (store arr0 j 3) i 2))", "(i Int)", "(j Int)",
				"(arr0 (Array Int Int))", "(arr2 (Array Int Int))");
		final Term expected = parseWithVariables("(distinct i j)", "(i Int)", "(j Int)");
		final TermVariable outVar =
				mScript.variable("arr2", mScript.sort("Array", mScript.sort("Int"), mScript.sort("Int")));
		runAbductionTest(premise, conclusion, Collections.singleton(outVar), expected, false);
	}

	@Test
	public void commutingStores2() {
		final Term premise = parseWithVariables("(= arr2 (store (store arr0 i (+ i 1)) j 3))", "(i Int)", "(j Int)",
				"(arr0 (Array Int Int))", "(arr2 (Array Int Int))");
		final Term conclusion = parseWithVariables("(= arr2 (store (store arr0 j 3) i (+ i 1)))", "(i Int)", "(j Int)",
				"(arr0 (Array Int Int))", "(arr2 (Array Int Int))");
		final Term expected = parseWithVariables("(= i 2)", "(i Int)", "(j Int)");
		final TermVariable outVar =
				mScript.variable("arr2", mScript.sort("Array", mScript.sort("Int"), mScript.sort("Int")));
		runAbductionTest(premise, conclusion, Collections.singleton(outVar), expected, false);
	}

	@Test
	public void equivalenceEquality() {
		final Term lhs = parseWithVariables("(and (= x 0) (= x y))", "(x Int)", "(y Int)");
		final Term rhs = parseWithVariables("(= y 0)", "(y Int)");
		final Term expected = parseWithVariables("(= x 0)", "(x Int)", "(y Int)");
		runAbductionTest(lhs, rhs, Collections.emptySet(), expected, true);
	}

	private void runAbductionTest(final Term premise, final Term conclusion, final Term expected) {
		runAbductionTest(premise, conclusion, Collections.emptySet(), expected, false);
	}

	private void runAbductionTest(final Term premise, final Term conclusion, final Set<TermVariable> forbidden,
			final Term expected, final boolean equiv) {
		final Term result;
		if (equiv) {
			result = new Abducer(mServices, mMgdScript, forbidden).abduceEquivalence(premise, conclusion);
		} else {
			result = new Abducer(mServices, mMgdScript, forbidden).abduce(premise, conclusion);
		}
		if (expected == null) {
			assert result == null : "Unexpectedly found solution to abduction problem: " + result;
		} else {
			assert result != null : "No solution found to abduction problem, expected " + expected;
			final LBool sat = SmtUtils.checkEquivalence(expected, result, mScript);
			assert sat != LBool.SAT : "Unexpected abduction result -- actual: " + result + ", expected: " + expected;
			assert sat == LBool.UNSAT : "Abduction result could not be proven equivalent -- actual: " + result
					+ ", expected: " + expected;
		}
	}

	private Term parseWithVariables(final String syntax, final String... declarations) {
		final String fullSyntax = "(forall (" + String.join(" ", declarations) + ") " + syntax + ")";
		final QuantifiedFormula quant = (QuantifiedFormula) TermParseUtils.parseTerm(mScript, fullSyntax);
		return new CommuhashNormalForm(mServices, mScript).transform(quant.getSubformula());
	}
}
