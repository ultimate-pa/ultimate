/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.io.IOException;

import org.hamcrest.MatcherAssert;
import org.hamcrest.core.IsEqual;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.StatisticsScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * Tests for mirroring the "greater than" bitvector comparisons ({@code bvugt}, {@code bvuge}, {@code bvsgt},
 * {@code bvsge}) onto their swapped "less than" counterpart in
 * {@link de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils}, and for confirming that constant
 * folding still applies after the swap.
 *
 * Extracted from {@link SimplificationTest} into its own file; reuses {@link SimplificationTest#runSimplificationTest}
 * so the test-running/-checking logic is not duplicated.
 *
 * @author Roman Vintonyak
 * @author David Enoghama
 *
 */
public class BitvectorUtilsTest {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY = false;
	private static final long TEST_TIMEOUT_MILLISECONDS = 20_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final String SOLVER_COMMAND = "cvc4 --incremental --lang smt";

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private static QuantifierEliminationTestCsvWriter mCsvWriter;

	@BeforeClass
	public static void beforeAllTests() {
		mCsvWriter = new QuantifierEliminationTestCsvWriter(BitvectorUtilsTest.class.getSimpleName());
	}

	@AfterClass
	public static void afterAllTests() {
		if (WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY) {
			try {
				mCsvWriter.writeCsv();
			} catch (final IOException e) {
				throw new AssertionError(e);
			}
		}
	}

	@Before
	public void setUp() throws IOException {
		mServices = UltimateMocks.createUltimateServiceProviderMock(LOG_LEVEL);
		mServices.getProgressMonitorService().setDeadline(System.currentTimeMillis() + TEST_TIMEOUT_MILLISECONDS);
		mLogger = mServices.getLoggingService().getLogger("lol");

		final Script solverInstance = new HistoryRecordingScript(UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL));
		if (WRITE_SMT_SCRIPTS_TO_FILE) {
			mScript = new LoggingScript(solverInstance, "BitvectorUtilsTest.smt2", true);
		} else {
			mScript = solverInstance;
		}
		mScript = new StatisticsScript(mScript);

		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
	}

	@After
	public void tearDown() {
		mScript.exit();
		mCsvWriter.reportTestFinished();
	}

	// --- Operator mirroring (bvugt/bvuge/bvsgt/bvsge -> bvult/bvule/bvslt/bvsle) ---

	@Test
	public void bvugtMirroredToBvult() {
		// Unsigned "greater than" is eliminated by swapping operands into "less than": (x bvugt 1) -> (1 bvult x).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvugt x (_ bv1 8))";
		final String expected = "(bvult (_ bv1 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvugeMirroredToBvule() {
		// Same mirroring for the non-strict unsigned variant: (x bvuge 1) -> (1 bvule x).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvuge x (_ bv1 8))";
		final String expected = "(bvule (_ bv1 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvsgtMirroredToBvslt() {
		// Signed "greater than" is mirrored the same way as the unsigned case: (x bvsgt 1) -> (1 bvslt x).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvsgt x (_ bv1 8))";
		final String expected = "(bvslt (_ bv1 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvsgeMirroredToBvsle() {
		// Same mirroring for the non-strict signed variant: (x bvsge 1) -> (1 bvsle x).
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "(bvsge x (_ bv1 8))";
		final String expected = "(bvsle (_ bv1 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvugtConstantFoldingAfterMirroring() {
		// Guards against a purely syntactic swap: mirroring to bvult must still trigger the existing constant
		// folding, not just rewrite the operator. Both operands are literals here, so the result must be "true",
		// not an unevaluated (bvult (_ bv3 8) (_ bv5 8)) term.
		final String formulaAsString = "(bvugt (_ bv5 8) (_ bv3 8))";
		final String expected = "true";

		SimplificationTest.runSimplificationTest(new FunDecl[0], formulaAsString, expected,
				SimplificationTechnique.POLY_PAC, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvsgtConstantFoldingAfterMirroring() {
		// Same guard for the signed variant, to confirm signed constant folding also still works after mirroring.
		final String formulaAsString = "(bvsgt (_ bv5 8) (_ bv3 8))";
		final String expected = "true";

		SimplificationTest.runSimplificationTest(new FunDecl[0], formulaAsString, expected,
				SimplificationTechnique.POLY_PAC, mServices, mLogger, mMgdScript, mCsvWriter);
	}

}
