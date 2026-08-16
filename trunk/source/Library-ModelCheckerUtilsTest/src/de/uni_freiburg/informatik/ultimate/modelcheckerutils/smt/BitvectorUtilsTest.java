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
 * Tests for the extract-over-extend simplification added to
 * {@link de.uni_freiburg.informatik.ultimate.lib.smtlibutils.BitvectorUtils}: extracting bits [hi:0] from a
 * sign_extend/zero_extend result collapses to the original value, or to a smaller extend of it.
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

	// --- Extract-over-extend no-op ---

	@Test
	public void bvExtractOverSignExtend() {
		// extract exactly undoes sign_extend when the width matches: ((_ extract 7 0) ((_ sign_extend 24) x)) -> x.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "((_ extract 7 0) ((_ sign_extend 24) x))";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvExtractOverZeroExtend() {
		// Same no-op for zero_extend: ((_ extract 7 0) ((_ zero_extend 24) x)) -> x.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "((_ extract 7 0) ((_ zero_extend 24) x))";
		final String expected = "x";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvExtractOverSignExtendPartialReduction() {
		// Extracting MORE than the original width but LESS than the full extended width keeps some padding bits,
		// which is equivalent to a smaller extend, not the bare original value:
		// ((_ extract 15 0) ((_ sign_extend 24) x)) -> ((_ sign_extend 8) x), for an 8-bit x.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "((_ extract 15 0) ((_ sign_extend 24) x))";
		final String expected = "((_ sign_extend 8) x)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvExtractOfFullExtendedWidthNotHandledByThisRule() {
		// Guard: extracting the ENTIRE extended width (bit 31 of a 32-bit result) is out of scope for this rule -
		// it's a different ("extract of full range") simplification, not yet implemented - so it must stay as-is.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "x") };
		final String formulaAsString = "((_ extract 31 0) ((_ sign_extend 24) x))";
		final String expected = "((_ extract 31 0) ((_ sign_extend 24) x))";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvExtractOfPlainVariableNotSimplified() {
		// Guard: no sign_extend/zero_extend underneath at all, so the rule must not touch it.
		final FunDecl[] funDecls = { new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "y") };
		final String formulaAsString = "((_ extract 7 0) y)";
		final String expected = "((_ extract 7 0) y)";

		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expected, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}
}
