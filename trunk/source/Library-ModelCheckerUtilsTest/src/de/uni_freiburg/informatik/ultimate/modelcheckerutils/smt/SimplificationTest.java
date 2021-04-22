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

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Assert;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class SimplificationTest {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY = false;
//	private static final long TEST_TIMEOUT_MILLISECONDS = 10_000_99999;
	private static final long TEST_TIMEOUT_MILLISECONDS = 60_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:1000 -memory:2024 -smt2 -in";

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private static QuantifierEliminationTestCsvWriter mCsvWriter;

	@BeforeClass
	public static void beforeAllTests() {
		mCsvWriter = new QuantifierEliminationTestCsvWriter(SimplificationTest.class.getSimpleName());
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
			mScript = new LoggingScript(solverInstance, "SimplificationTest.smt2", true);
		} else {
			mScript = solverInstance;
		}

		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
	}

	@After
	public void tearDown() {
		mScript.exit();
		mCsvWriter.reportTestFinished();
	}

	@Test
	public void ddaExample6 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x"), };
		final String formulaAsString = "(and (distinct x 1) (or (<= x 0) (> x 2) (= x 1)))";
		final String expectedResultAsString = "(and (not (= x 1)) (or (<= x 0) (< 2 x)))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void alternativeRepresentations () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x", "y"), };
		final String formulaAsString = "(and (distinct y x) (or (<= x 0) (> x 2) (= x y)))";
		final String expectedResultAsString = "(and (not (= x y)) (or (<= x 0) (< 2 x)))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void distinctAndLess1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (not (= x 7.0)) (< x 7.0))";
		final String expectedResultAsString = "(< x 7.0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void distinctAndLess2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (not (= x 7.0)) (< x 8.0))";
		final String expectedResultAsString = "(and (< x 8.0) (not (= 7.0x)))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void distinctAndLeq1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (not (= x 7.0)) (<= x 6.0))";
		final String expectedResultAsString = "(<= x 6.0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void distinctAndLeq2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (not (= x 7.0)) (<= x 7.0))";
		final String expectedResultAsString = "(and (not (= x 7.0)) (<= x 7.0))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void distinctAndGt1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (not (= x 7.0)) (> x 7.0))";
		final String expectedResultAsString = "(< 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void distinctAndGt2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (not (= x 7.0)) (> x 8.0))";
		final String expectedResultAsString = "(< 8.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void distinctAndGeq1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (not (= x 7.0)) (>= x 8.0))";
		final String expectedResultAsString = "(<= 8.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void distinctAndGeq2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (not (= x 7.0)) (>= x 7.0))";
		final String expectedResultAsString = "(and (not (= 7.0 x)) (<= 7.0 x))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void eqAndLess1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (= x 7.0) (< x 7.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void eqAndLess2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (= x 7.0) (< x 8.0))";
		final String expectedResultAsString = "(= 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void eqAndLeq1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (= x 7.0) (<= x 6.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void eqAndLeq2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (= x 7.0) (<= x 7.0))";
		final String expectedResultAsString = "(= 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void eqAndGt1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (= x 7.0) (> x 7.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void eqAndGt2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (= x 7.0) (> x 6.0))";
		final String expectedResultAsString = "(= 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void eqAndGeq1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (= x 7.0) (>= x 8.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void eqAndGeq2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (= x 7.0) (>= x 7.0))";
		final String expectedResultAsString = "(= 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}






	@Test
	public void geqAndLess1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (>= x 7.0) (< x 7.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void geqAndLess2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (>= x 7.0) (< x 8.0))";
		final String expectedResultAsString = "(and (< x 8.0) (<= 7.0 x))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void geqAndLeq1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (>= x 7.0) (<= x 6.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void geqAndLeq2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (>= x 7.0) (<= x 7.0))";
		final String expectedResultAsString = "(and (<= x 7.0) (<= 7.0 x))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void geqAndGt1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (>= x 7.0) (> x 7.0))";
		final String expectedResultAsString = "(< 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void geqAndGt2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (>= x 7.0) (> x 6.0))";
		final String expectedResultAsString = "(<= 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void geqAndGeq1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (>= x 7.0) (>= x 6.0))";
		final String expectedResultAsString = "(<= 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void geqAndGeq2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (>= x 7.0) (>= x 8.0))";
		final String expectedResultAsString = "(<= 8.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}




	@Test
	public void greaterAndLess1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (> x 7.0) (< x 7.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void greaterAndLess2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (> x 7.0) (< x 8.0))";
		final String expectedResultAsString = "(and (< x 8.0) (< 7.0 x))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void greaterAndLeq1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (> x 7.0) (<= x 7.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void greaterAndLeq2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (> x 7.0) (<= x 8.0))";
		final String expectedResultAsString = "(and  (< 7.0 x) (<= x 8.0))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void greaterAndGt1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (> x 7.0) (> x 8.0))";
		final String expectedResultAsString = "(< 8.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void greaterAndGt2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (> x 7.0) (> x 6.0))";
		final String expectedResultAsString = "(< 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void greaterAndGeq1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (> x 7.0) (>= x 7.0))";
		final String expectedResultAsString = "(< 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void greaterAndGeq2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (> x 7.0) (>= x 8.0))";
		final String expectedResultAsString = "(<= 8.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}




	@Test
	public void leqAndLess1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (<= x 7.0) (< x 7.0))";
		final String expectedResultAsString = "(< x 7.0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void leqAndLess2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (<= x 7.0) (< x 6.0))";
		final String expectedResultAsString = "(< x 6.0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void leqAndLeq1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (<= x 7.0) (<= x 6.0))";
		final String expectedResultAsString = "(<= x 6.0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void leqAndLeq2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (<= x 7.0) (<= x 8.0))";
		final String expectedResultAsString = "(<= x 7.0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void leqAndGt1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (<= x 7.0) (> x 7.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void leqAndGt2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (<= x 7.0) (> x 6.0))";
		final String expectedResultAsString = "(and (<= x 7.0) (< 6.0 x))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void leqAndGeq1 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (<= x 7.0) (>= x 6.0))";
		final String expectedResultAsString = "(and (<= x 7.0) (<= 6.0 x))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void leqAndGeq2 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"), new FunDecl(SmtSortUtils::getBoolSort, "A"),};
		final String formulaAsString = "(and (<= x 7.0) (>= x 8.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript);
	}



	/**
	 * Benchmark from MCR. Quantifier elimination did not terminate.
	 */
	@Test
	public void mcrPthreadWmm01 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x0", "x1"), };
		final String formulaAsString = "(exists ((v_x1_32 Int) (v_x2_42 Int) (v_x1_28 Int) (v_x2_38 Int) (v_x2_60 Int) (v_x2_54 Int) (v_x1_41 Int) (v_x1_56 Int) (v_x0_46 Int) (v_x0_59 Int) (v_x3_53 Int)) (let ((.cse47 (+ v_x1_56 1)) (.cse4 (<= 0 v_x1_56)) (.cse2 (<= v_x1_56 0)) (.cse5 (<= 0 x1)) (.cse1 (<= x1 0))) (or (let ((.cse0 (<= v_x1_56 x1)) (.cse3 (<= x1 v_x1_56))) (and .cse0 .cse1 .cse2 .cse3 .cse4 .cse5 (let ((.cse23 (<= v_x2_42 v_x2_54)) (.cse52 (+ v_x2_38 1)) (.cse53 (+ v_x2_54 1)) (.cse29 (<= v_x2_42 0))) (let ((.cse22 (<= 0 v_x2_38)) (.cse7 (<= 0 v_x2_54)) (.cse49 (not .cse29)) (.cse48 (<= .cse53 v_x2_42)) (.cse50 (<= .cse52 v_x2_42)) (.cse51 (or (<= v_x2_42 v_x2_38) .cse23)) (.cse6 (<= v_x2_38 0)) (.cse32 (<= v_x2_54 0)) (.cse26 (<= 0 v_x2_42))) (or (let ((.cse8 (<= v_x2_38 v_x2_60)) (.cse9 (ite .cse48 (=> .cse49 (or .cse29 (ite (not .cse50) .cse6 .cse51))) .cse32)) (.cse10 (<= v_x2_60 0)) (.cse36 (<= v_x2_60 v_x2_38))) (and .cse6 .cse7 .cse8 .cse9 .cse1 .cse10 (let ((.cse11 (<= v_x1_41 v_x1_56))) (or (let ((.cse13 (<= v_x1_41 x1)) (.cse14 (<= v_x1_41 0)) (.cse15 (<= 0 v_x1_41)) (.cse12 (<= x1 v_x1_41)) (.cse16 (<= v_x1_56 v_x1_41))) (and .cse11 .cse0 .cse1 .cse3 .cse12 .cse5 (or (and .cse12 .cse13) (ite .cse14 (and (<= (+ v_x1_41 1) 0) .cse15) .cse14)) .cse16 .cse13 (let ((.cse17 (<= 0 v_x0_46))) (or (and (<= (+ v_x0_46 1) 0) .cse17) (let ((.cse33 (<= v_x0_46 0))) (and (let ((.cse44 (<= (+ x0 1) 0))) (let ((.cse18 (not .cse44)) (.cse40 (<= 0 x0))) (ite .cse18 (let ((.cse20 (<= x0 0))) (let ((.cse19 (not .cse20))) (or (ite .cse19 .cse20 (<= 1 x0)) (let ((.cse34 (<= 0 v_x0_59))) (let ((.cse37 (<= v_x0_46 x0)) (.cse42 (<= x0 v_x0_46)) (.cse45 (<= v_x0_46 v_x0_59)) (.cse46 (<= v_x0_59 v_x0_46)) (.cse38 (and (<= (+ v_x0_59 1) 0) .cse34))) (let ((.cse21 (or (and .cse45 .cse46 .cse17 .cse33) .cse38)) (.cse43 (ite .cse19 (or .cse42 .cse20) .cse17)) (.cse41 (ite .cse44 (or .cse37 .cse40) .cse33))) (and .cse21 (or (let ((.cse39 (<= v_x0_59 0))) (and (or (and (let ((.cse30 (+ v_x1_28 1)) (.cse35 (<= 0 v_x1_28))) (or (let ((.cse25 (<= v_x1_32 v_x2_42)) (.cse31 (and (<= (+ v_x1_32 1) 0) (<= 0 v_x1_32)))) (let ((.cse24 (or .cse25 .cse31)) (.cse28 (<= v_x1_28 v_x2_42)) (.cse27 (<= x1 v_x2_42))) (and (<= v_x2_42 v_x1_28) .cse8 .cse22 .cse23 .cse1 (<= 0 v_x2_60) .cse5 .cse24 .cse13 (<= v_x1_28 0) .cse6 .cse11 .cse7 (<= v_x2_42 x1) (or (and .cse25 .cse26 .cse1 .cse27 .cse5 .cse28) (and .cse1 .cse24 .cse5)) .cse27 .cse29 .cse14 .cse9 .cse15 (or (and (<= .cse30 v_x1_32) (<= v_x1_32 v_x1_28)) (and .cse1 .cse5 (<= x1 v_x1_32) (<= v_x1_32 x1)) .cse31) .cse10 .cse12 .cse28 (<= v_x2_54 v_x2_42) (<= v_x0_46 v_x2_54) .cse32 .cse17 .cse33 .cse34 (<= v_x2_42 v_x1_32) .cse26 .cse0 (<= v_x1_41 v_x2_54) .cse2 (<= v_x1_41 v_x2_42) .cse3 .cse4 (<= v_x2_42 v_x1_41) .cse35 .cse36 (or (and .cse1 .cse5) .cse27) .cse16 (<= v_x2_42 v_x1_56)))) (and (<= .cse30 0) .cse35))) .cse37 .cse20 (or .cse38 (and .cse21 .cse34 (or (ite .cse18 (and .cse21 .cse34 .cse39 .cse17) .cse40) .cse38) .cse17)) (<= v_x3_53 0) .cse32 .cse33 .cse17 .cse41 (<= 0 v_x3_53) .cse11 .cse42 .cse7 .cse34 .cse26 .cse39 .cse29 .cse16 .cse40 .cse43 (<= v_x3_53 v_x2_54)) .cse44) .cse34 .cse39 .cse45 .cse46 .cse17 .cse33)) .cse38) (or .cse44 (and .cse42 .cse37 .cse33 .cse17)) .cse43 .cse41 .cse33 .cse17)))) .cse44))) .cse40))) .cse33 .cse17)))))) (and (<= .cse47 v_x1_41) .cse11))) .cse5 .cse36 .cse29 .cse32)) (and (<= .cse52 0) .cse22) (and (<= .cse53 0) .cse7) (ite .cse49 (ite .cse48 (ite .cse50 .cse51 .cse6) .cse32) (and (<= (+ v_x2_42 1) 0) .cse26))))))) (ite .cse2 (and (<= .cse47 0) .cse4) .cse2) (ite .cse1 (and (<= (+ x1 1) 0) .cse5) .cse1))))";
		runSimplificationTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void mcrPthreadWmm02 () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "~x~0", "~x$r_buff0_thd2~0", "~x$w_buff0_used~0", "~x$w_buff1_used~0", "~x$w_buff0~0", "~x$w_buff1~0", "~x$r_buff1_thd0~0"), };
		final String formulaAsString = "(forall ((~x$r_buff1_thd2~0 Int) (|P1Thread1of1ForFork0_#t~nondet35| Int)) (let ((.cse11 (= (mod ~x$r_buff0_thd2~0 256) 0)) (.cse19 (= (mod ~x$w_buff1_used~0 256) 0)) (.cse20 (= (mod ~x$r_buff1_thd2~0 256) 0))) (let ((.cse2 (= (mod ~x$w_buff0_used~0 256) 0)) (.cse21 (not .cse20)) (.cse18 (not .cse19)) (.cse13 (not .cse11))) (let ((.cse22 (or .cse18 .cse13)) (.cse14 (or .cse13 .cse21)) (.cse15 (not .cse2)) (.cse8 (= (mod |P1Thread1of1ForFork0_#t~nondet35| 256) 0))) (let ((.cse7 (not .cse8)) (.cse3 (and .cse11 .cse19)) (.cse4 (and .cse13 .cse15)) (.cse6 (and .cse11 .cse20)) (.cse1 (and .cse22 .cse14 .cse15))) (or (let ((.cse5 (or .cse2 .cse11))) (let ((.cse0 (let ((.cse16 (and .cse5 .cse13 .cse15))) (let ((.cse9 (let ((.cse17 (and .cse8 (or .cse7 (and (or .cse2 .cse16 .cse3 .cse6) .cse22 .cse14 .cse15))))) (and (or .cse7 (and (or (and (or .cse17 .cse4) (or .cse2 .cse11 (and (or .cse7 (and .cse18 (or .cse2 .cse19 .cse20) .cse21 .cse15)) .cse8))) .cse2 .cse3 .cse6) (or .cse17 .cse1))) (or .cse17 .cse8))))) (and (or .cse8 .cse9) (or .cse7 (and (or .cse2 .cse3 (let ((.cse10 (let ((.cse12 (and (or .cse7 (and (or .cse2 .cse16 .cse11 .cse6) .cse13 .cse14 .cse15)) .cse8))) (and (or .cse12 .cse8) (or .cse7 (and (or (and .cse5 (or .cse4 .cse12)) .cse2 .cse11 .cse6) (or .cse12 (and .cse13 .cse14 .cse15)))))))) (and (or .cse10 .cse4) (or .cse2 .cse11 .cse10))) .cse6) (or .cse1 .cse9)))))))) (and (or (and (or .cse0 .cse1) (or .cse2 .cse3 (and (or .cse4 .cse0) .cse5) .cse6)) .cse7) (or .cse0 .cse8)))) (let ((.cse25 (<= ~x$w_buff0~0 0)) (.cse26 (= 0 ~x$w_buff1~0)) (.cse27 (= ~x$r_buff1_thd0~0 0))) (let ((.cse31 (let ((.cse32 (let ((.cse33 (and (= ~x~0 1) .cse25 .cse26 .cse27))) (and (or .cse7 (and (or .cse2 .cse3 (and (or .cse33 .cse4) (or .cse2 .cse11 .cse33)) .cse6) (or .cse33 .cse1))) (or .cse33 .cse8))))) (and (or .cse7 (and (or .cse32 .cse1) (or .cse2 .cse3 (and (or .cse2 .cse11 .cse32) (or .cse4 .cse32)) .cse6))) (or .cse32 .cse8))))) (let ((.cse28 (or .cse31 .cse8))) (and (or .cse2 .cse3 (and (or .cse4 (and (or .cse7 (let ((.cse23 (let ((.cse24 (and .cse25 .cse26 (= ~x$w_buff1~0 1) .cse27))) (and (or .cse24 .cse8) (or (and (or .cse24 .cse1) (or .cse2 .cse3 (and (or .cse4 .cse24) (or .cse2 .cse11 .cse24)) .cse6)) .cse7))))) (and (or (and (or .cse1 .cse23) (or .cse2 .cse3 (and (or .cse2 .cse11 .cse23) (or .cse4 .cse23)) .cse6)) .cse7) (or .cse8 .cse23)))) .cse28)) (or .cse2 .cse11 (and (or .cse7 (let ((.cse29 (let ((.cse30 (and (= ~x$w_buff0~0 1) .cse25 .cse26 .cse27))) (and (or .cse7 (and (or .cse2 .cse3 .cse6 (and (or .cse2 .cse11 .cse30) (or .cse4 .cse30))) (or .cse30 .cse1))) (or .cse30 .cse8))))) (and (or .cse29 .cse8) (or .cse7 (and (or .cse2 .cse3 (and (or .cse2 .cse11 .cse29) (or .cse4 .cse29)) .cse6) (or .cse29 .cse1)))))) .cse28))) .cse6) (or (and (or .cse7 .cse31) .cse28) .cse1)))))))))))";
		runSimplificationTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void mcrPthreadWmm02Inner () {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "~x$r_buff1_thd2~0", "P1Thread1of1ForFork0_#t~nondet35", "~x~0", "~x$r_buff0_thd2~0", "~x$w_buff0_used~0", "~x$w_buff1_used~0", "~x$w_buff0~0", "~x$w_buff1~0", "~x$r_buff1_thd0~0"), };
		final String formulaAsString = "(let ((.cse11 (= (mod ~x$r_buff0_thd2~0 256) 0)) (.cse19 (= (mod ~x$w_buff1_used~0 256) 0)) (.cse20 (= (mod ~x$r_buff1_thd2~0 256) 0))) (let ((.cse2 (= (mod ~x$w_buff0_used~0 256) 0)) (.cse21 (not .cse20)) (.cse18 (not .cse19)) (.cse13 (not .cse11))) (let ((.cse22 (or .cse18 .cse13)) (.cse14 (or .cse13 .cse21)) (.cse15 (not .cse2)) (.cse8 (= (mod |P1Thread1of1ForFork0_#t~nondet35| 256) 0))) (let ((.cse7 (not .cse8)) (.cse3 (and .cse11 .cse19)) (.cse4 (and .cse13 .cse15)) (.cse6 (and .cse11 .cse20)) (.cse1 (and .cse22 .cse14 .cse15))) (or (let ((.cse5 (or .cse2 .cse11))) (let ((.cse0 (let ((.cse16 (and .cse5 .cse13 .cse15))) (let ((.cse9 (let ((.cse17 (and .cse8 (or .cse7 (and (or .cse2 .cse16 .cse3 .cse6) .cse22 .cse14 .cse15))))) (and (or .cse7 (and (or (and (or .cse17 .cse4) (or .cse2 .cse11 (and (or .cse7 (and .cse18 (or .cse2 .cse19 .cse20) .cse21 .cse15)) .cse8))) .cse2 .cse3 .cse6) (or .cse17 .cse1))) (or .cse17 .cse8))))) (and (or .cse8 .cse9) (or .cse7 (and (or .cse2 .cse3 (let ((.cse10 (let ((.cse12 (and (or .cse7 (and (or .cse2 .cse16 .cse11 .cse6) .cse13 .cse14 .cse15)) .cse8))) (and (or .cse12 .cse8) (or .cse7 (and (or (and .cse5 (or .cse4 .cse12)) .cse2 .cse11 .cse6) (or .cse12 (and .cse13 .cse14 .cse15)))))))) (and (or .cse10 .cse4) (or .cse2 .cse11 .cse10))) .cse6) (or .cse1 .cse9)))))))) (and (or (and (or .cse0 .cse1) (or .cse2 .cse3 (and (or .cse4 .cse0) .cse5) .cse6)) .cse7) (or .cse0 .cse8)))) (let ((.cse25 (<= ~x$w_buff0~0 0)) (.cse26 (= 0 ~x$w_buff1~0)) (.cse27 (= ~x$r_buff1_thd0~0 0))) (let ((.cse31 (let ((.cse32 (let ((.cse33 (and (= ~x~0 1) .cse25 .cse26 .cse27))) (and (or .cse7 (and (or .cse2 .cse3 (and (or .cse33 .cse4) (or .cse2 .cse11 .cse33)) .cse6) (or .cse33 .cse1))) (or .cse33 .cse8))))) (and (or .cse7 (and (or .cse32 .cse1) (or .cse2 .cse3 (and (or .cse2 .cse11 .cse32) (or .cse4 .cse32)) .cse6))) (or .cse32 .cse8))))) (let ((.cse28 (or .cse31 .cse8))) (and (or .cse2 .cse3 (and (or .cse4 (and (or .cse7 (let ((.cse23 (let ((.cse24 (and .cse25 .cse26 (= ~x$w_buff1~0 1) .cse27))) (and (or .cse24 .cse8) (or (and (or .cse24 .cse1) (or .cse2 .cse3 (and (or .cse4 .cse24) (or .cse2 .cse11 .cse24)) .cse6)) .cse7))))) (and (or (and (or .cse1 .cse23) (or .cse2 .cse3 (and (or .cse2 .cse11 .cse23) (or .cse4 .cse23)) .cse6)) .cse7) (or .cse8 .cse23)))) .cse28)) (or .cse2 .cse11 (and (or .cse7 (let ((.cse29 (let ((.cse30 (and (= ~x$w_buff0~0 1) .cse25 .cse26 .cse27))) (and (or .cse7 (and (or .cse2 .cse3 .cse6 (and (or .cse2 .cse11 .cse30) (or .cse4 .cse30))) (or .cse30 .cse1))) (or .cse30 .cse8))))) (and (or .cse29 .cse8) (or .cse7 (and (or .cse2 .cse3 (and (or .cse2 .cse11 .cse29) (or .cse4 .cse29)) .cse6) (or .cse29 .cse1)))))) .cse28))) .cse6) (or (and (or .cse7 .cse31) .cse28) .cse1))))))))))";
		runSimplificationTest(funDecls, formulaAsString, null, true, mServices, mLogger, mMgdScript);
	}

	@Test
	public void missingConjuncts() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x"), };
		final String formulaAsString = "(and (<= x 11) (not (= (+ x (- 2)) 0)) (<= 11 x))";
		final String simplified = "(and (<= x 11) (<= 11 x))";
		runSimplificationTest(funDecls, formulaAsString, simplified, true, mServices, mLogger, mMgdScript);
	}

	static void runSimplificationTest(final FunDecl[] funDecls, final String eliminationInputAsString, final String expectedResultAsString,
			final boolean checkResultIsQuantifierFree, final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript) {
		for (final FunDecl funDecl : funDecls) {
			funDecl.declareFuns(mgdScript.getScript());
		}
		final Term formulaAsTerm = TermParseUtils.parseTerm(mgdScript.getScript(), eliminationInputAsString);
		final Term letFree = new FormulaUnLet().transform(formulaAsTerm);
		final Term unf = new UnfTransformer(mgdScript.getScript()).transform(letFree);
		final Term nnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP).transform(unf);

		final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(mgdScript, letFree, services, SimplificationTechnique.POLY_PAC);
		final Term result = esr.getSimplifiedTerm();
		logger.info("Simplified result: " + esr.getSimplifiedTerm());
		logger.info(esr.buildSizeReductionMessage());
		if (expectedResultAsString != null) {
			final Term expectedResultAsTerm = TermParseUtils.parseTerm(mgdScript.getScript(), expectedResultAsString);
			Assert.assertTrue("Not syntactically equivalent to expected result: " + result, result.equals(expectedResultAsTerm));
		}
	}


}
