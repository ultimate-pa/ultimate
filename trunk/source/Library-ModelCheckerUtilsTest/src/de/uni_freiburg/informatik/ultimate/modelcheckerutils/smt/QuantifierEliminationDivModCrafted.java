/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierEliminationDivModCrafted {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY = false;
	private static final boolean CHECK_SIMPLIFICATION_POSSIBILITY = false;
	private static final long TEST_TIMEOUT_MILLISECONDS = 10_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final LogLevel LOG_LEVEL_SOLVER = LogLevel.INFO;
//	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:1000 -memory:2024 -smt2 -in";
//	private static final String SOLVER_COMMAND = "smtinterpol -q";
	private static final String SOLVER_COMMAND = "cvc5 --incremental --lang smt --tlimit-per=1000";

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private static QuantifierEliminationTestCsvWriter mCsvWriter;

	@BeforeClass
	public static void beforeAllTests() {
		mCsvWriter = new QuantifierEliminationTestCsvWriter(QuantifierEliminationDivMod.class.getSimpleName());
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

		final Script solverInstance = new HistoryRecordingScript(
				UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL_SOLVER));
		if (WRITE_SMT_SCRIPTS_TO_FILE) {
			mScript = new LoggingScript(solverInstance, "QuantifierEliminationTest.smt2", true);
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

	//@formatter:off


	@Test
	public void divCisternPositiveExists01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (= c (div (+ x e) 100)) (<= d x)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternPositiveExists02() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (= c (div (+ x e) 100)) (>= d x)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternNegativeExists01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (= c (div (+ x e) (- 100))) (<= d x)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternNegativeExists02() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (= c (div (+ x e) (- 100))) (>= d x)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternPositiveForall01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(forall ((x Int)) (or (not (= c (div (+ x e) 100))) (> d x)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternPositiveForall02() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(forall ((x Int)) (or (not (= c (div (+ x e) 100))) (< d x)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternNegativeForall01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(forall ((x Int)) (or (not (= c (div (+ x e) (- 100)))) (> d x)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternNegativeForall02() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(forall ((x Int)) (or (not (= c (div (+ x e) (- 100)))) (< d x)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void divFountainPositiveExists() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (= c (div (* 3 x) 100)) (<= d x)))";
		final String expectedResult = "(exists ((v_z_1 Int) (v_y_1 Int)) (and (<= d (+ (* v_y_1 100) (* 67 v_z_1))) (= c (+ (* 2 v_z_1) (* 3 v_y_1))) (<= 0 v_z_1) (< v_z_1 100)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void divElim14() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((v1 Int)) (and (not (= c (div v1 256))) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim20() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((v1 Int)) (and (not (= c (div v1 (- 256)))) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim15() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((v1 Int)) (and (= c (div v1 256)) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((v1 Int)) (and (not (= c (div (* 15 v1) 256))) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim18() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((v1 Int)) (and (= c (div (* 15 v1) 256)) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim19() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((v1 Int)) (and (= c (div (* (- 3) v1) 256)) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void divElim4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(forall ((v1 Int)) (or (not (<= v1 127)) (not (= c (div v1 256))) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(forall ((v1 Int)) (or (<= v1 127) (not (= c (div v1 256)))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(forall ((v1 Int)) (or (<= v1 127) (= c (div v1 256))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim12() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(forall ((v1 Int)) (or (not (<= v1 127)) (= c (div v1 256)) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(forall ((v1 Int)) (or (not (<= v1 127)) (not (= c (div (* 15 v1) 256))) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(forall ((v1 Int)) (or (not (<= v1 127)) (not (= c (div (* 233 v1) 19))) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(forall ((v1 Int)) (or (<= v1 127) (= c (div (+ v1 5) 256))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(forall ((v1 Int)) (or (not (<= v1 127)) (not (= c (div (+ v1 5) 256))) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	//@formatter:on
}