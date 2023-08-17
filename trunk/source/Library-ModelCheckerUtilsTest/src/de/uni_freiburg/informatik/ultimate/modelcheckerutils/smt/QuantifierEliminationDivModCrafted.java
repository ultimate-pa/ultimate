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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.StatisticsScript;
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
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:1000 -memory:2024 -smt2 -in";
//	private static final String SOLVER_COMMAND = "smtinterpol -q";
//	private static final String SOLVER_COMMAND = "cvc5 --incremental --lang smt --tlimit-per=1000";

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
		mScript = new StatisticsScript(mScript);

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
	public void crispbreadModulo01() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "y"), };
		final String formulaAsString = "(exists ((x Int)) (= y (mod (* 3 x) 256)))";
		final String expectedResult = "(and (< y 256) (<= 0 y))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void crispbreadModulo02() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "y"), };
		final String formulaAsString = "(and (exists ((x Int))	(and (< x 128) (<= 0 x) (= y (mod (* 3 x) 256)))) (< y 256) (<= 0 y))";
		final String expectedResult = "(and (<= 0 y) (< y 256) (<= (+ (* 171 y) (* (div (+ (- 1) (* y (- 171))) 256) 256) 129) 0))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor04Triathlon1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "i", "b"), };
		final String formulaAsString = "(forall ((diva Int) (moda Int)) (or (<= 4294967296 (+ (* 4294967296 diva) moda)) (and (< 0 (mod (+ (* b 4294967295) moda) 4294967296)) (<= (mod (+ (* b 4294967295) moda) 4294967296) 1)) (> 0 moda) (>= moda 4294967296) (<= (+ (* 4294967296 diva) moda) (mod i 4294967296)) (< (mod (+ i 1) 4294967296) moda) (< (+ (* 4294967296 diva) moda) 0)))";
		final String expectedResult = "(let ((.cse0 (mod (* b 4294967295) 4294967296)) (.cse3 (mod i 4294967296))) (let ((.cse1 (+ .cse0 .cse3)) (.cse2 (+ .cse0 (mod (+ i 1) 4294967296)))) (and (or (< (+ (* (div (+ (- 1) .cse0) 4294967296) 4294967296) 4294967295) .cse1) (< .cse2 (+ (* (div (+ .cse0 (- 4294967297)) 4294967296) 4294967296) 8589934592))) (< .cse2 4294967298) (or (< 4294967294 .cse1) (< .cse2 (+ (* (div (+ .cse3 (- 4294967295)) 4294967296) 4294967296) 4294967298))))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor04Triathlon2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "i", "b"), };
		final String formulaAsString = "(forall ((diva Int) (moda Int)) (or (<= 4294967296 (+ (* 4294967296 diva) moda)) (<= (mod (+ (* b 4294967295) moda) 4294967296) 1)  (<= (+ (* 4294967296 diva) moda) (mod i 4294967296)) (< (+ (* 4294967296 diva) moda) 0)))";
		final String expectedResult = "(let ((.cse0 (mod i 4294967296))) (or (< 4294967294 .cse0) (let ((.cse1 (* b 4294967295))) (< (+ 4294967294 (* 4294967296 (div (+ .cse1 4294967293) 4294967296))) (+ .cse0 .cse1)))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor04Triathlon3() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "i", "b"), };
		final String formulaAsString = "(forall ((diva Int) (aux_mod_moda_42 Int) (aux_div_moda_42 Int)) (or (> 0 aux_mod_moda_42) (<= aux_mod_moda_42 1) (<= (+ (* 4294967295 b) 4294967296) (+ (* 4294967296 diva) aux_mod_moda_42 (* 4294967296 aux_div_moda_42))) (>= aux_mod_moda_42 4294967296) (<= (+ (* 4294967296 diva) aux_mod_moda_42 (* 4294967296 aux_div_moda_42)) (+ (* 4294967295 b) (mod i 4294967296))) (< (+ (* 4294967296 diva) aux_mod_moda_42 (* 4294967296 aux_div_moda_42)) (* 4294967295 b))))";
		final String expectedResult = "(let ((.cse0 (mod i 4294967296))) (or (< 4294967294 .cse0) (let ((.cse1 (* b 4294967295))) (< (+ 4294967294 (* 4294967296 (div (+ .cse1 4294967293) 4294967296))) (+ .cse0 .cse1)))))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void choirNightTrezor04Triathlon4() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "b"), };
		final String formulaAsString = "(forall ((x Int)) (<= (+ (* 7 b) 8) (* 8 x))))";
		final String expectedResult = "false";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Minimal formula that revealed bug in `div` elimination.
	 */
	@Test
	public void qeDivMod87C893B3Bug() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (= c (div (+ x 1) 100)) (<= x 99)))";
		final String expectedResult = "(<= c 1)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternPositiveExists01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (= c (div (+ x e) 100)) (<= d x)))";
		final String expectedResult = "(<= (+ e d) (+ (* c 100) 99))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternPositiveExists02() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (= c (div (+ x e) 100)) (>= d x)))";
		final String expectedResult = "(<= (* c 100) (+ e d))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternNegativeExists01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (= c (div (+ x e) (- 100))) (<= d x)))";
		final String expectedResult = "(<= (+ e d (* c 100)) 99)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternNegativeExists02() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (= c (div (+ x e) (- 100))) (>= d x)))";
		final String expectedResult = "(<= 0 (+ e d (* c 100)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternPositiveForall01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(forall ((x Int)) (or (not (= c (div (+ x e) 100))) (> d x)))";
		final String expectedResult = "(< (+ (* c 100) 99) (+ e d))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternPositiveForall02() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(forall ((x Int)) (or (not (= c (div (+ x e) 100))) (< d x)))";
		final String expectedResult = "(< (+ e d) (* c 100))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternNegativeForall01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(forall ((x Int)) (or (not (= c (div (+ x e) (- 100)))) (> d x)))";
		final String expectedResult = "(< 99 (+ e d (* c 100)))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divCisternNegativeForall02() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d", "e"),
		};
		final String formulaAsString = "(forall ((x Int)) (or (not (= c (div (+ x e) (- 100)))) (< d x)))";
		final String expectedResult = "(< (+ e d (* c 100)) 0)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divFountainPositiveExists() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c", "d"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (= c (div (* 3 x) 100)) (<= d x)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
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
		final String expectedResult = "(<= (+ c 1) 0)";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((v1 Int)) (and (not (= c (div (* 15 v1) 256))) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim18() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((v1 Int)) (and (= c (div (* 15 v1) 256)) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim19() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((v1 Int)) (and (= c (div (* (- 3) v1) 256)) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
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
		final String expectedResult = "(< c 0)"; //checked with CVC5
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
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void divElim6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(forall ((v1 Int)) (or (not (<= v1 127)) (not (= c (div (* 233 v1) 19))) (< v1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
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

	@Test
	public void honigbuck01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(forall ((|v1| Int) (|v2| Int) (|v3| Int)) (or (< (mod (mod |v3| 256) 4294967296) (* |v1| 256)) (<= (+ (* |v1| 256) 256) (mod (mod |v3| 256) 4294967296)) (= (mod (mod |v3| 256) 4294967296) (+ (* |v1| 256) (* 4294967296 |v2|))) (<= (+ (* |v1| 256) 4294967296 (* 4294967296 |v2|)) (mod (mod |v3| 256) 4294967296)) (< (mod (mod |v3| 256) 4294967296) (+ (* |v1| 256) (* 4294967296 |v2|))) (and (or (<= (mod (mod |v3| 256) 4294967296) 2147483647) (<= (mod (mod |c| 256) 4294967296) 2147483647) (not (= (mod (mod |v3| 256) 4294967296) (mod (mod |c| 256) 4294967296)))) (or (not (<= (mod (mod |c| 256) 4294967296) 2147483647)) (not (<= (mod (mod |v3| 256) 4294967296) 2147483647)) (not (= (mod (mod |v3| 256) 4294967296) (mod (mod |c| 256) 4294967296)))))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void honigbuck02() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((v2 Int) (v3 Int) (v1 Int)) (let ((.cse1 (* 256 v1)) (.cse2 (* v2 4294967296))) (let ((.cse3 (+ .cse1 .cse2)) (.cse0 (mod (mod v3 256) 4294967296))) (and (< .cse0 (+ .cse1 .cse2 4294967296)) (<= .cse1 .cse0) (not (= .cse3 .cse0)) (< .cse0 (+ .cse1 256)) (let ((.cse5 (mod (mod c 256) 4294967296))) (let ((.cse4 (= .cse5 .cse0))) (or (and .cse4 (< 2147483647 .cse5) (< 2147483647 .cse0)) (and .cse4 (<= .cse5 2147483647) (<= .cse0 2147483647))))) (<= .cse3 .cse0)))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void honigbuck03() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "c"),
		};
		final String formulaAsString = "(exists ((v2 Int) (v3 Int) (v1 Int)) (let ((.cse1 (* 256 v1)) (.cse2 (* v2 4294967296))) (let ((.cse3 (+ .cse1 .cse2)) (.cse0 (mod (mod v3 256) 4294967296))) (and (< .cse0 (+ .cse1 .cse2 4294967296)) (<= .cse1 .cse0) (not (= .cse3 .cse0)) (< .cse0 (+ .cse1 256)) (let ((.cse5 (mod (mod c 256) 4294967296))) (let ((.cse4 (= .cse5 .cse0))) (or (and .cse4 (< 2147483647 .cse5) (< 2147483647 .cse0)) (and .cse4 (<= .cse5 2147483647)))))))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvToIntLynxForall() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "n", "m"),
		};
		final String formulaAsString = "(forall ((x Int)) (or (<= (+ (* (mod m 128) 2) (mod x 256)) (+ (mod m 256) (* (mod x 128) 2))) (<= (+ (mod x 256) (* 2 (mod n 128))) (+ (* (mod x 128) 2) (mod n 256)))))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvToIntLynxExists() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "n", "m"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (> (+ (* (mod m 128) 2) (mod x 256)) (+ (mod m 256) (* (mod x 128) 2))) (> (+ (mod x 256) (* 2 (mod n 128))) (+ (* (mod x 128) 2) (mod n 256)))))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvToIntFoxForall01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "n", "m"),
		};
		final String formulaAsString = "(forall ((x Int)) (or (<= (mod x 256) (+ m (* (mod x 128) 2))) (<= (mod x 256) (+ (* (mod x 128) 2) n))))";
		final String expectedResultAsString = "(or (< 127 n) (< 127 m))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvToIntFoxExists01() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "n", "m"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (> (mod x 256) (+ m (* (mod x 128) 2))) (> (mod x 256) (+ (* (mod x 128) 2) n))))";
		final String expectedResultAsString = "(and (<= n 127) (<= m 127))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvToIntFoxForall02() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "n", "m"),
		};
		final String formulaAsString = "(forall ((x Int)) (or (>= x 256) (>= (+ (* 2 (mod x 128)) n) (mod x 256)) (> 0 x) (>= (+ m (* 2 (mod x 128))) x)))";
		final String expectedResultAsString = "(or (< 127 n) (< 127 m))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvToIntFoxExists02() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "n", "m"),
		};
		final String formulaAsString = "(exists ((x Int)) (and (< x 256) (< (+ (* 2 (mod x 128)) n) (mod x 256)) (<= 0 x) (< (+ m (* 2 (mod x 128))) x)))";
		final String expectedResultAsString = "(and (<= n 127) (<= m 127))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvToIntFoxForall03() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "n", "m"),
		};
		final String formulaAsString = "(forall ((x Int) (u Int)) (or (>= (+ x (* u 128)) 256) (> 0 x) (>= (+ m x) (* u 128)) (>= (+ (* 2 (mod x 128)) n) (mod (+ x (* u 128)) 256)) (>= x 128) (> 0 (+ x (* u 128)))))";
		final String expectedResultAsString = "(or (< 127 n) (< 127 m))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvToIntFoxExists03() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "n", "m"),
		};
		final String formulaAsString = "(exists ((x Int) (u Int)) (and (< (+ x (* u 128)) 256) (<= 0 x) (< (+ m x) (* u 128)) (< (+ (* 2 (mod x 128)) n) (mod (+ x (* u 128)) 256)) (< x 128) (<= 0 (+ x (* u 128)))))";
		final String expectedResultAsString = "(and (<= n 127) (<= m 127))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvToIntFoxForall04() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "n", "m"),
		};
		final String formulaAsString = "(forall ((v Int) (u Int) (x Int)) (or (> 0 (+ (* 256 v) (* u 128) x)) (>= x 256) (> 0 (+ (* 256 v) x)) (> 0 x) (and (or (>= (+ (* 2 (mod x 128)) n) (+ x (* (mod u 2) 128))) (>= (+ x (* (mod u 2) 128)) 256)) (or (> 256 (+ x (* (mod u 2) 128))) (>= (+ (* 2 (mod x 128)) 256 n) (+ x (* (mod u 2) 128))))) (>= (+ m (* 256 v) x) (* u 128)) (>= (+ (* 256 v) x) 128) (>= (+ (* 256 v) (* u 128) x) 256)))";
		final String expectedResultAsString = "(or (< 127 n) (< 127 m))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvToIntFoxExists04() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "n", "m"),
		};
		final String formulaAsString = "(exists ((v Int) (u Int) (x Int)) (and (<= 0 (+ (* 256 v) (* u 128) x)) (< x 256) (<= 0 (+ (* 256 v) x)) (<= 0 x) (or (and (< (+ (* 2 (mod x 128)) n) (+ x (* (mod u 2) 128))) (< (+ x (* (mod u 2) 128)) 256)) (and (<= 256 (+ x (* (mod u 2) 128))) (< (+ (* 2 (mod x 128)) 256 n) (+ x (* (mod u 2) 128))))) (< (+ m (* 256 v) x) (* u 128)) (< (+ (* 256 v) x) 128) (< (+ (* 256 v) (* u 128) x) 256)))";
		final String expectedResultAsString = "(and (<= n 127) (<= m 127))";
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	//@formatter:on
}