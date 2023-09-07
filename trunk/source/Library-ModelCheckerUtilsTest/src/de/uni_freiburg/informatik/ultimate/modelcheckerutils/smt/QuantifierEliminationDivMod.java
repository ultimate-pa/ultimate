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
public class QuantifierEliminationDivMod {

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
	public void qeMod983DF698() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((aux_div_aux_mod_ULTIMATE.start_main_~b~5_38_43 Int)) (and (< (* aux_div_aux_mod_ULTIMATE.start_main_~b~5_38_43 2) 2) (not (= 3 (mod (+ 3 (* 4294967290 aux_div_aux_mod_ULTIMATE.start_main_~b~5_38_43)) 4294967296))) (<= 0 (* aux_div_aux_mod_ULTIMATE.start_main_~b~5_38_43 2))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod8A1BCADA() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((aux_div_ULTIMATE.start_main_~y~5_38 Int)) (= (mod (+ 4294967295 (* 2 aux_div_ULTIMATE.start_main_~y~5_38)) 4294967296) 0))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModE688E331() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start___VERIFIER_assert_~cond"),
		};
		final String formulaAsString = "(exists ((ULTIMATE.start_main_~z~5 Int) (ULTIMATE.start_main_~y~5 Int) (aux_div_ULTIMATE.start_main_~x~5_32 Int)) (and (or (and (not (= (mod (+ ULTIMATE.start_main_~z~5 ULTIMATE.start_main_~y~5 (* aux_div_ULTIMATE.start_main_~x~5_32 4)) 4294967296) 1)) (= 1 ULTIMATE.start___VERIFIER_assert_~cond)) (and (= (mod (+ ULTIMATE.start_main_~z~5 ULTIMATE.start_main_~y~5 (* aux_div_ULTIMATE.start_main_~x~5_32 4)) 4294967296) 1) (= 0 ULTIMATE.start___VERIFIER_assert_~cond))) (= (mod (* ULTIMATE.start_main_~y~5 3) 4) 0) (= (mod (* ULTIMATE.start_main_~z~5 7) 8) 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModAC3DF136() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start___VERIFIER_assert_~cond"),
		};
		final String formulaAsString = "(exists ((ULTIMATE.start_main_~y~5 Int) (ULTIMATE.start_main_~z~5 Int) (aux_div_ULTIMATE.start_main_~x~5_32 Int)) (and (= (mod (* ULTIMATE.start_main_~y~5 3) 4) 0) (= (mod (* ULTIMATE.start_main_~z~5 7) 8) 0) (or (and (not (= 4 (mod (+ (* ULTIMATE.start_main_~y~5 2) ULTIMATE.start_main_~z~5 (* 8 aux_div_ULTIMATE.start_main_~x~5_32)) 4294967296))) (= 1 ULTIMATE.start___VERIFIER_assert_~cond)) (and (= 4 (mod (+ (* ULTIMATE.start_main_~y~5 2) ULTIMATE.start_main_~z~5 (* 8 aux_div_ULTIMATE.start_main_~x~5_32)) 4294967296)) (= 0 ULTIMATE.start___VERIFIER_assert_~cond)))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod5C13FE76() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start___VERIFIER_assert_~cond"),
		};
		final String formulaAsString = "(exists ((ULTIMATE.start_main_~z~5 Int) (ULTIMATE.start_main_~y~5 Int) (ULTIMATE.start_main_~x~5 Int)) (and (= (mod (* ULTIMATE.start_main_~z~5 4194303) 4194304) 0) (= (mod (* ULTIMATE.start_main_~x~5 1048575) 1048576) 0) (or (and (= 1 ULTIMATE.start___VERIFIER_assert_~cond) (not (= (mod (+ ULTIMATE.start_main_~z~5 (* ULTIMATE.start_main_~y~5 4294967294) (* ULTIMATE.start_main_~x~5 4)) 4294967296) 1048576))) (and (= 0 ULTIMATE.start___VERIFIER_assert_~cond) (= (mod (+ ULTIMATE.start_main_~z~5 (* ULTIMATE.start_main_~y~5 4294967294) (* ULTIMATE.start_main_~x~5 4)) 4294967296) 1048576))) (= (mod (* 2097151 ULTIMATE.start_main_~y~5) 2097152) 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod33825C1E() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((~p1_old Int) (~send1 Int)) (and (= ~p1_old (mod ~send1 256)) (<= (mod ~send1 256) 127)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod824A9EA1() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((~alive1 Int)) (= (mod ~alive1 256) 0))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod8DD1F76C() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((ULTIMATE.start_ssl3_connect_~__cil_tmp56~4 Int)) (= (mod (+ ULTIMATE.start_ssl3_connect_~__cil_tmp56~4 18446744073709551360) 18446744073709551616) 0))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod8282A8D6() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((ULTIMATE.start_ssl3_connect_~__cil_tmp64~4 Int)) (= (mod (+ ULTIMATE.start_ssl3_connect_~__cil_tmp64~4 256) 18446744073709551616) 0))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void qeDivModE208D894() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "main_a"),
			new FunDecl(SmtSortUtils::getIntSort, "main_p", "main_q"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_4 Int) (v_arrayElimCell_3 Int)) (and (= (select main_a main_p) (mod (+ v_arrayElimCell_4 (div v_arrayElimCell_3 2)) 4294967296)) (or (= main_q main_p) (= v_arrayElimCell_4 (select main_a main_q))) (or (not (= main_q main_p)) (= v_arrayElimCell_4 v_arrayElimCell_3)) (<= 0 v_arrayElimCell_4) (or (= main_q main_p) (<= v_arrayElimCell_4 500)) (= v_arrayElimCell_3 1000)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod58B32222() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((aux_div_main_yold_19 Int) (main_x Int) (aux_div_main_xold_25 Int) (main_a (Array Int Int))) (and (= (select main_a (+ (- 1) main_x (* 256 aux_div_main_xold_25))) (select main_a (mod (+ main_x 1) 256))) (= (select main_a main_x) (select main_a (+ (- 1) main_x (* 256 aux_div_main_xold_25)))) (<= 1 (+ main_x (* 256 aux_div_main_xold_25))) (< (+ main_x (* 256 aux_div_main_xold_25)) 257) (= (select main_a (+ (- 1) main_x (* 256 aux_div_main_xold_25))) (select main_a (+ (* 256 aux_div_main_yold_19) (- 2) main_x (* 256 aux_div_main_xold_25)))) (= (select main_a main_x) 0) (<= 0 main_x) (< main_x 256) (= (select main_a (+ (- 1) main_x (* 256 aux_div_main_xold_25))) 1000)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModF7E66B88() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "aux_mod_v_main_~x~0_19_31", "main_~x~0", "main_~y~0"),
		};
		final String formulaAsString = "(exists ((aux_div_v_main_~x~0_19_31 Int)) (and (= (mod (+ aux_mod_v_main_~x~0_19_31 aux_div_v_main_~x~0_19_31) 3) 0) (or (and (= (div (+ aux_mod_v_main_~x~0_19_31 (* aux_div_v_main_~x~0_19_31 4294967296)) 3) 1) (= (div (+ (- (div (+ (- main_~y~0) 1) 2)) 1) 2) 1)) (and (= 3 (div (+ aux_mod_v_main_~x~0_19_31 (* aux_div_v_main_~x~0_19_31 4294967296)) 3)) (= (+ (div (+ (- (div (+ (- main_~y~0) 1) 2)) 1) 2) 1) 0))) (= (+ (* aux_mod_v_main_~x~0_19_31 3) (* aux_div_v_main_~x~0_19_31 12884901888)) main_~x~0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModFE53C0DD() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_6| Int)) (= (mod (* 16777215 |v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_6|) 16777216) 0))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod619EF237() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_23| Int)) (= (mod (* |v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_23| 16777215) 16777216) 0))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModE2840B20() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~p1_new~0", "~id3~0", "~nomsg~0"),
		};
		final String formulaAsString = "(exists ((~send1~0 Int)) (and (<= (mod ~send1~0 256) 127) (<= ~send1~0 127) (= ~p1_new~0 (mod ~send1~0 256)) (not (= ~send1~0 ~id3~0)) (not (= ~send1~0 ~nomsg~0)) (<= 0 ~send1~0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod2CD67151() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~nomsg~0", "~p4_new~0"),
		};
		final String formulaAsString = "(exists ((~send4~0 Int)) (and (not (<= (mod ~send4~0 256) 127)) (<= 0 ~send4~0) (<= ~send4~0 127) (or (and (not (= ~send4~0 ~nomsg~0)) (= (+ ~p4_new~0 256) (mod ~send4~0 256))) (and (= ~p4_new~0 (mod ~nomsg~0 256)) (= ~send4~0 ~nomsg~0)))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModF0164ADC() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~p1_new~0", "~nomsg~0"),
		};
		final String formulaAsString = "(exists ((~send1~0 Int)) (and (<= ~send1~0 127) (not (= ~send1~0 ~nomsg~0)) (<= (mod ~send1~0 256) (+ 256 ~p1_new~0)) (not (<= (mod ~send1~0 256) 127)) (<= 0 ~send1~0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModC4A49E94() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~var_23~0#1| Int)) (and (<= 0 |ULTIMATE.start_main_~var_23~0#1|) (= (mod |ULTIMATE.start_main_~var_23~0#1| 256) 0) (< |ULTIMATE.start_main_~var_23~0#1| 256)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDivBA566C0() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~n~0#1| Int)) (and (or (not (< |ULTIMATE.start_main_~n~0#1| 0)) (= (mod |ULTIMATE.start_main_~n~0#1| 2) 0)) (<= 1 (div |ULTIMATE.start_main_~n~0#1| 2))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModEDB1EF13() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "aux_mod_ULTIMATE.start_main_~z~0#1_45"),
		};
		final String formulaAsString = "(exists ((|aux_mod_ULTIMATE.start_main_~n~0#1_45| Int)) (and (not (= (mod |aux_mod_ULTIMATE.start_main_~n~0#1_45| 4294967296) (mod |aux_mod_ULTIMATE.start_main_~z~0#1_45| 4294967296))) (<= |aux_mod_ULTIMATE.start_main_~n~0#1_45| 0) (<= 0 |aux_mod_ULTIMATE.start_main_~n~0#1_45|)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModA007BB5B() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_student_version_~w#1"),
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~w~0#1| Int)) (and (not (<= (mod |ULTIMATE.start_main_~w~0#1| 4294967296) 2147483647)) (or (and (<= |ULTIMATE.start_student_version_~w#1| (mod |ULTIMATE.start_main_~w~0#1| 4294967296)) (<= (mod |ULTIMATE.start_main_~w~0#1| 4294967296) 2147483647)) (and (not (<= (mod |ULTIMATE.start_main_~w~0#1| 4294967296) 2147483647)) (<= (+ |ULTIMATE.start_student_version_~w#1| 4294967296) (mod |ULTIMATE.start_main_~w~0#1| 4294967296))))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModB61935DD() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~p2_new~0"),
		};
		final String formulaAsString = "(exists ((~send2~0 Int)) (and (<= (mod ~send2~0 256) 127) (<= 0 ~send2~0) (<= ~send2~0 127) (= (mod ~send2~0 256) ~p2_new~0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModE5BC6CE6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~p5_old~0"),
		};
		final String formulaAsString = "(exists ((~send5~0 Int)) (and (<= 0 ~send5~0) (not (<= (mod ~send5~0 256) 127)) (<= ~send5~0 127) (= (+ 256 ~p5_old~0) (mod ~send5~0 256))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModFD34F53D() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~p6_new~0"),
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~node6____CPAchecker_TMP_0~0#1| Int)) (and (<= |ULTIMATE.start_main_~node6____CPAchecker_TMP_0~0#1| 127) (= (mod |ULTIMATE.start_main_~node6____CPAchecker_TMP_0~0#1| 256) ~p6_new~0) (<= 0 |ULTIMATE.start_main_~node6____CPAchecker_TMP_0~0#1|) (<= (mod |ULTIMATE.start_main_~node6____CPAchecker_TMP_0~0#1| 256) 127)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModC0B8F0E9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~send4~0", "~p4_new~0"),
		};
		final String formulaAsString = "(exists ((~nomsg~0 Int)) (and (or (and (not (<= (mod ~send4~0 256) 127)) (or (and (not (= ~send4~0 ~nomsg~0)) (= (+ ~p4_new~0 256) (mod ~send4~0 256))) (and (= (mod ~nomsg~0 256) (+ ~p4_new~0 256)) (= ~send4~0 ~nomsg~0)))) (and (<= (mod ~send4~0 256) 127) (or (and (not (= ~send4~0 ~nomsg~0)) (= ~p4_new~0 (mod ~send4~0 256))) (and (= (mod ~nomsg~0 256) (+ ~p4_new~0 256)) (= ~send4~0 ~nomsg~0))))) (not (<= (mod ~nomsg~0 256) 127))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void qeDivB1B0C54E() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(forall ((main_eat Int)) (or (< 0 (+ (div main_eat 2) 1)) (not (<= 0 main_eat))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod52A6DC5F() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~N~0", "ULTIMATE.start_main_~ret~0#1", "ULTIMATE.start_main_~temp~0#1", "ULTIMATE.start_main_~ret2~0#1"),
		};
		final String formulaAsString = "(forall ((v_arrayElimCell_13 Int)) (or (and (or (and (= (mod v_arrayElimCell_13 4294967296) (+ |ULTIMATE.start_main_~ret~0#1| 4294967296)) (not (= (* ~N~0 4) 8))) (and (= (mod |ULTIMATE.start_main_~temp~0#1| 4294967296) (+ |ULTIMATE.start_main_~ret~0#1| 4294967296)) (= (* ~N~0 4) 8))) (= |ULTIMATE.start_main_~ret2~0#1| |ULTIMATE.start_main_~ret~0#1|)) (<= (mod v_arrayElimCell_13 4294967296) 2147483647)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod929FEB0F() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~j~1#1"),
		};
		final String formulaAsString = "(forall ((|aux_mod_ULTIMATE.start_main_~a_len~0#1_49| Int)) (or (>= |aux_mod_ULTIMATE.start_main_~a_len~0#1_49| 4294967296) (> 0 |aux_mod_ULTIMATE.start_main_~a_len~0#1_49|) (<= |aux_mod_ULTIMATE.start_main_~a_len~0#1_49| (mod |ULTIMATE.start_main_~j~1#1| 4294967296)) (< 0 (mod |aux_mod_ULTIMATE.start_main_~a_len~0#1_49| 4294967296))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModD93B9359() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~nomsg~0"),
		};
		final String formulaAsString = "(forall ((v_~send2~0_11 Int)) (or (not (<= v_~send2~0_11 127)) (not (= ~nomsg~0 (mod v_~send2~0_11 256))) (< v_~send2~0_11 (+ ~nomsg~0 1)) (not (<= (mod v_~send2~0_11 256) 127))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod4F2FEFB7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~nomsg~0"),
		};
		final String formulaAsString = "(forall ((v_~id1~0_21 Int)) (or (not (<= 0 v_~id1~0_21)) (not (= ~nomsg~0 (mod v_~id1~0_21 256))) (not (<= v_~id1~0_21 127))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDivB4D9651E() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~a1~0"),
		};
		final String formulaAsString = "(forall ((v_~a1~0_354 Int)) (or (not (<= (mod ~a1~0 299993) (+ v_~a1~0_354 600000))) (< 0 (+ (div v_~a1~0_354 5) 449596))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod34DEADF0() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.base", "ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.offset", "ULTIMATE.start_Id_MCDC_99_~Id_MCDC_140~0#1"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_193 (Array Int Int))) (or (not (< (mod (select v_ArrVal_193 (+ 3 |ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.offset|)) 4294967296) (mod (select v_ArrVal_193 (+ 2 |ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.offset|)) 4294967296))) (and (or (not (= v_ArrVal_193 (store (select |#memory_int| |ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.base|) (+ (mod |ULTIMATE.start_Id_MCDC_99_~Id_MCDC_140~0#1| 4294967296) |ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.offset|) 1))) (not (<= (mod |ULTIMATE.start_Id_MCDC_99_~Id_MCDC_140~0#1| 4294967296) 2147483647))) (or (not (= (store (select |#memory_int| |ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.base|) (+ (mod |ULTIMATE.start_Id_MCDC_99_~Id_MCDC_140~0#1| 4294967296) (- 4294967296) |ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.offset|) 1) v_ArrVal_193)) (<= (mod |ULTIMATE.start_Id_MCDC_99_~Id_MCDC_140~0#1| 4294967296) 2147483647)))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod80C1F76C() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~this_expect~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~P1~0#1| Int)) (or (and (or (not (= (mod |ULTIMATE.start_main_~P1~0#1| 2) (mod |ULTIMATE.start_main_~this_expect~0#1| 2))) (not (< |ULTIMATE.start_main_~this_expect~0#1| 0))) (or (not (= (mod |ULTIMATE.start_main_~this_expect~0#1| 2) 0)) (not (= (mod |ULTIMATE.start_main_~P1~0#1| 2) 0)))) (not (= (mod |ULTIMATE.start_main_~P1~0#1| 2) 0))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDivModF2EDFBA0() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "mult_#res", "mult_#in~n"),
		};
		final String formulaAsString = "(forall ((|v_mult_#in~n_BEFORE_CALL_31| Int)) (or (= (* 2 (div (* |v_mult_#in~n_BEFORE_CALL_31| (- 3)) (- 2))) (+ |v_mult_#in~n_BEFORE_CALL_31| |mult_#res| |mult_#in~n|)) (not (= (mod |v_mult_#in~n_BEFORE_CALL_31| 2) 0)) (not (= (+ |v_mult_#in~n_BEFORE_CALL_31| (* 2 |mult_#in~n|)) (* 2 (div (* |v_mult_#in~n_BEFORE_CALL_31| (- 3)) (- 2)))))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod880E4D55() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~nomsg~0"),
		};
		final String formulaAsString = "(forall ((v_~id1~0_36 Int)) (or (not (= (mod v_~id1~0_36 256) (+ ~nomsg~0 256))) (not (<= 0 v_~id1~0_36)) (not (<= v_~id1~0_36 127)) (<= (mod v_~id1~0_36 256) 127)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod3D87DEAE() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~nomsg~0"),
		};
		final String formulaAsString = "(forall ((v_~send4~0_265 Int)) (or (not (= (mod v_~send4~0_265 256) (+ ~nomsg~0 256))) (< v_~send4~0_265 0) (not (<= v_~send4~0_265 127)) (<= (mod v_~send4~0_265 256) 127)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod8E79A81D() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~nomsg~0"),
		};
		final String formulaAsString = "(forall ((v_~send2~0_20 Int)) (or (< v_~send2~0_20 0) (not (= (mod v_~send2~0_20 256) (+ ~nomsg~0 256))) (<= (mod v_~send2~0_20 256) 127) (not (<= v_~send2~0_20 127))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod30AF22DC() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~nomsg~0"),
		};
		final String formulaAsString = "(forall ((v_~id3~0_88 Int)) (or (not (= ~nomsg~0 (mod v_~id3~0_88 256))) (not (<= 0 v_~id3~0_88)) (not (<= (mod v_~id3~0_88 256) 127)) (not (<= v_~id3~0_88 127))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModBB56F2F2() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~nomsg~0"),
		};
		final String formulaAsString = "(forall ((v_~send2~0_15 Int)) (or (< v_~send2~0_15 (+ ~nomsg~0 1)) (not (<= v_~send2~0_15 127)) (<= (mod v_~send2~0_15 256) 127) (not (= (mod v_~send2~0_15 256) (+ ~nomsg~0 256)))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod11238817() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~nomsg~0"),
		};
		final String formulaAsString = "(forall ((v_~send4~0_11 Int)) (or (not (<= v_~send4~0_11 127)) (not (= ~nomsg~0 (mod v_~send4~0_11 256))) (< v_~send4~0_11 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void qeDivMod3A6FFDF4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "upsweep_#in~right", "upsweep_#in~left"),
		};
		final String formulaAsString = "(forall ((|aux_mod_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63| Int) (|aux_div_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63| Int)) (or (not (= (mod |aux_mod_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63| 2) 0)) (>= |aux_mod_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63| 2) (< (+ (* 2 (div |aux_mod_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63| 2)) |upsweep_#in~right|) (+ (* 2 |upsweep_#in~left|) |aux_mod_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63| 1)) (< (+ (* |aux_div_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63| 2) |aux_mod_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63|) 0) (> 0 |aux_mod_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63|) (< (+ (* |aux_div_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63| 2) |upsweep_#in~right| |aux_mod_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63|) 3) (<= 2 (+ (* |aux_div_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63| 2) |aux_mod_aux_mod_v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_8_52_63|))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void qeDivMod87C893B3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~a29~0"),
		};
		final String formulaAsString = "(exists ((v_~a29~0_897 Int)) (and (<= ~a29~0 (+ (div (+ v_~a29~0_897 (- 142312)) 5) 1)) (not (= (mod (+ 3 v_~a29~0_897) 5) 0)) (<= (+ v_~a29~0_897 127) 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Can be solved by old elimination but not by the new elimination.
	 */
	@Test
	public void qeMod3862CCBE() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~a28~0"),
		};
		final String formulaAsString = "(exists ((v_~a28~0_1300 Int)) (and (<= v_~a28~0_1300 111) (not (= (mod (+ v_~a28~0_1300 4) 5) 0)) (or (and (<= ~a28~0 (+ (div (+ (div (+ v_~a28~0_1300 (- 600036)) 5) 1) 5) 1)) (< (+ (div (+ v_~a28~0_1300 (- 600036)) 5) 1) 0) (not (= (mod (+ (div (+ v_~a28~0_1300 (- 600036)) 5) 1) 5) 0))) (and (<= ~a28~0 (div (+ (div (+ v_~a28~0_1300 (- 600036)) 5) 1) 5)) (or (not (< (+ (div (+ v_~a28~0_1300 (- 600036)) 5) 1) 0)) (= (mod (+ (div (+ v_~a28~0_1300 (- 600036)) 5) 1) 5) 0))))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

    @Test
	public void qeDivModB3099151() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 Int) (aux_div_aux_mod_ULTIMATE.start_main_~n~6_41_52 Int) (aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 Int)) (and (not (= (mod (div (mod (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63)) 18446744073709551616) 2) 18446744073709551616) 1)) (< (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_div_aux_mod_ULTIMATE.start_main_~n~6_41_52 4294967296) (* aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296)) 4294967296) (<= 1 (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_div_aux_mod_ULTIMATE.start_main_~n~6_41_52 4294967296) (* aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296))) (<= 0 (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296))) (< (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296)) 2) (< aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296) (<= 0 aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void qeMod38D95F62() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~mask_SORT_1~0#1", "ULTIMATE.start_main_~var_107~0#1"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_main_~var_141~0#1_8| Int)) (or (and (or (<= (mod (mod |ULTIMATE.start_main_~var_107~0#1| 256) 4294967296) 2147483647) (not (= (+ (mod (mod |ULTIMATE.start_main_~var_107~0#1| 256) 4294967296) |v_ULTIMATE.start_main_~var_141~0#1_8|) 4294967295))) (or (not (<= (mod (mod |ULTIMATE.start_main_~var_107~0#1| 256) 4294967296) 2147483647)) (not (= (+ (mod (mod |ULTIMATE.start_main_~var_107~0#1| 256) 4294967296) |v_ULTIMATE.start_main_~var_141~0#1_8| 1) 0)))) (not (= (mod (+ (* |v_ULTIMATE.start_main_~var_141~0#1_8| 255) |ULTIMATE.start_main_~mask_SORT_1~0#1|) 256) 0))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void qeMod5C9A1EC6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~mask_SORT_1~0#1"),
		};
		final String formulaAsString = "(forall ((|aux_div_v_ULTIMATE.start_main_#t~nondet87#1_12_50| Int) (|aux_div_aux_mod_v_ULTIMATE.start_main_#t~nondet87#1_12_50_68| Int) (|ULTIMATE.start_main_~var_131~0#1| Int)) (or (< (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) (* |aux_div_v_ULTIMATE.start_main_#t~nondet87#1_12_50| 256)) (<= (+ (* |aux_div_v_ULTIMATE.start_main_#t~nondet87#1_12_50| 256) 256) (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296)) (= (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) (+ (* |aux_div_v_ULTIMATE.start_main_#t~nondet87#1_12_50| 256) (* 4294967296 |aux_div_aux_mod_v_ULTIMATE.start_main_#t~nondet87#1_12_50_68|))) (<= (+ (* |aux_div_v_ULTIMATE.start_main_#t~nondet87#1_12_50| 256) 4294967296 (* 4294967296 |aux_div_aux_mod_v_ULTIMATE.start_main_#t~nondet87#1_12_50_68|)) (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296)) (< (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) (+ (* |aux_div_v_ULTIMATE.start_main_#t~nondet87#1_12_50| 256) (* 4294967296 |aux_div_aux_mod_v_ULTIMATE.start_main_#t~nondet87#1_12_50_68|))) (and (or (<= (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) 2147483647) (<= (mod (mod |ULTIMATE.start_main_~mask_SORT_1~0#1| 256) 4294967296) 2147483647) (not (= (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) (mod (mod |ULTIMATE.start_main_~mask_SORT_1~0#1| 256) 4294967296)))) (or (not (<= (mod (mod |ULTIMATE.start_main_~mask_SORT_1~0#1| 256) 4294967296) 2147483647)) (not (<= (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) 2147483647)) (not (= (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) (mod (mod |ULTIMATE.start_main_~mask_SORT_1~0#1| 256) 4294967296)))))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void qeDivModE3613A47() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "base2flt_#res"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_17| Int)) (or (not (< (mod (div |v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_17| 16777216) 4294967296) 256)) (and (or (not (<= (mod (div |v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_17| 16777216) 4294967296) 2147483647)) (< (mod (div |v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_17| 16777216) 4294967296) (+ (mod (div |base2flt_#res| 16777216) 4294967296) 1))) (or (<= (mod (div |base2flt_#res| 16777216) 4294967296) 2147483647) (and (not (<= (mod (div |v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_17| 16777216) 4294967296) 2147483647)) (< (mod (div |v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_17| 16777216) 4294967296) (+ (mod (div |base2flt_#res| 16777216) 4294967296) 1)))))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void qeModD7D5D9D2() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~mask_SORT_1~0#1", "ULTIMATE.start_main_~var_109~0#1"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_main_~var_139~0#1_12| Int)) (or (and (or (<= (mod (mod |ULTIMATE.start_main_~var_109~0#1| 256) 4294967296) 2147483647) (not (= (+ (mod (mod |ULTIMATE.start_main_~var_109~0#1| 256) 4294967296) |v_ULTIMATE.start_main_~var_139~0#1_12|) 4294967295))) (or (not (= (+ (mod (mod |ULTIMATE.start_main_~var_109~0#1| 256) 4294967296) |v_ULTIMATE.start_main_~var_139~0#1_12| 1) 0)) (not (<= (mod (mod |ULTIMATE.start_main_~var_109~0#1| 256) 4294967296) 2147483647)))) (not (= (mod (+ |ULTIMATE.start_main_~mask_SORT_1~0#1| (* 255 |v_ULTIMATE.start_main_~var_139~0#1_12|)) 256) 0))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	//@formatter:on
}