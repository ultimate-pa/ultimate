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
public class QuantifierEliminationDivMod {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY = false;
	private static final boolean CHECK_SIMPLIFICATION_POSSIBILITY = false;
	private static final long TEST_TIMEOUT_MILLISECONDS = 60000999;
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
	public void qeMod3CD45A9E() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~7", "ULTIMATE.start_gcd_test_~b"),
		};
		final String formulaAsString = "(exists ((v_ULTIMATE.start_gcd_test_~a_7 Int)) (and (or (and (or (and (or (and (= ULTIMATE.start_gcd_test_~b (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256)) (not (= (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 0)) (< v_ULTIMATE.start_gcd_test_~a_7 0)) (= ULTIMATE.start_gcd_test_~b (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256))) (<= (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256) 127)) (and (or (and (= ULTIMATE.start_gcd_test_~b (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256)) (not (= (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 0)) (< v_ULTIMATE.start_gcd_test_~a_7 0)) (= (+ ULTIMATE.start_gcd_test_~b 256) (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256))) (not (<= (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256) 127)))) (or (not (< v_ULTIMATE.start_gcd_test_~a_7 0)) (= (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 0))) (and (or (and (or (and (= ULTIMATE.start_gcd_test_~b (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256)) (<= (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256) 127)) (and (= ULTIMATE.start_gcd_test_~b (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256)) (not (<= (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256) 127)))) (<= (mod (+ ULTIMATE.start_main_~y~7 (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7)) 256) 127)) (and (or (and (= ULTIMATE.start_gcd_test_~b (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256)) (<= (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256) 127)) (and (= ULTIMATE.start_gcd_test_~b (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256)) (not (<= (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256) 127)))) (not (<= (mod (+ ULTIMATE.start_main_~y~7 (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7)) 256) 127)))) (not (= (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 0)) (< v_ULTIMATE.start_gcd_test_~a_7 0))) (<= (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256) 127)))";
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
	public void qeDivModB3099151() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 Int) (aux_div_aux_mod_ULTIMATE.start_main_~n~6_41_52 Int) (aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 Int)) (and (not (= (mod (div (mod (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63)) 18446744073709551616) 2) 18446744073709551616) 1)) (< (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_div_aux_mod_ULTIMATE.start_main_~n~6_41_52 4294967296) (* aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296)) 4294967296) (<= 1 (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_div_aux_mod_ULTIMATE.start_main_~n~6_41_52 4294967296) (* aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296))) (<= 0 (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296))) (< (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296)) 2) (< aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296) (<= 0 aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModF059E9EA() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_~x~0"),
		};
		final String formulaAsString = "(exists ((|#memory_int| (Array Int (Array Int Int))) (|main_~#a~0.base| Int) (|main_~#a~0.offset| Int)) (and (= (+ (select (select |#memory_int| |main_~#a~0.base|) |main_~#a~0.offset|) 1) 0) (= (mod (select (select |#memory_int| |main_~#a~0.base|) |main_~#a~0.offset|) 256) main_~x~0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModC44E259() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_~x~0"),
		};
		final String formulaAsString = "(exists ((|#memory_int| (Array Int (Array Int Int))) (|main_~#cp~0.base| Int) (|main_~#cp~0.offset| Int)) (and (= (mod (select (select |#memory_int| |main_~#cp~0.base|) |main_~#cp~0.offset|) 256) main_~x~0) (= (+ (select (select |#memory_int| |main_~#cp~0.base|) |main_~#cp~0.offset|) 1) 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod4C35A753() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_~snd~0"),
		};
		final String formulaAsString = "(exists ((|#memory_int| (Array Int (Array Int Int))) (main_~p~0.base Int) (main_~p~0.offset Int) (|v_#Ultimate.C_memset_#ptr.offset_AFTER_CALL_5| Int)) (and (= (+ (select (select |#memory_int| main_~p~0.base) (+ 2 |v_#Ultimate.C_memset_#ptr.offset_AFTER_CALL_5|)) 1) 0) (<= 0 |v_#Ultimate.C_memset_#ptr.offset_AFTER_CALL_5|) (<= main_~p~0.offset 0) (<= |v_#Ultimate.C_memset_#ptr.offset_AFTER_CALL_5| main_~p~0.offset) (= (mod (select (select |#memory_int| main_~p~0.base) (+ 2 main_~p~0.offset)) 256) main_~snd~0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod22274A50() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_~pos~0"),
		};
		final String formulaAsString = "(exists ((aux_mod_v_main_~pos~0_9_35 Int) (aux_div_v_main_~pos~0_9_35 Int)) (and (<= 254 aux_mod_v_main_~pos~0_9_35) (< 0 (+ 256 aux_mod_v_main_~pos~0_9_35 (* aux_div_v_main_~pos~0_9_35 256))) (= (+ (mod (+ (* 255 aux_mod_v_main_~pos~0_9_35) 2) 256) 2) main_~pos~0) (<= (+ aux_mod_v_main_~pos~0_9_35 (* aux_div_v_main_~pos~0_9_35 256)) 0) (< aux_mod_v_main_~pos~0_9_35 256)))";
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
	public void qeDivMod79A79F74() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_a_p"),
		};
		final String formulaAsString = "(exists ((v_main_a_p_18 Int) (aux_div_v_main_a_q_17_56 Int)) (and (= (mod (+ 4294966796 (* 4294967295 main_a_p) (div v_main_a_p_18 2) v_main_a_p_18) 4294967296) 0) (<= (+ (* aux_div_v_main_a_q_17_56 4294967296) (* 4294967296 (div (+ (- 500) (div v_main_a_p_18 2) (* (- 1) main_a_p) v_main_a_p_18) (- 4294967296))) v_main_a_p_18) 1000) (<= 0 v_main_a_p_18) (<= 500 (+ (* aux_div_v_main_a_q_17_56 4294967296) (* 4294967296 (div (+ (- 500) (div v_main_a_p_18 2) (* (- 1) main_a_p) v_main_a_p_18) (- 4294967296))) v_main_a_p_18)) (< v_main_a_p_18 4294967296)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDiv4686750A() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "main_m"),
			new FunDecl(SmtSortUtils::getIntSort, "main_eat", "main_init", "main_cakeLeft"),
		};
		final String formulaAsString = "(exists ((v_main_m_14 (Array Int Int)) (v_ArrVal_17 Int) (v_ArrVal_16 Int) (v_ArrVal_18 Int)) (and (or (= main_eat main_cakeLeft) (<= main_init (select v_main_m_14 main_cakeLeft))) (= main_m (store (store v_main_m_14 main_eat v_ArrVal_17) main_cakeLeft v_ArrVal_16)) (<= (select v_main_m_14 main_eat) (select v_main_m_14 main_cakeLeft)) (<= (select (store v_main_m_14 main_eat v_ArrVal_18) main_cakeLeft) (+ (div (select v_main_m_14 main_eat) 2) v_ArrVal_16))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDiv7C176B87() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "main_m"),
			new FunDecl(SmtSortUtils::getIntSort, "main_eat", "main_init", "main_cakeLeft"),
		};
		final String formulaAsString = "(exists ((v_main_m_12 (Array Int Int)) (v_ArrVal_11 Int) (v_ArrVal_10 Int)) (and (or (and (<= (+ (div main_init 2) (select v_main_m_12 main_eat)) (select v_main_m_12 main_cakeLeft)) (<= 0 (select v_main_m_12 main_eat))) (= main_eat main_cakeLeft)) (= (store (store v_main_m_12 main_eat (div (select v_main_m_12 main_eat) 2)) main_cakeLeft v_ArrVal_11) main_m) (<= (select (store v_main_m_12 main_eat v_ArrVal_10) main_cakeLeft) (+ v_ArrVal_11 (div (select v_main_m_12 main_eat) 2)))))";
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
	public void qeModDA7283E() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_y", "aux_mod_v_main_y_22_19"),
		};
		final String formulaAsString = "(exists ((aux_div_v_main_y_22_19 Int)) (= main_y (mod (+ (* 4294967294 aux_mod_v_main_y_22_19) 1 (* 4294967292 aux_div_v_main_y_22_19)) 4294967296)))";
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
	public void qeModBEF5E320() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "main_~#a~0.base", "main_~#a~0.offset"),
		};
		final String formulaAsString = "(exists ((main_~x~0 Int)) (and (= (select (select |#memory_int| |main_~#a~0.base|) (+ |main_~#a~0.offset| (* (mod main_~x~0 4294967296) 4))) 0) (<= 0 main_~x~0) (< main_~x~0 128)))";
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
	public void qeDivMod87C893B3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~a29~0"),
		};
		final String formulaAsString = "(exists ((v_~a29~0_897 Int)) (and (<= ~a29~0 (+ (div (+ v_~a29~0_897 (- 142312)) 5) 1)) (not (= (mod (+ 3 v_~a29~0_897) 5) 0)) (<= (+ v_~a29~0_897 127) 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


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
	public void qeModC4A49E94() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~var_23~0#1| Int)) (and (<= 0 |ULTIMATE.start_main_~var_23~0#1|) (= (mod |ULTIMATE.start_main_~var_23~0#1| 256) 0) (< |ULTIMATE.start_main_~var_23~0#1| 256)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModCCCC5BE3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_#t~mem36#1"),
		};
		final String formulaAsString = "(exists ((|#memory_int| (Array Int (Array Int Int))) (|ULTIMATE.start_main_~#new_packet~0#1.base| Int) (|ULTIMATE.start_main_~#new_packet~0#1.offset| Int) (|v_ULTIMATE.start_receive_~#packet~0#1.base_10| Int)) (and (= (select (select |#memory_int| |v_ULTIMATE.start_receive_~#packet~0#1.base_10|) 4) (select (select |#memory_int| |ULTIMATE.start_main_~#new_packet~0#1.base|) (+ 4 |ULTIMATE.start_main_~#new_packet~0#1.offset|))) (= (mod (select (select |#memory_int| |ULTIMATE.start_main_~#new_packet~0#1.base|) (+ 4 |ULTIMATE.start_main_~#new_packet~0#1.offset|)) 4294967296) 1) (= |ULTIMATE.start_main_#t~mem36#1| (select (select |#memory_int| |ULTIMATE.start_main_~#new_packet~0#1.base|) (+ 4 |ULTIMATE.start_main_~#new_packet~0#1.offset|)))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModBB65ABF4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53_73"),
		};
		final String formulaAsString = "(exists ((|aux_div_ULTIMATE.start_main_~main__x~0#1_66| Int) (|aux_div_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53| Int)) (and (<= 0 (+ (* |aux_div_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53| 3) (* 4294967296 |aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53_73|) 1)) (= (mod (mod (mod (+ (* |aux_div_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53| 3) 3) 4294967296) 3) 4294967296) 0) (< (+ (* |aux_div_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53| 3) (* 4294967296 |aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53_73|)) 4294967295) (<= (+ (* |aux_div_ULTIMATE.start_main_~main__x~0#1_66| 4294967296) (* |aux_div_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53| 3) (* 4294967296 |aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53_73|)) 6442450942) (<= 2147483647 (+ (* |aux_div_ULTIMATE.start_main_~main__x~0#1_66| 4294967296) (* |aux_div_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53| 3) (* 4294967296 |aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53_73|)))))";
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
	public void qeDivModE995CB24() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1| Int) (|v_ULTIMATE.start_main_~ret~1#1_BEFORE_CALL_1| Int)) (and (not (<= (mod (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 4294967296) 2147483647)) (or (and (or (and (= (mod (+ (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 1) 4294967296) (+ |v_ULTIMATE.start_main_~ret~1#1_BEFORE_CALL_1| 4294967296)) (not (= 0 (mod (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10))) (< (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 0)) (and (or (not (< (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 0)) (= 0 (mod (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10))) (= (mod (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 4294967296) (+ |v_ULTIMATE.start_main_~ret~1#1_BEFORE_CALL_1| 4294967296)))) (not (<= (mod (+ (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 1) 4294967296) 2147483647))) (and (<= (mod (+ (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 1) 4294967296) 2147483647) (or (and (or (not (< (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 0)) (= 0 (mod (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10))) (= (mod (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 4294967296) (+ |v_ULTIMATE.start_main_~ret~1#1_BEFORE_CALL_1| 4294967296))) (and (not (= 0 (mod (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10))) (< (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 0) (= |v_ULTIMATE.start_main_~ret~1#1_BEFORE_CALL_1| (mod (+ (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 1) 4294967296))))))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod115C8EE3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#x~0#1.offset", "ULTIMATE.start_main_~ret~1#1", "ULTIMATE.start_main_~#x~0#1.base"),
		};
		final String formulaAsString = "(exists ((|v_#memory_int_24| (Array Int (Array Int Int))) (v_ArrVal_325 Int) (v_ArrVal_324 Int)) (and (= |#memory_int| (store |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base| (store (store (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) |ULTIMATE.start_main_~#x~0#1.offset| v_ArrVal_325) (+ 4 |ULTIMATE.start_main_~#x~0#1.offset|) v_ArrVal_324))) (<= 1 (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) |ULTIMATE.start_main_~#x~0#1.offset|)) (<= (+ 1 (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 12 |ULTIMATE.start_main_~#x~0#1.offset|))) (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 16 |ULTIMATE.start_main_~#x~0#1.offset|))) (<= (+ (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 4 |ULTIMATE.start_main_~#x~0#1.offset|)) 1) (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 8 |ULTIMATE.start_main_~#x~0#1.offset|))) (<= (+ (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) |ULTIMATE.start_main_~#x~0#1.offset|) 1) (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 4 |ULTIMATE.start_main_~#x~0#1.offset|))) (= |ULTIMATE.start_main_~ret~1#1| (mod (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 16 |ULTIMATE.start_main_~#x~0#1.offset|)) 4294967296)) (<= (+ (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 8 |ULTIMATE.start_main_~#x~0#1.offset|)) 1) (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 12 |ULTIMATE.start_main_~#x~0#1.offset|))) (<= (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 16 |ULTIMATE.start_main_~#x~0#1.offset|)) 2147483647)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod9C6A4266() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#x~0#1.offset", "ULTIMATE.start_main_~temp~0#1", "ULTIMATE.start_main_~#x~0#1.base"),
		};
		final String formulaAsString = "(exists ((|#memory_int| (Array Int (Array Int Int)))) (and (not (= (mod (select (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|) |ULTIMATE.start_main_~#x~0#1.offset|) 2) 0)) (= (select (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|) |ULTIMATE.start_main_~#x~0#1.offset|) |ULTIMATE.start_main_~temp~0#1|)))";
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
	public void qeDiv77A7B16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~a~0#1.offset", "ULTIMATE.start_main_~a~0#1.base"),
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~n~0#1| Int) (v_ArrVal_62 Int) (v_arrayElimCell_1 Int)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (+ |ULTIMATE.start_main_~a~0#1.offset| (- 4) (* |ULTIMATE.start_main_~n~0#1| 4))) v_ArrVal_62) (<= |ULTIMATE.start_main_~n~0#1| 2) (= v_arrayElimCell_1 (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (+ |ULTIMATE.start_main_~a~0#1.offset| (- 4) (* (div |ULTIMATE.start_main_~n~0#1| 2) 4)))) (< 1 |ULTIMATE.start_main_~n~0#1|) (= v_arrayElimCell_1 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void qeMod868D31B1() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_~p~0.offset"),
		};
		final String formulaAsString = "(forall ((|v_#memory_int_31| (Array Int (Array Int Int))) (main_~p~0.base Int) (|v_#Ultimate.C_memset_#ptr.offset_18| Int)) (or (not (<= |v_#Ultimate.C_memset_#ptr.offset_18| main_~p~0.offset)) (not (<= 0 |v_#Ultimate.C_memset_#ptr.offset_18|)) (= 255 (mod (mod (select (store (select |v_#memory_int_31| main_~p~0.base) (+ |v_#Ultimate.C_memset_#ptr.offset_18| 2) (- 1)) (+ 2 main_~p~0.offset)) 256) 4294967296))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod408F192() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "#Ultimate.meminit_#t~loopctr19", "#Ultimate.meminit_#ptr.offset", "~#perf_swevent_enabled~0.offset", "#Ultimate.meminit_#ptr.base"),
		};
		final String formulaAsString = "(forall ((|#memory_int| (Array Int (Array Int Int)))) (or (< 17179869183 (+ |~#perf_swevent_enabled~0.offset| (* (mod (select (store (select |#memory_int| |#Ultimate.meminit_#ptr.base|) (+ |#Ultimate.meminit_#ptr.offset| |#Ultimate.meminit_#t~loopctr19|) 0) |#Ultimate.meminit_#ptr.offset|) 4294967296) 4))) (<= (mod (select (store (select |#memory_int| |#Ultimate.meminit_#ptr.base|) (+ |#Ultimate.meminit_#ptr.offset| |#Ultimate.meminit_#t~loopctr19|) 0) |#Ultimate.meminit_#ptr.offset|) 4294967296) 2147483647)))";
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
	public void qeDiv75B4002B() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "main_m"),
			new FunDecl(SmtSortUtils::getIntSort, "main_eat", "main_init", "main_cakeLeft"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_29 Int) (v_ArrVal_31 Int) (v_ArrVal_33 Int) (v_ArrVal_30 Int)) (or (not (<= (select (store main_m main_eat v_ArrVal_30) main_cakeLeft) (+ (div (select main_m main_eat) 2) v_ArrVal_31))) (not (<= v_ArrVal_29 (div (select main_m main_eat) 2))) (not (<= (select (store (store main_m main_eat v_ArrVal_29) main_cakeLeft v_ArrVal_31) main_eat) v_ArrVal_31)) (< (+ (div (select (store (store main_m main_eat v_ArrVal_29) main_cakeLeft v_ArrVal_31) main_eat) 2) (div main_init 2)) (+ (select (store (store (store main_m main_eat v_ArrVal_29) main_cakeLeft v_ArrVal_31) main_eat v_ArrVal_33) main_cakeLeft) 1))))";
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
	public void qeModB1B00B69() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#x~0#1.offset", "~N~0", "ULTIMATE.start_main_~temp~0#1", "ULTIMATE.start_main_~ret~0#1", "ULTIMATE.start_main_~ret2~0#1", "ULTIMATE.start_main_~#x~0#1.base"),
		};
		final String formulaAsString = "(forall ((|#memory_int| (Array Int (Array Int Int)))) (or (and (= (+ |ULTIMATE.start_main_~ret~0#1| 4294967296) (mod (select (store (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|) (+ (* ~N~0 4) (- 4) |ULTIMATE.start_main_~#x~0#1.offset|) |ULTIMATE.start_main_~temp~0#1|) (+ 4 |ULTIMATE.start_main_~#x~0#1.offset|)) 4294967296)) (= |ULTIMATE.start_main_~ret2~0#1| |ULTIMATE.start_main_~ret~0#1|)) (<= (mod (select (store (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|) (+ (* ~N~0 4) (- 4) |ULTIMATE.start_main_~#x~0#1.offset|) |ULTIMATE.start_main_~temp~0#1|) (+ 4 |ULTIMATE.start_main_~#x~0#1.offset|)) 4294967296) 2147483647)))";
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
	public void qeModB80ACE51() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~num~0#1", "~ARR_SIZE~0", "ULTIMATE.start_main_~#array1~0#1.offset", "ULTIMATE.start_main_~#array2~0#1.offset", "ULTIMATE.start_main_~#array2~0#1.base", "ULTIMATE.start_main_~sum~0#1", "ULTIMATE.start_main_~#array1~0#1.base"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~index~0#1| Int)) (or (= (+ (select (select (store (store |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) (+ |ULTIMATE.start_main_~#array1~0#1.offset| (* 4 |ULTIMATE.start_main_~index~0#1|)) (+ (* |ULTIMATE.start_main_~num~0#1| |ULTIMATE.start_main_~num~0#1| |ULTIMATE.start_main_~index~0#1|) (select (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) (+ |ULTIMATE.start_main_~#array1~0#1.offset| (* 4 |ULTIMATE.start_main_~index~0#1|)))))) |ULTIMATE.start_main_~#array2~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) (+ |ULTIMATE.start_main_~#array1~0#1.offset| (* 4 |ULTIMATE.start_main_~index~0#1|)) (+ (* |ULTIMATE.start_main_~num~0#1| |ULTIMATE.start_main_~num~0#1| |ULTIMATE.start_main_~index~0#1|) (select (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) (+ |ULTIMATE.start_main_~#array1~0#1.offset| (* 4 |ULTIMATE.start_main_~index~0#1|)))))) |ULTIMATE.start_main_~#array2~0#1.base|) (+ |ULTIMATE.start_main_~#array2~0#1.offset| (- 17179869184) (* (mod (+ 4294967295 ~ARR_SIZE~0 (* 4294967295 |ULTIMATE.start_main_~index~0#1|)) 4294967296) 4)) (+ (select (select (store |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) (+ |ULTIMATE.start_main_~#array1~0#1.offset| (* 4 |ULTIMATE.start_main_~index~0#1|)) (+ (* |ULTIMATE.start_main_~num~0#1| |ULTIMATE.start_main_~num~0#1| |ULTIMATE.start_main_~index~0#1|) (select (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) (+ |ULTIMATE.start_main_~#array1~0#1.offset| (* 4 |ULTIMATE.start_main_~index~0#1|)))))) |ULTIMATE.start_main_~#array2~0#1.base|) (+ |ULTIMATE.start_main_~#array2~0#1.offset| (- 17179869184) (* (mod (+ 4294967295 ~ARR_SIZE~0 (* 4294967295 |ULTIMATE.start_main_~index~0#1|)) 4294967296) 4))) (* |ULTIMATE.start_main_~num~0#1| |ULTIMATE.start_main_~index~0#1|)))) |ULTIMATE.start_main_~#array1~0#1.base|) |ULTIMATE.start_main_~#array1~0#1.offset|) (select (store (select (store |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) (+ |ULTIMATE.start_main_~#array1~0#1.offset| (* 4 |ULTIMATE.start_main_~index~0#1|)) (+ (* |ULTIMATE.start_main_~num~0#1| |ULTIMATE.start_main_~num~0#1| |ULTIMATE.start_main_~index~0#1|) (select (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) (+ |ULTIMATE.start_main_~#array1~0#1.offset| (* 4 |ULTIMATE.start_main_~index~0#1|)))))) |ULTIMATE.start_main_~#array2~0#1.base|) (+ |ULTIMATE.start_main_~#array2~0#1.offset| (- 17179869184) (* (mod (+ 4294967295 ~ARR_SIZE~0 (* 4294967295 |ULTIMATE.start_main_~index~0#1|)) 4294967296) 4)) (+ (select (select (store |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) (+ |ULTIMATE.start_main_~#array1~0#1.offset| (* 4 |ULTIMATE.start_main_~index~0#1|)) (+ (* |ULTIMATE.start_main_~num~0#1| |ULTIMATE.start_main_~num~0#1| |ULTIMATE.start_main_~index~0#1|) (select (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) (+ |ULTIMATE.start_main_~#array1~0#1.offset| (* 4 |ULTIMATE.start_main_~index~0#1|)))))) |ULTIMATE.start_main_~#array2~0#1.base|) (+ |ULTIMATE.start_main_~#array2~0#1.offset| (- 17179869184) (* (mod (+ 4294967295 ~ARR_SIZE~0 (* 4294967295 |ULTIMATE.start_main_~index~0#1|)) 4294967296) 4))) (* |ULTIMATE.start_main_~num~0#1| |ULTIMATE.start_main_~index~0#1|))) |ULTIMATE.start_main_~#array2~0#1.offset|) |ULTIMATE.start_main_~sum~0#1|) 0) (not (< |ULTIMATE.start_main_~index~0#1| ~ARR_SIZE~0)) (<= (mod (+ 4294967295 ~ARR_SIZE~0 (* 4294967295 |ULTIMATE.start_main_~index~0#1|)) 4294967296) 2147483647) (not (<= 0 |ULTIMATE.start_main_~index~0#1|))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod8E7FC458() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "base2flt_#res", "aux_mod_v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_16_62"),
		};
		final String formulaAsString = "(forall ((|aux_div_v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_16_62| Int)) (or (<= (mod (+ (div |aux_mod_v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_16_62| 16777216) (* 256 |aux_div_v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_16_62|)) 4294967296) 2147483647) (and (or (< (mod (+ (div |aux_mod_v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_16_62| 16777216) (* 256 |aux_div_v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_16_62|)) 4294967296) (+ (mod (div |base2flt_#res| 16777216) 4294967296) 1)) (<= (mod (div |base2flt_#res| 16777216) 4294967296) 2147483647)) (or (and (< (mod (+ (div |aux_mod_v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_16_62| 16777216) (* 256 |aux_div_v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_16_62|)) 4294967296) (+ (mod (div |base2flt_#res| 16777216) 4294967296) 1)) (<= (mod (div |base2flt_#res| 16777216) 4294967296) 2147483647)) (not (<= (mod (+ (div |aux_mod_v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_16_62| 16777216) (* 256 |aux_div_v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_16_62|)) 4294967296) 2147483647))))))";
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
	public void qeDivModB6FB8F46() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~sn~0#1"),
		};
		final String formulaAsString = "(forall ((|aux_mod_ULTIMATE.start_main_~n~0#1_45| Int)) (or (> 0 |aux_mod_ULTIMATE.start_main_~n~0#1_45|) (< |aux_mod_ULTIMATE.start_main_~n~0#1_45| (mod |ULTIMATE.start_main_~i~0#1| 4294967296)) (= (mod (div (mod (+ |aux_mod_ULTIMATE.start_main_~n~0#1_45| (* |aux_mod_ULTIMATE.start_main_~n~0#1_45| |aux_mod_ULTIMATE.start_main_~n~0#1_45|)) 4294967296) 2) 4294967296) (mod (+ |ULTIMATE.start_main_~sn~0#1| |ULTIMATE.start_main_~i~0#1|) 4294967296)) (>= |aux_mod_ULTIMATE.start_main_~n~0#1_45| 4294967296)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod9052E25D() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~nomsg~0"),
		};
		final String formulaAsString = "(forall ((v_~id1~0_18 Int)) (or (not (<= v_~id1~0_18 127)) (not (= (+ ~nomsg~0 256) (mod v_~id1~0_18 256))) (not (<= 0 v_~id1~0_18))))";
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
	public void qeModFA6DC5F4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~nomsg~0"),
		};
		final String formulaAsString = "(forall ((v_~id1~0_27 Int)) (or (not (<= 0 v_~id1~0_27)) (not (= (+ ~nomsg~0 256) (mod v_~id1~0_27 256))) (not (<= v_~id1~0_27 127))))";
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
	public void qeMod5C9A1EC6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~mask_SORT_1~0#1"),
		};
		final String formulaAsString = "(forall ((|aux_div_v_ULTIMATE.start_main_#t~nondet87#1_12_50| Int) (|aux_div_aux_mod_v_ULTIMATE.start_main_#t~nondet87#1_12_50_68| Int) (|ULTIMATE.start_main_~var_131~0#1| Int)) (or (< (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) (* |aux_div_v_ULTIMATE.start_main_#t~nondet87#1_12_50| 256)) (<= (+ (* |aux_div_v_ULTIMATE.start_main_#t~nondet87#1_12_50| 256) 256) (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296)) (= (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) (+ (* |aux_div_v_ULTIMATE.start_main_#t~nondet87#1_12_50| 256) (* 4294967296 |aux_div_aux_mod_v_ULTIMATE.start_main_#t~nondet87#1_12_50_68|))) (<= (+ (* |aux_div_v_ULTIMATE.start_main_#t~nondet87#1_12_50| 256) 4294967296 (* 4294967296 |aux_div_aux_mod_v_ULTIMATE.start_main_#t~nondet87#1_12_50_68|)) (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296)) (< (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) (+ (* |aux_div_v_ULTIMATE.start_main_#t~nondet87#1_12_50| 256) (* 4294967296 |aux_div_aux_mod_v_ULTIMATE.start_main_#t~nondet87#1_12_50_68|))) (and (or (<= (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) 2147483647) (<= (mod (mod |ULTIMATE.start_main_~mask_SORT_1~0#1| 256) 4294967296) 2147483647) (not (= (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) (mod (mod |ULTIMATE.start_main_~mask_SORT_1~0#1| 256) 4294967296)))) (or (not (<= (mod (mod |ULTIMATE.start_main_~mask_SORT_1~0#1| 256) 4294967296) 2147483647)) (not (<= (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) 2147483647)) (not (= (mod (mod |ULTIMATE.start_main_~var_131~0#1| 256) 4294967296) (mod (mod |ULTIMATE.start_main_~mask_SORT_1~0#1| 256) 4294967296)))))))";
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


	@Test
	public void qeModE9F5B50() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "aux_mod_aux_mod_v_ULTIMATE.start_main_~var_63~0#1_14_48_66", "aux_div_aux_mod_v_ULTIMATE.start_main_~var_63~0#1_14_48_66", "ULTIMATE.start_main_~var_60~0#1", "ULTIMATE.start_main_~state_61~0#1"),
		};
		final String formulaAsString = "(forall ((|aux_div_v_ULTIMATE.start_main_~var_63~0#1_14_48| Int) (|v_ULTIMATE.start_main_~var_63_arg_2~0#1_13| Int)) (or (and (or (= (mod |ULTIMATE.start_main_~state_61~0#1| 256) 0) (and (or (not (= (+ (* |aux_div_v_ULTIMATE.start_main_~var_63~0#1_14_48| 256) (* 4294967296 |aux_div_aux_mod_v_ULTIMATE.start_main_~var_63~0#1_14_48_66|) |aux_mod_aux_mod_v_ULTIMATE.start_main_~var_63~0#1_14_48_66|) (mod (mod |ULTIMATE.start_main_~var_60~0#1| 256) 4294967296))) (not (<= (mod (mod |ULTIMATE.start_main_~var_60~0#1| 256) 4294967296) 2147483647))) (or (not (= (mod (mod |ULTIMATE.start_main_~var_60~0#1| 256) 4294967296) (+ (* |aux_div_v_ULTIMATE.start_main_~var_63~0#1_14_48| 256) (* 4294967296 |aux_div_aux_mod_v_ULTIMATE.start_main_~var_63~0#1_14_48_66|) 4294967296 |aux_mod_aux_mod_v_ULTIMATE.start_main_~var_63~0#1_14_48_66|))) (<= (mod (mod |ULTIMATE.start_main_~var_60~0#1| 256) 4294967296) 2147483647)))) (or (and (or (not (= (+ (* |aux_div_v_ULTIMATE.start_main_~var_63~0#1_14_48| 256) (* 4294967296 |aux_div_aux_mod_v_ULTIMATE.start_main_~var_63~0#1_14_48_66|) |aux_mod_aux_mod_v_ULTIMATE.start_main_~var_63~0#1_14_48_66|) (mod (mod |v_ULTIMATE.start_main_~var_63_arg_2~0#1_13| 256) 4294967296))) (not (<= (mod (mod |ULTIMATE.start_main_~var_60~0#1| 256) 4294967296) 2147483647))) (or (not (= (+ (* |aux_div_v_ULTIMATE.start_main_~var_63~0#1_14_48| 256) (* 4294967296 |aux_div_aux_mod_v_ULTIMATE.start_main_~var_63~0#1_14_48_66|) |aux_mod_aux_mod_v_ULTIMATE.start_main_~var_63~0#1_14_48_66|) (mod (mod |v_ULTIMATE.start_main_~var_63_arg_2~0#1_13| 256) 4294967296))) (<= (mod (mod |ULTIMATE.start_main_~var_60~0#1| 256) 4294967296) 2147483647))) (not (= (mod |ULTIMATE.start_main_~state_61~0#1| 256) 0)))) (not (<= (mod (mod |v_ULTIMATE.start_main_~var_63_arg_2~0#1_13| 256) 4294967296) 2147483647))))";
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
	public void qeMod27F0D8E4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#prio_queue~0#1.base", "#StackHeapBarrier", "ULTIMATE.start_main_#t~mem36#1"),
		};
		final String formulaAsString = "(forall ((|v_#memory_int_59| (Array Int (Array Int Int))) (|v_append_to_queue_~#p.base_10| Int) (v_ArrVal_244 Int) (v_ArrVal_246 Int) (v_append_to_queue_~node~0.base_4 Int) (v_ArrVal_245 Int) (v_ArrVal_242 Int) (v_ArrVal_243 Int) (v_ArrVal_238 (Array Int Int))) (or (= (mod (select (select (store (store (store |v_#memory_int_59| |v_append_to_queue_~#p.base_10| (store (store (store (select |v_#memory_int_59| |v_append_to_queue_~#p.base_10|) 0 v_ArrVal_244) 4 |ULTIMATE.start_main_#t~mem36#1|) 8 v_ArrVal_246)) v_append_to_queue_~node~0.base_4 (store (store (store (store (select (store |v_#memory_int_59| |v_append_to_queue_~#p.base_10| (store (store (store (select |v_#memory_int_59| |v_append_to_queue_~#p.base_10|) 0 v_ArrVal_244) 4 |ULTIMATE.start_main_#t~mem36#1|) 8 v_ArrVal_246)) v_append_to_queue_~node~0.base_4) 0 v_ArrVal_245) 4 |ULTIMATE.start_main_#t~mem36#1|) 8 v_ArrVal_242) 12 v_ArrVal_243)) |ULTIMATE.start_main_~#prio_queue~0#1.base| v_ArrVal_238) v_append_to_queue_~node~0.base_4) 4) 4294967296) 1) (not (< v_append_to_queue_~node~0.base_4 |#StackHeapBarrier|))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDiv883B2FE0() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~list~0#1.offset", "ULTIMATE.start_main_~p~0#1.base", "ULTIMATE.start_main_~p~0#1.offset", "ULTIMATE.start_main_~list~0#1.base"),
		};
		final String formulaAsString = "(forall ((|#memory_int| (Array Int (Array Int Int))) (v_ArrVal_396 Int)) (or (< (select (select |#memory_int| |ULTIMATE.start_main_~p~0#1.base|) |ULTIMATE.start_main_~p~0#1.offset|) 20) (< 9 (select (select (store |#memory_int| |ULTIMATE.start_main_~p~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~p~0#1.base|) |ULTIMATE.start_main_~p~0#1.offset| v_ArrVal_396)) |ULTIMATE.start_main_~list~0#1.base|) |ULTIMATE.start_main_~list~0#1.offset|)) (not (<= (div (select (select |#memory_int| |ULTIMATE.start_main_~p~0#1.base|) |ULTIMATE.start_main_~p~0#1.offset|) 2) v_ArrVal_396))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod6C989C94() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "Id_MCDC_113_#res#1"),
		};
		final String formulaAsString = "(forall ((|v_Id_MCDC_113_~Id_MCDC_112#1.base_BEFORE_CALL_1| Int) (|v_Id_MCDC_113_~Id_MCDC_112#1.offset_BEFORE_CALL_1| Int)) (<= (mod (select (select |#memory_int| |v_Id_MCDC_113_~Id_MCDC_112#1.base_BEFORE_CALL_1|) |v_Id_MCDC_113_~Id_MCDC_112#1.offset_BEFORE_CALL_1|) 4294967296) (mod |Id_MCDC_113_#res#1| 4294967296)))";
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
	public void qeMod4E5EF4AF() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#valid"),
			new FunDecl(SmtSortUtils::getIntSort, "~#Id_MCDC_113~0.base"),
		};
		final String formulaAsString = "(forall ((|#memory_int| (Array Int (Array Int Int))) (v_ArrVal_185 (Array Int Int)) (|v_ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.base_10| Int)) (or (not (< (mod (select (select (store |#memory_int| |~#Id_MCDC_113~0.base| v_ArrVal_185) |v_ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.base_10|) 3) 4294967296) (mod (select (select (store |#memory_int| |~#Id_MCDC_113~0.base| v_ArrVal_185) |v_ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.base_10|) 2) 4294967296))) (not (= (select (select |#memory_int| |v_ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.base_10|) 3) 0)) (not (= (select |#valid| |v_ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.base_10|) 0)) (not (= (select (select |#memory_int| |v_ULTIMATE.start_Id_MCDC_99_~#Id_MCDC_139~0#1.base_10|) 2) 0))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod5D401389() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~s~0#1"),
		};
		final String formulaAsString = "(forall ((|aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| Int) (|aux_div_v_ULTIMATE.start_main_~s~0#1_10_50| Int) (|aux_div_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| Int)) (or (<= (+ |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| (* 4294967296 |aux_div_v_ULTIMATE.start_main_~s~0#1_10_50|)) (+ (mod (mod |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| 256) 4294967296) |ULTIMATE.start_main_~s~0#1|)) (< (+ (mod (mod |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| 256) 4294967296) |ULTIMATE.start_main_~s~0#1|) (* 4294967296 |aux_div_v_ULTIMATE.start_main_~s~0#1_10_50|)) (>= |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| 4294967296) (> 0 |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60|) (< (+ |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| (* |aux_div_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| 4294967296)) 0) (<= 256 (+ |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| (* |aux_div_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| 4294967296)))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModCB4D790D() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~s~0#1"),
		};
		final String formulaAsString = "(forall ((|aux_div_aux_mod_v_ULTIMATE.start_main_~s~0#1_10_43_61| Int) (|aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| Int) (|aux_div_v_ULTIMATE.start_main_~s~0#1_10_43| Int) (|aux_div_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| Int)) (or (<= (+ 256 (* 256 |aux_div_v_ULTIMATE.start_main_~s~0#1_10_43|)) (+ (mod (mod |ULTIMATE.start_main_~s~0#1| 256) 4294967296) (mod (mod |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| 256) 4294967296))) (>= |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| 4294967296) (<= (+ (* |aux_div_aux_mod_v_ULTIMATE.start_main_~s~0#1_10_43_61| 4294967296) |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| (* 256 |aux_div_v_ULTIMATE.start_main_~s~0#1_10_43|)) (+ (mod (mod |ULTIMATE.start_main_~s~0#1| 256) 4294967296) (mod (mod |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| 256) 4294967296))) (< (+ (mod (mod |ULTIMATE.start_main_~s~0#1| 256) 4294967296) (mod (mod |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| 256) 4294967296)) (+ (* |aux_div_aux_mod_v_ULTIMATE.start_main_~s~0#1_10_43_61| 4294967296) (* 256 |aux_div_v_ULTIMATE.start_main_~s~0#1_10_43|))) (> 0 |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60|) (< (+ |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| (* |aux_div_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| 4294967296)) 0) (< (+ (mod (mod |ULTIMATE.start_main_~s~0#1| 256) 4294967296) (mod (mod |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| 256) 4294967296)) (* 256 |aux_div_v_ULTIMATE.start_main_~s~0#1_10_43|)) (<= 256 (+ |aux_mod_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| (* |aux_div_aux_mod_v_ULTIMATE.start_main_~v~0#1_7_42_60| 4294967296)))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModABFFDE63() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#vogal_array~0#1.offset", "ULTIMATE.start_main_~#input_string~0#1.offset", "ULTIMATE.start_main_~#input_string~0#1.base", "ULTIMATE.start_main_~#vogal_array~0#1.base"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~i~0#1| Int)) (or (not (= (select (select |#memory_int| |ULTIMATE.start_main_~#input_string~0#1.base|) (+ |ULTIMATE.start_main_~#input_string~0#1.offset| (mod |ULTIMATE.start_main_~i~0#1| 4294967296) (- 4294967296))) (select (select |#memory_int| |ULTIMATE.start_main_~#vogal_array~0#1.base|) |ULTIMATE.start_main_~#vogal_array~0#1.offset|))) (<= (mod |ULTIMATE.start_main_~i~0#1| 4294967296) 2147483647) (and (or (<= (mod |ULTIMATE.start_main_~i~0#1| 4294967296) 2147483647) (= (select (select |#memory_int| |ULTIMATE.start_main_~#input_string~0#1.base|) (+ |ULTIMATE.start_main_~#input_string~0#1.offset| (mod |ULTIMATE.start_main_~i~0#1| 4294967296) (- 4294967296))) (select (select |#memory_int| |ULTIMATE.start_main_~#vogal_array~0#1.base|) (+ |ULTIMATE.start_main_~#vogal_array~0#1.offset| 1)))) (or (= (select (select |#memory_int| |ULTIMATE.start_main_~#input_string~0#1.base|) (+ |ULTIMATE.start_main_~#input_string~0#1.offset| (mod |ULTIMATE.start_main_~i~0#1| 4294967296))) (select (select |#memory_int| |ULTIMATE.start_main_~#vogal_array~0#1.base|) (+ |ULTIMATE.start_main_~#vogal_array~0#1.offset| 1))) (not (<= (mod |ULTIMATE.start_main_~i~0#1| 4294967296) 2147483647))))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModC1E78117() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "__VERIFIER_assert_#in~cond"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_main_~x~0#1_BEFORE_CALL_1| Int) (|v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| Int) (|v_ULTIMATE.start_main_~k~0#1_BEFORE_CALL_3| Int)) (or (and (or (not (= |__VERIFIER_assert_#in~cond| 1)) (not (= (+ (* (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|) 10) (* (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|) 15) (* 6 (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|))) (+ (* |v_ULTIMATE.start_main_~x~0#1_BEFORE_CALL_1| 30) |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|)))) (or (= (+ (* (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|) 10) (* (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|) 15) (* 6 (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|))) (+ (* |v_ULTIMATE.start_main_~x~0#1_BEFORE_CALL_1| 30) |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|)) (not (= |__VERIFIER_assert_#in~cond| 0)))) (= 0 (mod (+ (* 10 |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|) (* 29 |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|) (* 6 |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|) (* 15 |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|)) 30)) (= (* |v_ULTIMATE.start_main_~k~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|) (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_3|))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModECC70C69() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "__VERIFIER_assert_#in~cond"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_main_~x~0#1_BEFORE_CALL_2| Int) (|v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| Int) (|v_ULTIMATE.start_main_~k~0#1_BEFORE_CALL_3| Int)) (or (and (or (not (= |__VERIFIER_assert_#in~cond| 1)) (not (= (+ (* 5 (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|)) (* 2 (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|)) (* (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|) 6)) (+ (* |v_ULTIMATE.start_main_~x~0#1_BEFORE_CALL_2| 12) (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|))))) (or (= (+ (* 5 (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|)) (* 2 (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|)) (* (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|) 6)) (+ (* |v_ULTIMATE.start_main_~x~0#1_BEFORE_CALL_2| 12) (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|))) (not (= |__VERIFIER_assert_#in~cond| 0)))) (= 0 (mod (+ (* 10 |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|) (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|) (* 7 |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|) (* 6 |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|)) 12)) (= (* |v_ULTIMATE.start_main_~k~0#1_BEFORE_CALL_3| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|) (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_4|))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod8B5E500A() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "__VERIFIER_assert_#in~cond"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_main_~x~0#1_BEFORE_CALL_2| Int) (|v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| Int) (|ULTIMATE.start_main_~k~0#1| Int)) (or (= (* |ULTIMATE.start_main_~k~0#1| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|) (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|)) (= (mod (+ (* 10 |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|) (* 7 |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|) (* 6 |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|) (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|)) 12) 0) (and (or (not (= |__VERIFIER_assert_#in~cond| 1)) (not (= (+ (* 2 (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|)) (* 6 (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|)) (* 5 (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|))) (+ (* |v_ULTIMATE.start_main_~x~0#1_BEFORE_CALL_2| 12) (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|))))) (or (not (= |__VERIFIER_assert_#in~cond| 0)) (= (+ (* 2 (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|)) (* 6 (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|)) (* 5 (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|))) (+ (* |v_ULTIMATE.start_main_~x~0#1_BEFORE_CALL_2| 12) (* |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2| |v_ULTIMATE.start_main_~y~0#1_BEFORE_CALL_2|)))))))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod62C06A2A() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int", "#memory_$Pointer$.base", "#memory_$Pointer$.offset"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_KbFilter_AddDevice_#t~nondet29#1", "ULTIMATE.start_KbFilter_AddDevice_#t~mem27#1.offset", "ULTIMATE.start_KbFilter_AddDevice_~#device~0#1.offset", "ULTIMATE.start_KbFilter_AddDevice_#t~mem27#1.base", "ULTIMATE.start_KbFilter_AddDevice_~#device~0#1.base"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_6421 Int) (v_ArrVal_6424 Int)) (not (<= (mod (select (select (store |#memory_int| |ULTIMATE.start_KbFilter_AddDevice_#t~mem27#1.base| (store (select |#memory_int| |ULTIMATE.start_KbFilter_AddDevice_#t~mem27#1.base|) (+ |ULTIMATE.start_KbFilter_AddDevice_#t~mem27#1.offset| 28) |ULTIMATE.start_KbFilter_AddDevice_#t~nondet29#1|)) (select (select (store |#memory_$Pointer$.base| |ULTIMATE.start_KbFilter_AddDevice_#t~mem27#1.base| (store (select |#memory_$Pointer$.base| |ULTIMATE.start_KbFilter_AddDevice_#t~mem27#1.base|) (+ |ULTIMATE.start_KbFilter_AddDevice_#t~mem27#1.offset| 28) v_ArrVal_6421)) |ULTIMATE.start_KbFilter_AddDevice_~#device~0#1.base|) |ULTIMATE.start_KbFilter_AddDevice_~#device~0#1.offset|)) (+ (select (select (store |#memory_$Pointer$.offset| |ULTIMATE.start_KbFilter_AddDevice_#t~mem27#1.base| (store (select |#memory_$Pointer$.offset| |ULTIMATE.start_KbFilter_AddDevice_#t~mem27#1.base|) (+ |ULTIMATE.start_KbFilter_AddDevice_#t~mem27#1.offset| 28) v_ArrVal_6424)) |ULTIMATE.start_KbFilter_AddDevice_~#device~0#1.base|) |ULTIMATE.start_KbFilter_AddDevice_~#device~0#1.offset|) 28)) 4294967296) 0)))";
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
	public void qeMod40615611() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "sep_~i~0", "sep_#in~x.base", "sep_#in~x.offset", "sep_~x.base", "sep_~x.offset"),
		};
		final String formulaAsString = "(forall ((|#memory_int| (Array Int (Array Int Int)))) (or (not (= (mod (select (select |#memory_int| sep_~x.base) (+ sep_~x.offset (* sep_~i~0 4))) 2) 0)) (= (mod (select (select |#memory_int| |sep_#in~x.base|) |sep_#in~x.offset|) 2) 0)))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod47117616() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "sep_~i~0", "sep_#in~x.base", "sep_#in~x.offset", "sep_~x.base", "sep_~x.offset"),
		};
		final String formulaAsString = "(forall ((|#memory_int| (Array Int (Array Int Int)))) (or (not (= (mod (select (select |#memory_int| |sep_#in~x.base|) |sep_#in~x.offset|) 2) 0)) (= (mod (select (select |#memory_int| sep_~x.base) (+ sep_~x.offset (* sep_~i~0 4))) 2) 0)))";
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
	public void qeMod94843759() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#__CS_thread_status~0.base", "~#__CS_thread_lockedon~0.base", "~#data~0.base", "~#__CS_thread_born_round~0.base", "~#__CS_thread_allocated~0.base", "~#mutex~0.base", "~#__CS_thread_allocated~0.offset"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_2684 (Array Int Int)) (v_ArrVal_2683 (Array Int Int)) (v_ArrVal_2694 (Array Int Int)) (v_ArrVal_2686 (Array Int Int)) (v_ArrVal_2687 (Array Int Int)) (v_ArrVal_2690 (Array Int Int))) (= (mod (mod (select (select (store (store (store (store (store (store |#memory_int| |~#__CS_thread_status~0.base| v_ArrVal_2684) |~#__CS_thread_lockedon~0.base| v_ArrVal_2683) |~#mutex~0.base| v_ArrVal_2694) |~#data~0.base| v_ArrVal_2686) |~#__CS_thread_born_round~0.base| v_ArrVal_2687) |~#__CS_thread_status~0.base| v_ArrVal_2690) |~#__CS_thread_allocated~0.base|) (+ 2 |~#__CS_thread_allocated~0.offset|)) 256) 4294967296) 1))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod2944E2C6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#empty~0.base", "~#__CS_thread_status~0.base", "~#__CS_thread_lockedon~0.base", "~#full~0.base", "~#__CS_thread_born_round~0.base", "~#num~0.base", "~#m~0.base", "~#__CS_thread_allocated~0.base", "~#__CS_thread_allocated~0.offset"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_6151 (Array Int Int)) (v_ArrVal_6148 (Array Int Int)) (v_ArrVal_6156 (Array Int Int)) (v_ArrVal_6150 (Array Int Int)) (v_ArrVal_6146 (Array Int Int)) (v_ArrVal_6158 (Array Int Int)) (v_ArrVal_6160 (Array Int Int)) (v_ArrVal_6162 (Array Int Int))) (= (mod (mod (select (select (store (store (store (store (store (store (store (store |#memory_int| |~#__CS_thread_status~0.base| v_ArrVal_6151) |~#__CS_thread_lockedon~0.base| v_ArrVal_6148) |~#num~0.base| v_ArrVal_6156) |~#m~0.base| v_ArrVal_6150) |~#empty~0.base| v_ArrVal_6146) |~#full~0.base| v_ArrVal_6158) |~#__CS_thread_born_round~0.base| v_ArrVal_6160) |~#__CS_thread_status~0.base| v_ArrVal_6162) |~#__CS_thread_allocated~0.base|) (+ |~#__CS_thread_allocated~0.offset| 1)) 256) 4294967296) 1))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod779F44B9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#__CS_thread_status~0.base", "~#__CS_thread_lockedon~0.base", "~#x~0.base", "~#__CS_thread_born_round~0.base", "~#__CS_thread_allocated~0.base", "~#flag1~0.base", "~#flag2~0.base", "~#__CS_thread_allocated~0.offset"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_19887 (Array Int Int)) (v_ArrVal_19888 (Array Int Int)) (v_ArrVal_19892 (Array Int Int)) (v_ArrVal_19881 (Array Int Int)) (v_ArrVal_19886 (Array Int Int)) (v_ArrVal_19889 (Array Int Int)) (v_ArrVal_19875 (Array Int Int))) (= (mod (mod (select (select (store (store (store (store (store (store (store |#memory_int| |~#__CS_thread_status~0.base| v_ArrVal_19887) |~#__CS_thread_lockedon~0.base| v_ArrVal_19888) |~#flag1~0.base| v_ArrVal_19892) |~#flag2~0.base| v_ArrVal_19881) |~#x~0.base| v_ArrVal_19886) |~#__CS_thread_born_round~0.base| v_ArrVal_19889) |~#__CS_thread_status~0.base| v_ArrVal_19875) |~#__CS_thread_allocated~0.base|) (+ |~#__CS_thread_allocated~0.offset| 1)) 256) 4294967296) 1))";
		final String expectedResult = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDiv72B59E81() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "v_ULTIMATE.start_mkdup_~i~0#1_BEFORE_CALL_6"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_main_~a~0#1.offset_BEFORE_CALL_3| Int) (|v_ULTIMATE.start_mkdup_~a#1.offset_BEFORE_CALL_3| Int) (|v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_10| Int)) (or (< (+ (div (+ (- |v_ULTIMATE.start_main_~a~0#1.offset_BEFORE_CALL_3|) |v_ULTIMATE.start_mkdup_~a#1.offset_BEFORE_CALL_3| (- 5)) 4) |v_ULTIMATE.start_mkdup_~i~0#1_BEFORE_CALL_6| 2) |v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_10|) (< 2 |v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_10|)))";
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


	//@formatter:on
}