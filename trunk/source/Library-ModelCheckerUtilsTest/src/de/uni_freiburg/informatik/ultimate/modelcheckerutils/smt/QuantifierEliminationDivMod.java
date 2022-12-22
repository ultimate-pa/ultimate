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
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod3CD45A9E() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~7", "ULTIMATE.start_gcd_test_~b"),
		};
		final String formulaAsString = "(exists ((v_ULTIMATE.start_gcd_test_~a_7 Int)) (and (or (and (or (and (or (and (= ULTIMATE.start_gcd_test_~b (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256)) (not (= (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 0)) (< v_ULTIMATE.start_gcd_test_~a_7 0)) (= ULTIMATE.start_gcd_test_~b (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256))) (<= (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256) 127)) (and (or (and (= ULTIMATE.start_gcd_test_~b (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256)) (not (= (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 0)) (< v_ULTIMATE.start_gcd_test_~a_7 0)) (= (+ ULTIMATE.start_gcd_test_~b 256) (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256))) (not (<= (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256) 127)))) (or (not (< v_ULTIMATE.start_gcd_test_~a_7 0)) (= (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 0))) (and (or (and (or (and (= ULTIMATE.start_gcd_test_~b (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256)) (<= (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256) 127)) (and (= ULTIMATE.start_gcd_test_~b (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256)) (not (<= (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256) 127)))) (<= (mod (+ ULTIMATE.start_main_~y~7 (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7)) 256) 127)) (and (or (and (= ULTIMATE.start_gcd_test_~b (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256)) (<= (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256) 127)) (and (= ULTIMATE.start_gcd_test_~b (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256)) (not (<= (mod (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 256) 127)))) (not (<= (mod (+ ULTIMATE.start_main_~y~7 (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7)) 256) 127)))) (not (= (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) 0)) (< v_ULTIMATE.start_gcd_test_~a_7 0))) (<= (mod (+ (mod v_ULTIMATE.start_gcd_test_~a_7 ULTIMATE.start_main_~y~7) (* ULTIMATE.start_main_~y~7 255)) 256) 127)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod8A1BCADA() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((aux_div_ULTIMATE.start_main_~y~5_38 Int)) (= (mod (+ 4294967295 (* 2 aux_div_ULTIMATE.start_main_~y~5_38)) 4294967296) 0))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModE688E331() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start___VERIFIER_assert_~cond"),
		};
		final String formulaAsString = "(exists ((ULTIMATE.start_main_~z~5 Int) (ULTIMATE.start_main_~y~5 Int) (aux_div_ULTIMATE.start_main_~x~5_32 Int)) (and (or (and (not (= (mod (+ ULTIMATE.start_main_~z~5 ULTIMATE.start_main_~y~5 (* aux_div_ULTIMATE.start_main_~x~5_32 4)) 4294967296) 1)) (= 1 ULTIMATE.start___VERIFIER_assert_~cond)) (and (= (mod (+ ULTIMATE.start_main_~z~5 ULTIMATE.start_main_~y~5 (* aux_div_ULTIMATE.start_main_~x~5_32 4)) 4294967296) 1) (= 0 ULTIMATE.start___VERIFIER_assert_~cond))) (= (mod (* ULTIMATE.start_main_~y~5 3) 4) 0) (= (mod (* ULTIMATE.start_main_~z~5 7) 8) 0)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModAC3DF136() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start___VERIFIER_assert_~cond"),
		};
		final String formulaAsString = "(exists ((ULTIMATE.start_main_~y~5 Int) (ULTIMATE.start_main_~z~5 Int) (aux_div_ULTIMATE.start_main_~x~5_32 Int)) (and (= (mod (* ULTIMATE.start_main_~y~5 3) 4) 0) (= (mod (* ULTIMATE.start_main_~z~5 7) 8) 0) (or (and (not (= 4 (mod (+ (* ULTIMATE.start_main_~y~5 2) ULTIMATE.start_main_~z~5 (* 8 aux_div_ULTIMATE.start_main_~x~5_32)) 4294967296))) (= 1 ULTIMATE.start___VERIFIER_assert_~cond)) (and (= 4 (mod (+ (* ULTIMATE.start_main_~y~5 2) ULTIMATE.start_main_~z~5 (* 8 aux_div_ULTIMATE.start_main_~x~5_32)) 4294967296)) (= 0 ULTIMATE.start___VERIFIER_assert_~cond)))))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod5C13FE76() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start___VERIFIER_assert_~cond"),
		};
		final String formulaAsString = "(exists ((ULTIMATE.start_main_~z~5 Int) (ULTIMATE.start_main_~y~5 Int) (ULTIMATE.start_main_~x~5 Int)) (and (= (mod (* ULTIMATE.start_main_~z~5 4194303) 4194304) 0) (= (mod (* ULTIMATE.start_main_~x~5 1048575) 1048576) 0) (or (and (= 1 ULTIMATE.start___VERIFIER_assert_~cond) (not (= (mod (+ ULTIMATE.start_main_~z~5 (* ULTIMATE.start_main_~y~5 4294967294) (* ULTIMATE.start_main_~x~5 4)) 4294967296) 1048576))) (and (= 0 ULTIMATE.start___VERIFIER_assert_~cond) (= (mod (+ ULTIMATE.start_main_~z~5 (* ULTIMATE.start_main_~y~5 4294967294) (* ULTIMATE.start_main_~x~5 4)) 4294967296) 1048576))) (= (mod (* 2097151 ULTIMATE.start_main_~y~5) 2097152) 0)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod33825C1E() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((~p1_old Int) (~send1 Int)) (and (= ~p1_old (mod ~send1 256)) (<= (mod ~send1 256) 127)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod824A9EA1() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((~alive1 Int)) (= (mod ~alive1 256) 0))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod8DD1F76C() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((ULTIMATE.start_ssl3_connect_~__cil_tmp56~4 Int)) (= (mod (+ ULTIMATE.start_ssl3_connect_~__cil_tmp56~4 18446744073709551360) 18446744073709551616) 0))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod8282A8D6() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((ULTIMATE.start_ssl3_connect_~__cil_tmp64~4 Int)) (= (mod (+ ULTIMATE.start_ssl3_connect_~__cil_tmp64~4 256) 18446744073709551616) 0))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDivModB3099151() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 Int) (aux_div_aux_mod_ULTIMATE.start_main_~n~6_41_52 Int) (aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 Int)) (and (not (= (mod (div (mod (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63)) 18446744073709551616) 2) 18446744073709551616) 1)) (< (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_div_aux_mod_ULTIMATE.start_main_~n~6_41_52 4294967296) (* aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296)) 4294967296) (<= 1 (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_div_aux_mod_ULTIMATE.start_main_~n~6_41_52 4294967296) (* aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296))) (<= 0 (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296))) (< (+ aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 (* aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296)) 2) (< aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63 4294967296) (<= 0 aux_mod_aux_mod_aux_mod_ULTIMATE.start_main_~n~6_41_52_63)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModF059E9EA() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_~x~0"),
		};
		final String formulaAsString = "(exists ((|#memory_int| (Array Int (Array Int Int))) (|main_~#a~0.base| Int) (|main_~#a~0.offset| Int)) (and (= (+ (select (select |#memory_int| |main_~#a~0.base|) |main_~#a~0.offset|) 1) 0) (= (mod (select (select |#memory_int| |main_~#a~0.base|) |main_~#a~0.offset|) 256) main_~x~0)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModC44E259() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_~x~0"),
		};
		final String formulaAsString = "(exists ((|#memory_int| (Array Int (Array Int Int))) (|main_~#cp~0.base| Int) (|main_~#cp~0.offset| Int)) (and (= (mod (select (select |#memory_int| |main_~#cp~0.base|) |main_~#cp~0.offset|) 256) main_~x~0) (= (+ (select (select |#memory_int| |main_~#cp~0.base|) |main_~#cp~0.offset|) 1) 0)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod4C35A753() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_~snd~0"),
		};
		final String formulaAsString = "(exists ((|#memory_int| (Array Int (Array Int Int))) (main_~p~0.base Int) (main_~p~0.offset Int) (|v_#Ultimate.C_memset_#ptr.offset_AFTER_CALL_5| Int)) (and (= (+ (select (select |#memory_int| main_~p~0.base) (+ 2 |v_#Ultimate.C_memset_#ptr.offset_AFTER_CALL_5|)) 1) 0) (<= 0 |v_#Ultimate.C_memset_#ptr.offset_AFTER_CALL_5|) (<= main_~p~0.offset 0) (<= |v_#Ultimate.C_memset_#ptr.offset_AFTER_CALL_5| main_~p~0.offset) (= (mod (select (select |#memory_int| main_~p~0.base) (+ 2 main_~p~0.offset)) 256) main_~snd~0)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod22274A50() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_~pos~0"),
		};
		final String formulaAsString = "(exists ((aux_mod_v_main_~pos~0_9_35 Int) (aux_div_v_main_~pos~0_9_35 Int)) (and (<= 254 aux_mod_v_main_~pos~0_9_35) (< 0 (+ 256 aux_mod_v_main_~pos~0_9_35 (* aux_div_v_main_~pos~0_9_35 256))) (= (+ (mod (+ (* 255 aux_mod_v_main_~pos~0_9_35) 2) 256) 2) main_~pos~0) (<= (+ aux_mod_v_main_~pos~0_9_35 (* aux_div_v_main_~pos~0_9_35 256)) 0) (< aux_mod_v_main_~pos~0_9_35 256)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDivModE208D894() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "main_a"),
			new FunDecl(SmtSortUtils::getIntSort, "main_p", "main_q"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_4 Int) (v_arrayElimCell_3 Int)) (and (= (select main_a main_p) (mod (+ v_arrayElimCell_4 (div v_arrayElimCell_3 2)) 4294967296)) (or (= main_q main_p) (= v_arrayElimCell_4 (select main_a main_q))) (or (not (= main_q main_p)) (= v_arrayElimCell_4 v_arrayElimCell_3)) (<= 0 v_arrayElimCell_4) (or (= main_q main_p) (<= v_arrayElimCell_4 500)) (= v_arrayElimCell_3 1000)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDivMod79A79F74() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_a_p"),
		};
		final String formulaAsString = "(exists ((v_main_a_p_18 Int) (aux_div_v_main_a_q_17_56 Int)) (and (= (mod (+ 4294966796 (* 4294967295 main_a_p) (div v_main_a_p_18 2) v_main_a_p_18) 4294967296) 0) (<= (+ (* aux_div_v_main_a_q_17_56 4294967296) (* 4294967296 (div (+ (- 500) (div v_main_a_p_18 2) (* (- 1) main_a_p) v_main_a_p_18) (- 4294967296))) v_main_a_p_18) 1000) (<= 0 v_main_a_p_18) (<= 500 (+ (* aux_div_v_main_a_q_17_56 4294967296) (* 4294967296 (div (+ (- 500) (div v_main_a_p_18 2) (* (- 1) main_a_p) v_main_a_p_18) (- 4294967296))) v_main_a_p_18)) (< v_main_a_p_18 4294967296)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDiv4686750A() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "main_m"),
			new FunDecl(SmtSortUtils::getIntSort, "main_eat", "main_init", "main_cakeLeft"),
		};
		final String formulaAsString = "(exists ((v_main_m_14 (Array Int Int)) (v_ArrVal_17 Int) (v_ArrVal_16 Int) (v_ArrVal_18 Int)) (and (or (= main_eat main_cakeLeft) (<= main_init (select v_main_m_14 main_cakeLeft))) (= main_m (store (store v_main_m_14 main_eat v_ArrVal_17) main_cakeLeft v_ArrVal_16)) (<= (select v_main_m_14 main_eat) (select v_main_m_14 main_cakeLeft)) (<= (select (store v_main_m_14 main_eat v_ArrVal_18) main_cakeLeft) (+ (div (select v_main_m_14 main_eat) 2) v_ArrVal_16))))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDiv7C176B87() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "main_m"),
			new FunDecl(SmtSortUtils::getIntSort, "main_eat", "main_init", "main_cakeLeft"),
		};
		final String formulaAsString = "(exists ((v_main_m_12 (Array Int Int)) (v_ArrVal_11 Int) (v_ArrVal_10 Int)) (and (or (and (<= (+ (div main_init 2) (select v_main_m_12 main_eat)) (select v_main_m_12 main_cakeLeft)) (<= 0 (select v_main_m_12 main_eat))) (= main_eat main_cakeLeft)) (= (store (store v_main_m_12 main_eat (div (select v_main_m_12 main_eat) 2)) main_cakeLeft v_ArrVal_11) main_m) (<= (select (store v_main_m_12 main_eat v_ArrVal_10) main_cakeLeft) (+ v_ArrVal_11 (div (select v_main_m_12 main_eat) 2)))))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod58B32222() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((aux_div_main_yold_19 Int) (main_x Int) (aux_div_main_xold_25 Int) (main_a (Array Int Int))) (and (= (select main_a (+ (- 1) main_x (* 256 aux_div_main_xold_25))) (select main_a (mod (+ main_x 1) 256))) (= (select main_a main_x) (select main_a (+ (- 1) main_x (* 256 aux_div_main_xold_25)))) (<= 1 (+ main_x (* 256 aux_div_main_xold_25))) (< (+ main_x (* 256 aux_div_main_xold_25)) 257) (= (select main_a (+ (- 1) main_x (* 256 aux_div_main_xold_25))) (select main_a (+ (* 256 aux_div_main_yold_19) (- 2) main_x (* 256 aux_div_main_xold_25)))) (= (select main_a main_x) 0) (<= 0 main_x) (< main_x 256) (= (select main_a (+ (- 1) main_x (* 256 aux_div_main_xold_25))) 1000)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModDA7283E() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "main_y", "aux_mod_v_main_y_22_19"),
		};
		final String formulaAsString = "(exists ((aux_div_v_main_y_22_19 Int)) (= main_y (mod (+ (* 4294967294 aux_mod_v_main_y_22_19) 1 (* 4294967292 aux_div_v_main_y_22_19)) 4294967296)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModF7E66B88() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "aux_mod_v_main_~x~0_19_31", "main_~x~0", "main_~y~0"),
		};
		final String formulaAsString = "(exists ((aux_div_v_main_~x~0_19_31 Int)) (and (= (mod (+ aux_mod_v_main_~x~0_19_31 aux_div_v_main_~x~0_19_31) 3) 0) (or (and (= (div (+ aux_mod_v_main_~x~0_19_31 (* aux_div_v_main_~x~0_19_31 4294967296)) 3) 1) (= (div (+ (- (div (+ (- main_~y~0) 1) 2)) 1) 2) 1)) (and (= 3 (div (+ aux_mod_v_main_~x~0_19_31 (* aux_div_v_main_~x~0_19_31 4294967296)) 3)) (= (+ (div (+ (- (div (+ (- main_~y~0) 1) 2)) 1) 2) 1) 0))) (= (+ (* aux_mod_v_main_~x~0_19_31 3) (* aux_div_v_main_~x~0_19_31 12884901888)) main_~x~0)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModBEF5E320() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "main_~#a~0.base", "main_~#a~0.offset"),
		};
		final String formulaAsString = "(exists ((main_~x~0 Int)) (and (= (select (select |#memory_int| |main_~#a~0.base|) (+ |main_~#a~0.offset| (* (mod main_~x~0 4294967296) 4))) 0) (<= 0 main_~x~0) (< main_~x~0 128)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModFE53C0DD() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_6| Int)) (= (mod (* 16777215 |v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_6|) 16777216) 0))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod619EF237() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_23| Int)) (= (mod (* |v_ULTIMATE.start_main_~a~0#1_BEFORE_CALL_23| 16777215) 16777216) 0))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModE2840B20() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~p1_new~0", "~id3~0", "~nomsg~0"),
		};
		final String formulaAsString = "(exists ((~send1~0 Int)) (and (<= (mod ~send1~0 256) 127) (<= ~send1~0 127) (= ~p1_new~0 (mod ~send1~0 256)) (not (= ~send1~0 ~id3~0)) (not (= ~send1~0 ~nomsg~0)) (<= 0 ~send1~0)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod2CD67151() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~nomsg~0", "~p4_new~0"),
		};
		final String formulaAsString = "(exists ((~send4~0 Int)) (and (not (<= (mod ~send4~0 256) 127)) (<= 0 ~send4~0) (<= ~send4~0 127) (or (and (not (= ~send4~0 ~nomsg~0)) (= (+ ~p4_new~0 256) (mod ~send4~0 256))) (and (= ~p4_new~0 (mod ~nomsg~0 256)) (= ~send4~0 ~nomsg~0)))))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModF0164ADC() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~p1_new~0", "~nomsg~0"),
		};
		final String formulaAsString = "(exists ((~send1~0 Int)) (and (<= ~send1~0 127) (not (= ~send1~0 ~nomsg~0)) (<= (mod ~send1~0 256) (+ 256 ~p1_new~0)) (not (<= (mod ~send1~0 256) 127)) (<= 0 ~send1~0)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDivMod87C893B3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~a29~0"),
		};
		final String formulaAsString = "(exists ((v_~a29~0_897 Int)) (and (<= ~a29~0 (+ (div (+ v_~a29~0_897 (- 142312)) 5) 1)) (not (= (mod (+ 3 v_~a29~0_897) 5) 0)) (<= (+ v_~a29~0_897 127) 0)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod3862CCBE() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~a28~0"),
		};
		final String formulaAsString = "(exists ((v_~a28~0_1300 Int)) (and (<= v_~a28~0_1300 111) (not (= (mod (+ v_~a28~0_1300 4) 5) 0)) (or (and (<= ~a28~0 (+ (div (+ (div (+ v_~a28~0_1300 (- 600036)) 5) 1) 5) 1)) (< (+ (div (+ v_~a28~0_1300 (- 600036)) 5) 1) 0) (not (= (mod (+ (div (+ v_~a28~0_1300 (- 600036)) 5) 1) 5) 0))) (and (<= ~a28~0 (div (+ (div (+ v_~a28~0_1300 (- 600036)) 5) 1) 5)) (or (not (< (+ (div (+ v_~a28~0_1300 (- 600036)) 5) 1) 0)) (= (mod (+ (div (+ v_~a28~0_1300 (- 600036)) 5) 1) 5) 0))))))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModC4A49E94() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~var_23~0#1| Int)) (and (<= 0 |ULTIMATE.start_main_~var_23~0#1|) (= (mod |ULTIMATE.start_main_~var_23~0#1| 256) 0) (< |ULTIMATE.start_main_~var_23~0#1| 256)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModCCCC5BE3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_#t~mem36#1"),
		};
		final String formulaAsString = "(exists ((|#memory_int| (Array Int (Array Int Int))) (|ULTIMATE.start_main_~#new_packet~0#1.base| Int) (|ULTIMATE.start_main_~#new_packet~0#1.offset| Int) (|v_ULTIMATE.start_receive_~#packet~0#1.base_10| Int)) (and (= (select (select |#memory_int| |v_ULTIMATE.start_receive_~#packet~0#1.base_10|) 4) (select (select |#memory_int| |ULTIMATE.start_main_~#new_packet~0#1.base|) (+ 4 |ULTIMATE.start_main_~#new_packet~0#1.offset|))) (= (mod (select (select |#memory_int| |ULTIMATE.start_main_~#new_packet~0#1.base|) (+ 4 |ULTIMATE.start_main_~#new_packet~0#1.offset|)) 4294967296) 1) (= |ULTIMATE.start_main_#t~mem36#1| (select (select |#memory_int| |ULTIMATE.start_main_~#new_packet~0#1.base|) (+ 4 |ULTIMATE.start_main_~#new_packet~0#1.offset|)))))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModBB65ABF4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53_73"),
		};
		final String formulaAsString = "(exists ((|aux_div_ULTIMATE.start_main_~main__x~0#1_66| Int) (|aux_div_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53| Int)) (and (<= 0 (+ (* |aux_div_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53| 3) (* 4294967296 |aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53_73|) 1)) (= (mod (mod (mod (+ (* |aux_div_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53| 3) 3) 4294967296) 3) 4294967296) 0) (< (+ (* |aux_div_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53| 3) (* 4294967296 |aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53_73|)) 4294967295) (<= (+ (* |aux_div_ULTIMATE.start_main_~main__x~0#1_66| 4294967296) (* |aux_div_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53| 3) (* 4294967296 |aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53_73|)) 6442450942) (<= 2147483647 (+ (* |aux_div_ULTIMATE.start_main_~main__x~0#1_66| 4294967296) (* |aux_div_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53| 3) (* 4294967296 |aux_div_aux_mod_aux_mod_ULTIMATE.start_main_~main__x~0#1_66_53_73|)))))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDivBA566C0() {
		final FunDecl[] funDecls = new FunDecl[] {
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~n~0#1| Int)) (and (or (not (< |ULTIMATE.start_main_~n~0#1| 0)) (= (mod |ULTIMATE.start_main_~n~0#1| 2) 0)) (<= 1 (div |ULTIMATE.start_main_~n~0#1| 2))))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModEDB1EF13() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "aux_mod_ULTIMATE.start_main_~z~0#1_45"),
		};
		final String formulaAsString = "(exists ((|aux_mod_ULTIMATE.start_main_~n~0#1_45| Int)) (and (not (= (mod |aux_mod_ULTIMATE.start_main_~n~0#1_45| 4294967296) (mod |aux_mod_ULTIMATE.start_main_~z~0#1_45| 4294967296))) (<= |aux_mod_ULTIMATE.start_main_~n~0#1_45| 0) (<= 0 |aux_mod_ULTIMATE.start_main_~n~0#1_45|)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModA007BB5B() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_student_version_~w#1"),
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~w~0#1| Int)) (and (not (<= (mod |ULTIMATE.start_main_~w~0#1| 4294967296) 2147483647)) (or (and (<= |ULTIMATE.start_student_version_~w#1| (mod |ULTIMATE.start_main_~w~0#1| 4294967296)) (<= (mod |ULTIMATE.start_main_~w~0#1| 4294967296) 2147483647)) (and (not (<= (mod |ULTIMATE.start_main_~w~0#1| 4294967296) 2147483647)) (<= (+ |ULTIMATE.start_student_version_~w#1| 4294967296) (mod |ULTIMATE.start_main_~w~0#1| 4294967296))))))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDivModE995CB24() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1| Int) (|v_ULTIMATE.start_main_~ret~1#1_BEFORE_CALL_1| Int)) (and (not (<= (mod (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 4294967296) 2147483647)) (or (and (or (and (= (mod (+ (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 1) 4294967296) (+ |v_ULTIMATE.start_main_~ret~1#1_BEFORE_CALL_1| 4294967296)) (not (= 0 (mod (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10))) (< (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 0)) (and (or (not (< (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 0)) (= 0 (mod (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10))) (= (mod (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 4294967296) (+ |v_ULTIMATE.start_main_~ret~1#1_BEFORE_CALL_1| 4294967296)))) (not (<= (mod (+ (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 1) 4294967296) 2147483647))) (and (<= (mod (+ (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 1) 4294967296) 2147483647) (or (and (or (not (< (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 0)) (= 0 (mod (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10))) (= (mod (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 4294967296) (+ |v_ULTIMATE.start_main_~ret~1#1_BEFORE_CALL_1| 4294967296))) (and (not (= 0 (mod (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10))) (< (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 0) (= |v_ULTIMATE.start_main_~ret~1#1_BEFORE_CALL_1| (mod (+ (div (+ (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 28) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 12) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 20) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 32) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 16) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 24) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 36) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 8) (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 0)) 10) 1) 4294967296))))))))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod115C8EE3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#x~0#1.offset", "ULTIMATE.start_main_~ret~1#1", "ULTIMATE.start_main_~#x~0#1.base"),
		};
		final String formulaAsString = "(exists ((|v_#memory_int_24| (Array Int (Array Int Int))) (v_ArrVal_325 Int) (v_ArrVal_324 Int)) (and (= |#memory_int| (store |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base| (store (store (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) |ULTIMATE.start_main_~#x~0#1.offset| v_ArrVal_325) (+ 4 |ULTIMATE.start_main_~#x~0#1.offset|) v_ArrVal_324))) (<= 1 (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) |ULTIMATE.start_main_~#x~0#1.offset|)) (<= (+ 1 (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 12 |ULTIMATE.start_main_~#x~0#1.offset|))) (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 16 |ULTIMATE.start_main_~#x~0#1.offset|))) (<= (+ (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 4 |ULTIMATE.start_main_~#x~0#1.offset|)) 1) (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 8 |ULTIMATE.start_main_~#x~0#1.offset|))) (<= (+ (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) |ULTIMATE.start_main_~#x~0#1.offset|) 1) (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 4 |ULTIMATE.start_main_~#x~0#1.offset|))) (= |ULTIMATE.start_main_~ret~1#1| (mod (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 16 |ULTIMATE.start_main_~#x~0#1.offset|)) 4294967296)) (<= (+ (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 8 |ULTIMATE.start_main_~#x~0#1.offset|)) 1) (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 12 |ULTIMATE.start_main_~#x~0#1.offset|))) (<= (select (select |v_#memory_int_24| |ULTIMATE.start_main_~#x~0#1.base|) (+ 16 |ULTIMATE.start_main_~#x~0#1.offset|)) 2147483647)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeMod9C6A4266() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#x~0#1.offset", "ULTIMATE.start_main_~temp~0#1", "ULTIMATE.start_main_~#x~0#1.base"),
		};
		final String formulaAsString = "(exists ((|#memory_int| (Array Int (Array Int Int)))) (and (not (= (mod (select (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|) |ULTIMATE.start_main_~#x~0#1.offset|) 2) 0)) (= (select (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|) |ULTIMATE.start_main_~#x~0#1.offset|) |ULTIMATE.start_main_~temp~0#1|)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModB61935DD() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~p2_new~0"),
		};
		final String formulaAsString = "(exists ((~send2~0 Int)) (and (<= (mod ~send2~0 256) 127) (<= 0 ~send2~0) (<= ~send2~0 127) (= (mod ~send2~0 256) ~p2_new~0)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModE5BC6CE6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~p5_old~0"),
		};
		final String formulaAsString = "(exists ((~send5~0 Int)) (and (<= 0 ~send5~0) (not (<= (mod ~send5~0 256) 127)) (<= ~send5~0 127) (= (+ 256 ~p5_old~0) (mod ~send5~0 256))))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModFD34F53D() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~p6_new~0"),
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~node6____CPAchecker_TMP_0~0#1| Int)) (and (<= |ULTIMATE.start_main_~node6____CPAchecker_TMP_0~0#1| 127) (= (mod |ULTIMATE.start_main_~node6____CPAchecker_TMP_0~0#1| 256) ~p6_new~0) (<= 0 |ULTIMATE.start_main_~node6____CPAchecker_TMP_0~0#1|) (<= (mod |ULTIMATE.start_main_~node6____CPAchecker_TMP_0~0#1| 256) 127)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeModC0B8F0E9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(SmtSortUtils::getIntSort, "~send4~0", "~p4_new~0"),
		};
		final String formulaAsString = "(exists ((~nomsg~0 Int)) (and (or (and (not (<= (mod ~send4~0 256) 127)) (or (and (not (= ~send4~0 ~nomsg~0)) (= (+ ~p4_new~0 256) (mod ~send4~0 256))) (and (= (mod ~nomsg~0 256) (+ ~p4_new~0 256)) (= ~send4~0 ~nomsg~0)))) (and (<= (mod ~send4~0 256) 127) (or (and (not (= ~send4~0 ~nomsg~0)) (= ~p4_new~0 (mod ~send4~0 256))) (and (= (mod ~nomsg~0 256) (+ ~p4_new~0 256)) (= ~send4~0 ~nomsg~0))))) (not (<= (mod ~nomsg~0 256) 127))))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void qeDiv77A7B16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~a~0#1.offset", "ULTIMATE.start_main_~a~0#1.base"),
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~n~0#1| Int) (v_ArrVal_62 Int) (v_arrayElimCell_1 Int)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (+ |ULTIMATE.start_main_~a~0#1.offset| (- 4) (* |ULTIMATE.start_main_~n~0#1| 4))) v_ArrVal_62) (<= |ULTIMATE.start_main_~n~0#1| 2) (= v_arrayElimCell_1 (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (+ |ULTIMATE.start_main_~a~0#1.offset| (- 4) (* (div |ULTIMATE.start_main_~n~0#1| 2) 4)))) (< 1 |ULTIMATE.start_main_~n~0#1|) (= v_arrayElimCell_1 0)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}





	//@formatter:on
}