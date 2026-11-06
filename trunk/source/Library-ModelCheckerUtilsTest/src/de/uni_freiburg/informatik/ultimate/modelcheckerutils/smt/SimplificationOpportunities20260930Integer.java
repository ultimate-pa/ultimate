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
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.experimental.categories.Category;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.StatisticsScript;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.test.junitextension.categories.NoRegression;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
// These tests are are used for benchmarking and should not run as regression tests.
@Category(NoRegression.class)
public class SimplificationOpportunities20260930Integer {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY = false;
	private static final long TEST_TIMEOUT_MILLISECONDS = 60_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	// private static final String SOLVER_COMMAND = "cvc4 --incremental --lang smt";
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:12000 -memory:2024 -smt2 -in";
	// private static final String SOLVER_COMMAND = "INTERNAL_SMTINTERPOL:10000";

	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.SIMPLIFY_DDA2;

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private static QuantifierEliminationTestCsvWriter mCsvWriter;

	@BeforeClass
	public static void beforeAllTests() {
		mCsvWriter = new QuantifierEliminationTestCsvWriter(
				SimplificationOpportunities20260930Integer.class.getSimpleName());
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
		mScript = new StatisticsScript(mScript);

		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
	}

	@After
	public void tearDown() {
		mScript.exit();
		mCsvWriter.reportTestFinished();
	}

	// @formatter:off

	@Test
	public void SimplificationOpportunity_10415639_ffe40b4d_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_right_trim_pred_~source.base_BEFORE_CALL_22 Int)) (<= 8691 (select |#memory_$Pointer$.base| (+ v_aws_byte_cursor_right_trim_pred_~source.base_BEFORE_CALL_22 4))))";
		final String expectedResultAsString = "(exists ((v_aws_byte_cursor_right_trim_pred_~source.base_BEFORE_CALL_21 Int)) (<= 8691 (select |#memory_$Pointer$.base| (+ v_aws_byte_cursor_right_trim_pred_~source.base_BEFORE_CALL_21 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1133e728_43c53cbf_Treesizes_26_21() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0", "~var_1_4~0", "~var_1_2~0", "~var_1_3~0"),
		};
		final String formulaAsString = "(and (= (div ~var_1_1~0 4294967296) 0) (= ~var_1_1~0 (mod ~var_1_3~0 65536)) (not (= (mod ~var_1_2~0 256) 0)) (<= (+ (mod ~var_1_4~0 65536) 1) (mod ~var_1_3~0 65536)))";
		final String expectedResultAsString = "(let ((.cse0 (mod ~var_1_3~0 65536))) (and (= ~var_1_1~0 .cse0) (not (= (mod ~var_1_2~0 256) 0)) (<= (+ (mod ~var_1_4~0 65536) 1) .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_11d1cd74_16db25b4_Treesizes_20_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base"),
		};
		final String formulaAsString = "(and (<= (mod (* (select |#memory_int| |aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base|) 4294967295) 4294967296) 0) (exists ((|v_aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_10| Int)) (<= (mod (* 4294967295 (select |#memory_int| |v_aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_10|)) 4294967296) 0)))";
		final String expectedResultAsString = "(<= (mod (* (select |#memory_int| |aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base|) 4294967295) 4294967296) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_12605813_2f4e4e79_Treesizes_6_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "mcp251x_can_probe_ldv_net_dummy_resourceless_instance_2_~data~2#1.base"),
		};
		final String formulaAsString = "(not (= (mod |mcp251x_can_probe_ldv_net_dummy_resourceless_instance_2_~data~2#1.base| 4294967296) 0))";
		final String expectedResultAsString = "(<= 1 (mod |mcp251x_can_probe_ldv_net_dummy_resourceless_instance_2_~data~2#1.base| 4294967296))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_12c5ce9d_d6d7584e_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base_BEFORE_CALL_88| Int)) (and (<= (+ 16 |v_ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base_BEFORE_CALL_88|) |#StackAllocations|) (<= 8681 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base_BEFORE_CALL_88| 4)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base_BEFORE_CALL_87| Int)) (and (<= 8681 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base_BEFORE_CALL_87| 4))) (<= (+ 16 |v_ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base_BEFORE_CALL_87|) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_133da72b_b4f32660_Treesizes_12_5() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_from_empty_array_~#buf~2#1.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| |ULTIMATE.start_aws_byte_buf_from_empty_array_~#buf~2#1.base|) 0) (exists ((|v_ULTIMATE.start_aws_byte_buf_from_empty_array_~#buf~2#1.base_BEFORE_CALL_5| Int)) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_from_empty_array_~#buf~2#1.base_BEFORE_CALL_5|) 0)))";
		final String expectedResultAsString = "(= (select |#memory_int| |ULTIMATE.start_aws_byte_buf_from_empty_array_~#buf~2#1.base|) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_145e97ef_7957dbd5_Treesizes_28_28() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_ignore_case_~a#1.base_BEFORE_CALL_11| Int)) (and (<= (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_ignore_case_~a#1.base_BEFORE_CALL_11|)) 4294967296) 15) (<= 328 |v_ULTIMATE.start_aws_string_eq_ignore_case_~a#1.base_BEFORE_CALL_11|) (= (select |#memory_int| (+ (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_ignore_case_~a#1.base_BEFORE_CALL_11|)) 4294967296) 8 |v_ULTIMATE.start_aws_string_eq_ignore_case_~a#1.base_BEFORE_CALL_11|)) 0)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_9| Int)) (let ((.cse0 (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_9|)) 4294967296))) (and (= (select |#memory_int| (+ .cse0 8 |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_9|)) 0) (<= 328 |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_9|) (<= .cse0 15))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_147aa7e5_dc28f620_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_46| Int)) (and (<= 50 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_46| 4))) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_46| 8) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_42| Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_42| 8) |#StackAllocations|) (<= 50 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_42| 4)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_14bdf044_b4660e57_Treesizes_25_19() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~w~0#1", "ULTIMATE.start_correct_version_~w#1"),
		};
		final String formulaAsString = "(or (and (<= 2147483648 (mod |ULTIMATE.start_main_~w~0#1| 4294967296)) (<= (+ 4294967296 |ULTIMATE.start_correct_version_~w#1|) (mod |ULTIMATE.start_main_~w~0#1| 4294967296))) (and (<= |ULTIMATE.start_correct_version_~w#1| (mod |ULTIMATE.start_main_~w~0#1| 4294967296)) (<= (mod |ULTIMATE.start_main_~w~0#1| 4294967296) 2147483647)))";
		final String expectedResultAsString = "(let ((.cse0 (mod |ULTIMATE.start_main_~w~0#1| 4294967296))) (or (< (+ 4294967295 |ULTIMATE.start_correct_version_~w#1|) .cse0) (and (<= |ULTIMATE.start_correct_version_~w#1| .cse0) (<= .cse0 2147483647))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_159f6c25_b7e318ce_Treesizes_9_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_byte_cursor_right_trim_pred_#in~source.base"),
		};
		final String formulaAsString = "(<= (mod (* 4294967295 (select |#memory_int| |aws_byte_cursor_right_trim_pred_#in~source.base|)) 4294967296) 0)";
		final String expectedResultAsString = "(<= (mod (select |#memory_int| |aws_byte_cursor_right_trim_pred_#in~source.base|) 4294967296) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_15c785c6_f1654889_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_buf_secure_zero_~buf#1.base_BEFORE_CALL_20| Int)) (and (<= 8684 (select |#memory_$Pointer$.base| (+ |v_aws_byte_buf_secure_zero_~buf#1.base_BEFORE_CALL_20| 4))) (<= (+ 2 (select |#memory_$Pointer$.base| (+ |v_aws_byte_buf_secure_zero_~buf#1.base_BEFORE_CALL_20| 4))) |v_aws_byte_buf_secure_zero_~buf#1.base_BEFORE_CALL_20|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_51| Int)) (let ((.cse0 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_51| 4)))) (and (<= 8684 .cse0) (<= (+ .cse0 2) |v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_51|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_15e1bfa9_e00c3461_Treesizes_18_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~a~0#1.base", "ULTIMATE.start_main_~DEFAULTVAL~0#1"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_3| Int)) (<= 10 (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_3|))) (= |ULTIMATE.start_main_~i~0#1| 1) (<= 10 (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|)) (<= |ULTIMATE.start_main_~DEFAULTVAL~0#1| 0))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_main_~i~0#1| 1) (<= 10 (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|)) (<= |ULTIMATE.start_main_~DEFAULTVAL~0#1| 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1652ae5c_f2b47b7e_Treesizes_71_50() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_6_Pointer~0.base", "~var_1_16_Pointer~0.base", "~var_1_8_Pointer~0.base", "~var_1_17_Pointer~0.base", "~var_1_10_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~var_1_8_Pointer~0.base ~var_1_17_Pointer~0.base)) (not (= ~var_1_6_Pointer~0.base ~var_1_16_Pointer~0.base)) (not (= ~var_1_10_Pointer~0.base ~var_1_17_Pointer~0.base)) (not (= ~var_1_8_Pointer~0.base ~var_1_16_Pointer~0.base)) (not (= ~var_1_6_Pointer~0.base ~var_1_17_Pointer~0.base)) (<= (+ (mod (+ 23071 (* (select |#memory_int| ~var_1_8_Pointer~0.base) 65535) (select |#memory_int| ~var_1_10_Pointer~0.base) (* (mod (select |#memory_int| ~var_1_6_Pointer~0.base) 256) 65535)) 65536) (mod (select |#memory_int| ~var_1_6_Pointer~0.base) 256) (mod (+ 225 (select |#memory_int| ~var_1_8_Pointer~0.base) (* 255 (select |#memory_int| ~var_1_10_Pointer~0.base)) (select |#memory_int| ~var_1_6_Pointer~0.base)) 256)) 255) (not (= ~var_1_10_Pointer~0.base ~var_1_16_Pointer~0.base)) (not (= ~var_1_8_Pointer~0.base ~var_1_6_Pointer~0.base)))";
		final String expectedResultAsString = "(and (<= (mod (+ 23071 (* (select |#memory_int| ~var_1_8_Pointer~0.base) 65535) (select |#memory_int| ~var_1_10_Pointer~0.base) (* (mod (select |#memory_int| ~var_1_6_Pointer~0.base) 256) 65535)) 65536) 0) (not (= ~var_1_8_Pointer~0.base ~var_1_17_Pointer~0.base)) (not (= ~var_1_6_Pointer~0.base ~var_1_16_Pointer~0.base)) (not (= ~var_1_10_Pointer~0.base ~var_1_17_Pointer~0.base)) (not (= ~var_1_8_Pointer~0.base ~var_1_16_Pointer~0.base)) (not (= ~var_1_6_Pointer~0.base ~var_1_17_Pointer~0.base)) (not (= ~var_1_10_Pointer~0.base ~var_1_16_Pointer~0.base)) (not (= ~var_1_8_Pointer~0.base ~var_1_6_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_16b6c849_d3b47bc2_Treesizes_84_65() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(and (or (= (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255) 10) 256) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 15))) (and (<= 128 (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255) 10) 256)) (= (+ 256 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 15))) (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255) 10) 256)))) (or (not (= (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255) 10) 256) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 15)))) (< (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255) 10) 256) 128)))";
		final String expectedResultAsString = "(let ((.cse1 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 15))) (.cse0 (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255) 10) 256))) (or (and (<= 128 .cse0) (= (+ 256 .cse1) .cse0)) (and (= .cse0 .cse1) (<= .cse0 127))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_170e5ca5_cd4d26f2_Treesizes_30_18() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~a~0", "~b~0", "~x_2~0", "~x_1~0", "thread2Thread1of1ForFork0_~i~1", "thread1Thread1of1ForFork1_~i~0"),
		};
		final String formulaAsString = "(and (<= (+ ~b~0 thread2Thread1of1ForFork0_~i~1) (+ ~x_2~0 1)) (<= ~x_2~0 ~b~0) (<= (+ 2 (mod (+ 4294967295 ~a~0) 4294967296)) (+ thread2Thread1of1ForFork0_~i~1 (mod ~a~0 4294967296))) (= thread1Thread1of1ForFork1_~i~0 0) (= ~x_1~0 0))";
		final String expectedResultAsString = "(and (= thread2Thread1of1ForFork0_~i~1 1) (<= 1 (mod ~a~0 4294967296)) (= thread1Thread1of1ForFork1_~i~0 0) (= ~x_1~0 0) (= ~x_2~0 ~b~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_17d9ffa5_535d2fc6_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_advance_~cursor#1.base_BEFORE_CALL_3| Int)) (and (<= (+ 29 |v_ULTIMATE.start_aws_byte_cursor_advance_~cursor#1.base_BEFORE_CALL_3|) |#StackAllocations|) (<= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_advance_~cursor#1.base_BEFORE_CALL_3|) 4294967296) 0)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_advance_~cursor#1.base_BEFORE_CALL_2| Int)) (and (<= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_advance_~cursor#1.base_BEFORE_CALL_2|) 4294967296) 0) (<= (+ 29 |v_ULTIMATE.start_aws_byte_cursor_advance_~cursor#1.base_BEFORE_CALL_2|) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_182153bc_9a47e154_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (<= 8678 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base| 4))) (exists ((|v_ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base_BEFORE_CALL_44| Int)) (<= 8678 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base_BEFORE_CALL_44| 4)))))";
		final String expectedResultAsString = "(<= 8678 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base| 4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_187b0e77_fb1d372b_Treesizes_24_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_next_~node#1.base", "ULTIMATE.start_aws_linked_list_next_harness_~#after~0#1.base", "ULTIMATE.start_aws_linked_list_next_~rval~4#1.base"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_aws_linked_list_next_harness_~#after~0#1.base| (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_next_~node#1.base|)) (<= (+ |ULTIMATE.start_aws_linked_list_next_~node#1.base| 8) |ULTIMATE.start_aws_linked_list_next_harness_~#after~0#1.base|) (exists ((|v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_56| Int)) (<= (+ |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_56| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_56|))) (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_next_~node#1.base|) |ULTIMATE.start_aws_linked_list_next_~rval~4#1.base|))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_next_~node#1.base|))) (and (= |ULTIMATE.start_aws_linked_list_next_harness_~#after~0#1.base| .cse0) (<= (+ |ULTIMATE.start_aws_linked_list_next_~node#1.base| 8) |ULTIMATE.start_aws_linked_list_next_harness_~#after~0#1.base|) (= .cse0 |ULTIMATE.start_aws_linked_list_next_~rval~4#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_192d16b8_18e18773_Treesizes_12_3() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_3~0"),
		};
		final String formulaAsString = "(forall ((~var_1_4~0 Int)) (or (< ~var_1_4~0 0) (< 0 (+ 129 (* ~var_1_4~0 ~var_1_3~0)))))";
		final String expectedResultAsString = "(<= 0 ~var_1_3~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1991ca20_1f1489d1_Treesizes_14_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#signed_char_Array_0~0.base", "~#signed_long_int_Array_0~0.base"),
		};
		final String formulaAsString = "(and (<= 0 (select |#memory_int| (+ |~#signed_long_int_Array_0~0.base| 12))) (not (= |~#signed_char_Array_0~0.base| (+ |~#signed_long_int_Array_0~0.base| 11))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_233 Int)) (<= 0 (select (store |#memory_int| (+ |~#signed_char_Array_0~0.base| 1) v_ArrVal_233) (+ |~#signed_long_int_Array_0~0.base| 12))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1aa7aa84_ec8ebf4d_Treesizes_134_129() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_11~0", "~var_1_10~0", "~var_1_16~0", "~var_1_4~0", "~var_1_15~0", "~var_1_14~0", "~var_1_3~0", "~var_1_8~0", "~var_1_9~0", "~var_1_18~0", "~var_1_17~0", "~var_1_1~0", "~last_1_var_1_20~0", "~last_1_var_1_41~0"),
		};
		final String formulaAsString = "(and (or (and (= ~var_1_1~0 (mod ~var_1_3~0 65536)) (<= (+ (mod ~var_1_4~0 65536) 1) (mod ~var_1_3~0 65536))) (and (<= (mod ~var_1_3~0 65536) (mod ~var_1_4~0 65536)) (= (mod ~var_1_4~0 65536) ~var_1_1~0))) (not (= ~var_1_10~0 (+ ~var_1_11~0 (mod ~var_1_8~0 65536)))) (= (div ~var_1_9~0 4294967296) 0) (not (= (mod ~last_1_var_1_20~0 256) 0)) (= ~var_1_9~0 (mod ~last_1_var_1_41~0 65536)) (or (and (or (= (mod (+ (* 255 ~var_1_17~0) (* 255 ~var_1_16~0) ~var_1_18~0 ~var_1_15~0) 256) (mod ~var_1_14~0 256)) (< (+ (mod ~var_1_18~0 256) (mod ~var_1_15~0 256)) (+ (mod ~var_1_17~0 256) (mod ~var_1_16~0 256))) (< ~var_1_9~0 6)) (or (= (mod ~var_1_14~0 256) (mod (+ (* 255 ~var_1_15~0) (* 255 ~var_1_18~0) ~var_1_17~0 ~var_1_16~0) 256)) (< ~var_1_9~0 6) (< (+ (mod ~var_1_17~0 256) (mod ~var_1_16~0 256)) (+ (mod ~var_1_18~0 256) (mod ~var_1_15~0 256) 1)))) (< (mod ~var_1_8~0 65536) (+ (mod ~var_1_4~0 65536) 1))))";
		final String expectedResultAsString = "(let ((.cse2 (mod ~var_1_4~0 65536))) (let ((.cse3 (mod ~var_1_8~0 65536)) (.cse1 (+ .cse2 1))) (and (let ((.cse0 (mod ~var_1_3~0 65536))) (or (and (= ~var_1_1~0 .cse0) (<= .cse1 .cse0)) (and (<= .cse0 .cse2) (= .cse2 ~var_1_1~0)))) (not (= ~var_1_10~0 (+ ~var_1_11~0 .cse3))) (not (= (mod ~last_1_var_1_20~0 256) 0)) (= ~var_1_9~0 (mod ~last_1_var_1_41~0 65536)) (or (let ((.cse4 (mod ~var_1_14~0 256)) (.cse8 (< ~var_1_9~0 6)) (.cse7 (+ (mod ~var_1_17~0 256) (mod ~var_1_16~0 256))) (.cse5 (mod ~var_1_18~0 256)) (.cse6 (mod ~var_1_15~0 256))) (and (or (= (mod (+ (* 255 ~var_1_17~0) (* 255 ~var_1_16~0) ~var_1_18~0 ~var_1_15~0) 256) .cse4) (< (+ .cse5 .cse6) .cse7) .cse8) (or (= .cse4 (mod (+ (* 255 ~var_1_15~0) (* 255 ~var_1_18~0) ~var_1_17~0 ~var_1_16~0) 256)) .cse8 (< .cse7 (+ .cse5 .cse6 1))))) (< .cse3 .cse1)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1b18f878_479da563_Treesizes_18_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#src~0#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#src~0#1.base_BEFORE_CALL_17| Int)) (not (= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#src~0#1.base_BEFORE_CALL_17|) 4294967296) 0))) (not (= (mod (select |#memory_int| |ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#src~0#1.base|) 4294967296) 0)))";
		final String expectedResultAsString = "(not (= (mod (select |#memory_int| |ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#src~0#1.base|) 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1b9ec687_4178587e_Treesizes_22_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#BOOL_unsigned_char_Array_0~0.base", "~#signed_short_int_Array_0~0.base", "~#double_Array_0~0.base"),
		};
		final String formulaAsString = "(and (not (= (+ |~#double_Array_0~0.base| 14) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= |~#signed_short_int_Array_0~0.base| |~#BOOL_unsigned_char_Array_0~0.base|)) (<= (mod (+ (select |#memory_int| (+ |~#BOOL_unsigned_char_Array_0~0.base| 3)) 255) 256) 254))";
		final String expectedResultAsString = "(and (not (= (+ |~#double_Array_0~0.base| 14) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (mod (select |#memory_int| (+ |~#BOOL_unsigned_char_Array_0~0.base| 3)) 256) 0)) (not (= |~#signed_short_int_Array_0~0.base| |~#BOOL_unsigned_char_Array_0~0.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1c3285f5_2eeccfea_Treesizes_32_28() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(<= (div (+ (* (- 1) (mod (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 1)) 254) 256)) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) 509) 256) (* (div (+ (- 1) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2))) 4294967296) 16777216))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)))) (<= (+ 255 (mod (+ .cse0 4294967295) 4294967296)) (mod (+ .cse0 (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 1)) 255) 255) 256)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1ca1975d_6262d7fc_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_9| Int)) (<= 76 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_9| 12)))) (<= 76 (select |#memory_$Pointer$.base| (+ 12 |ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base|))))";
		final String expectedResultAsString = "(<= 76 (select |#memory_$Pointer$.base| (+ 12 |ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1ce4de41_83507a90_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_priority_queue_capacity_harness_~#queue~0#1.base_BEFORE_CALL_43| Int)) (and (<= (+ |v_ULTIMATE.start_aws_priority_queue_capacity_harness_~#queue~0#1.base_BEFORE_CALL_43| 44) |#StackAllocations|) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_priority_queue_capacity_harness_~#queue~0#1.base_BEFORE_CALL_43| 20)) 0)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_priority_queue_capacity_harness_~#queue~0#1.base_BEFORE_CALL_40| Int)) (and (<= (+ |v_ULTIMATE.start_aws_priority_queue_capacity_harness_~#queue~0#1.base_BEFORE_CALL_40| 44) |#StackAllocations|) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_priority_queue_capacity_harness_~#queue~0#1.base_BEFORE_CALL_40| 20)) 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1d17a36d_2f6bd3d_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_end_~list#1.base_BEFORE_CALL_3| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_end_~list#1.base_BEFORE_CALL_3| 8)) 0))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_3| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_3| 8)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1d93bcf_ab169b5_Treesizes_72_38() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "func_to_recursive_line_31_to_42_0_~y3.base", "func_to_recursive_line_31_to_42_0_~y1.base", "func_to_recursive_line_31_to_42_0_~x1.base", "func_to_recursive_line_31_to_42_0_~x2.base", "func_to_recursive_line_31_to_42_0_~y2.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| func_to_recursive_line_31_to_42_0_~y1.base) 0) (<= (+ func_to_recursive_line_31_to_42_0_~x1.base 8) func_to_recursive_line_31_to_42_0_~y1.base) (= (select |#memory_int| func_to_recursive_line_31_to_42_0_~x1.base) (select |#memory_int| func_to_recursive_line_31_to_42_0_~y3.base)) (= (select |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base) 0) (<= (+ 4 func_to_recursive_line_31_to_42_0_~y2.base) func_to_recursive_line_31_to_42_0_~y3.base) (<= (+ func_to_recursive_line_31_to_42_0_~x2.base 4) func_to_recursive_line_31_to_42_0_~y1.base) (exists ((v_func_to_recursive_line_31_to_42_0_~y1.base_BEFORE_CALL_1 Int) (v_func_to_recursive_line_31_to_42_0_~x1.base_BEFORE_CALL_1 Int) (v_func_to_recursive_line_31_to_42_0_~y2.base_BEFORE_CALL_1 Int) (v_func_to_recursive_line_31_to_42_0_~y3.base_BEFORE_CALL_3 Int)) (and (= (select |#memory_int| v_func_to_recursive_line_31_to_42_0_~y3.base_BEFORE_CALL_3) (select |#memory_int| v_func_to_recursive_line_31_to_42_0_~x1.base_BEFORE_CALL_1)) (<= (+ v_func_to_recursive_line_31_to_42_0_~x1.base_BEFORE_CALL_1 8) v_func_to_recursive_line_31_to_42_0_~y1.base_BEFORE_CALL_1) (= (select |#memory_int| v_func_to_recursive_line_31_to_42_0_~y2.base_BEFORE_CALL_1) 0) (= (select |#memory_int| v_func_to_recursive_line_31_to_42_0_~y1.base_BEFORE_CALL_1) 0) (<= (+ v_func_to_recursive_line_31_to_42_0_~y1.base_BEFORE_CALL_1 4) v_func_to_recursive_line_31_to_42_0_~y2.base_BEFORE_CALL_1) (<= (+ v_func_to_recursive_line_31_to_42_0_~y2.base_BEFORE_CALL_1 4) v_func_to_recursive_line_31_to_42_0_~y3.base_BEFORE_CALL_3))) (<= (+ 4 func_to_recursive_line_31_to_42_0_~y1.base) func_to_recursive_line_31_to_42_0_~y2.base))";
		final String expectedResultAsString = "(and (= (select |#memory_int| func_to_recursive_line_31_to_42_0_~y1.base) 0) (<= (+ func_to_recursive_line_31_to_42_0_~x1.base 8) func_to_recursive_line_31_to_42_0_~y1.base) (= (select |#memory_int| func_to_recursive_line_31_to_42_0_~x1.base) (select |#memory_int| func_to_recursive_line_31_to_42_0_~y3.base)) (= (select |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base) 0) (<= (+ 4 func_to_recursive_line_31_to_42_0_~y2.base) func_to_recursive_line_31_to_42_0_~y3.base) (<= (+ func_to_recursive_line_31_to_42_0_~x2.base 4) func_to_recursive_line_31_to_42_0_~y1.base) (<= (+ 4 func_to_recursive_line_31_to_42_0_~y1.base) func_to_recursive_line_31_to_42_0_~y2.base))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1de46b5f_72af5f02_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_15| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_15| 4)) 0))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_14| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_14| 4)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1e89fc63_7455a4c3_Treesizes_24_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base", "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~bcki~0#1.base"),
		};
		final String formulaAsString = "(and (not (= (select |#memory_$Pointer$.base| (+ 4 |ULTIMATE.start_main_~bcki~0#1.base|)) |ULTIMATE.start_main_~bcki~0#1.base|)) (= (select |#memory_int| (+ 8 |ULTIMATE.start_main_~bcki~0#1.base|)) (select |#memory_int| (+ (select |#memory_$Pointer$.base| (+ 4 |ULTIMATE.start_main_~bcki~0#1.base|)) 4))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_472 Int)) (= (let ((.cse0 (+ 4 |ULTIMATE.start_main_~bcki~0#1.base|))) (select (store |#memory_int| .cse0 v_ArrVal_472) (+ (select |#memory_$Pointer$.base| .cse0) 4))) (select |#memory_int| (+ 8 |ULTIMATE.start_main_~bcki~0#1.base|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1f319220_9be5d960_Treesizes_69_20() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~var_8~0#1", "ULTIMATE.start_main_~var_5~0#1", "ULTIMATE.start_main_~mask_SORT_1~0#1", "ULTIMATE.start_main_#t~bitwise6#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~mask_SORT_1~0#1| 15) (<= 1 |ULTIMATE.start_main_~var_5~0#1|) (<= 0 |ULTIMATE.start_main_#t~bitwise6#1|) (= |ULTIMATE.start_main_~var_8~0#1| 15) (exists ((v_y_56 Int) (v_z_58 Int) (v_y_58 Int)) (and (<= |ULTIMATE.start_main_~var_5~0#1| (+ (* v_y_58 256) (* v_y_56 256) (* v_z_58 255))) (<= |ULTIMATE.start_main_#t~bitwise6#1| (+ (* v_y_58 256) (* v_z_58 255))) (<= (+ (* v_y_58 256) (* v_y_56 256) (* v_z_58 255)) (+ |ULTIMATE.start_main_~var_5~0#1| 255)) (<= (+ (* |ULTIMATE.start_main_~var_5~0#1| 6) 248) v_z_58) (<= v_z_58 255) (<= (+ (* v_y_58 256) (* v_z_58 255)) 255))))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_main_~mask_SORT_1~0#1| 15) (<= 1 |ULTIMATE.start_main_~var_5~0#1|) (<= 0 |ULTIMATE.start_main_#t~bitwise6#1|) (= |ULTIMATE.start_main_~var_8~0#1| 15) (<= (+ (* |ULTIMATE.start_main_~var_5~0#1| 6) |ULTIMATE.start_main_#t~bitwise6#1|) 8))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1f98b234_e6b76381_Treesizes_15_15() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~f1_6~0", "~l_4~0"),
		};
		final String formulaAsString = "(or (and (<= 1 ~f1_6~0) (= ~l_4~0 1)) (and (<= ~f1_6~0 0) (= ~l_4~0 0)))";
		final String expectedResultAsString = "(and (or (< ~f1_6~0 1) (= ~l_4~0 1)) (or (< 0 ~f1_6~0) (= ~l_4~0 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_201c5ba5_1feea665_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0", "~var_1_2~0", "~var_1_3~0", "~var_1_7~0"),
		};
		final String formulaAsString = "(and (<= (div ~var_1_7~0 4294967296) (div ~var_1_1~0 4294967296)) (<= ~var_1_3~0 ~var_1_2~0) (= (mod ~var_1_1~0 4294967296) (mod ~var_1_7~0 4294967296)))";
		final String expectedResultAsString = "(let ((.cse0 (mod ~var_1_7~0 4294967296))) (and (<= ~var_1_3~0 ~var_1_2~0) (= (mod ~var_1_1~0 4294967296) .cse0) (<= ~var_1_7~0 (+ ~var_1_1~0 .cse0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}



	@Test
	public void SimplificationOpportunity_213b41a3_62187eca_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_39~0"),
		};
		final String formulaAsString = "(= (mod ~var_1_39~0 256) 0)";
		final String expectedResultAsString = "(<= (mod ~var_1_39~0 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_21d3174f_698dadea_Treesizes_36_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~N~0"),
		};
		final String formulaAsString = "(and (or (exists ((|v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1| Int)) (= (mod (+ (select |#memory_int| (+ |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1| 4)) (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 1) 2) 0)) (exists ((|v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1| Int)) (not (= (mod (+ (select |#memory_int| (+ |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1| 4)) (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 1) 2) 0)))) (= 2 ~N~0))";
		final String expectedResultAsString = "(= 2 ~N~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_222acf5c_e7088d9a_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_back_~list.base_BEFORE_CALL_10 Int)) (= 0 (select |#memory_$Pointer$.base| (+ v_aws_linked_list_back_~list.base_BEFORE_CALL_10 8))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_28| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_28| 8)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_22e7e469_ede3c741_Treesizes_30_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~res2~0", "thread3Thread1of1ForFork0_~i~2#1", "~a3~0.base", "~a2~0.base"),
		};
		final String formulaAsString = "(and (= |thread3Thread1of1ForFork0_~i~2#1| 0) (exists ((~a1~0.base Int)) (and (= (select |#memory_int| ~a1~0.base) (+ ~res2~0 (select |#memory_int| ~a3~0.base))) (= (select |#memory_int| ~a1~0.base) (select |#memory_int| ~a2~0.base)) (not (= (select |#memory_int| ~a1~0.base) (select |#memory_int| ~a3~0.base))))))";
		final String expectedResultAsString = "(and (= |thread3Thread1of1ForFork0_~i~2#1| 0) (= (+ ~res2~0 (select |#memory_int| ~a3~0.base)) (select |#memory_int| ~a2~0.base)) (not (= ~res2~0 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_23bb0198_c1980cc6_Treesizes_38_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "func_to_recursive_line_27_to_35_0_~c.base", "func_to_recursive_line_27_to_35_0_~y.base", "func_to_recursive_line_27_to_35_0_~x.base"),
		};
		final String formulaAsString = "(and (exists ((v_func_to_recursive_line_27_to_35_0_~y.base_BEFORE_CALL_5 Int) (v_func_to_recursive_line_27_to_35_0_~x.base_BEFORE_CALL_5 Int)) (and (= (select |#memory_int| v_func_to_recursive_line_27_to_35_0_~x.base_BEFORE_CALL_5) 1) (<= (+ v_func_to_recursive_line_27_to_35_0_~y.base_BEFORE_CALL_5 8) v_func_to_recursive_line_27_to_35_0_~x.base_BEFORE_CALL_5) (= (select |#memory_int| v_func_to_recursive_line_27_to_35_0_~y.base_BEFORE_CALL_5) 1))) (= (select |#memory_int| func_to_recursive_line_27_to_35_0_~y.base) 1) (= (select |#memory_int| func_to_recursive_line_27_to_35_0_~x.base) 1) (<= (+ 8 func_to_recursive_line_27_to_35_0_~y.base) func_to_recursive_line_27_to_35_0_~x.base) (<= (+ 8 func_to_recursive_line_27_to_35_0_~x.base) func_to_recursive_line_27_to_35_0_~c.base))";
		final String expectedResultAsString = "(and (= (select |#memory_int| func_to_recursive_line_27_to_35_0_~y.base) 1) (= (select |#memory_int| func_to_recursive_line_27_to_35_0_~x.base) 1) (<= (+ 8 func_to_recursive_line_27_to_35_0_~y.base) func_to_recursive_line_27_to_35_0_~x.base) (<= (+ 8 func_to_recursive_line_27_to_35_0_~x.base) func_to_recursive_line_27_to_35_0_~c.base))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_241d8376_f184caa0_Treesizes_35_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_next_~node#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_31| Int)) (and (<= (+ |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_31| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_31|)) (= (select |#memory_$Pointer$.base| (+ (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_31|) 4)) |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_31|))) (= (select |#memory_$Pointer$.base| (+ (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_next_~node#1.base|) 4)) |ULTIMATE.start_aws_linked_list_next_~node#1.base|) (<= (+ |ULTIMATE.start_aws_linked_list_next_~node#1.base| 8) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_next_~node#1.base|)))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_next_~node#1.base|))) (and (= (select |#memory_$Pointer$.base| (+ .cse0 4)) |ULTIMATE.start_aws_linked_list_next_~node#1.base|) (<= (+ |ULTIMATE.start_aws_linked_list_next_~node#1.base| 8) .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2497ca19_32a64dd6_Treesizes_178_173() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~last_1_var_1_17~0", "~var_1_11~0", "~var_1_10~0", "~var_1_4~0", "~last_1_var_1_11~0", "~var_1_16~0", "~var_1_5~0", "~last_1_var_1_13~0", "~var_1_14~0", "~last_1_var_1_12~0", "~var_1_13~0", "~var_1_8~0", "~var_1_19~0", "~var_1_9~0", "~var_1_18~0", "~var_1_6~0", "~last_1_var_1_18~0", "~last_1_var_1_1~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (= 0 (mod ~var_1_10~0 256)) (= (div ~var_1_18~0 256) (div ~var_1_19~0 256)) (or (not (= (mod ~last_1_var_1_11~0 256) 0)) (not (= (mod ~last_1_var_1_12~0 256) 0)) (= (mod ~var_1_18~0 256) (mod ~var_1_16~0 256)) (and (<= (mod ~last_1_var_1_17~0 65536) (* ~var_1_4~0 ~last_1_var_1_1~0)) (not (= (* ~var_1_4~0 ~last_1_var_1_1~0) (mod ~last_1_var_1_17~0 65536))))) (or (and (or (not (= (mod ~last_1_var_1_12~0 256) 0)) (< ~var_1_5~0 (+ 5 ~last_1_var_1_13~0)) (< ~var_1_4~0 (+ 5 ~last_1_var_1_13~0))) (= ~var_1_1~0 ~last_1_var_1_13~0)) (and (or (and (= (mod ~last_1_var_1_12~0 256) 0) (<= (+ 5 ~last_1_var_1_13~0) ~var_1_4~0) (<= (+ ~var_1_4~0 1) ~var_1_5~0)) (and (= (mod ~last_1_var_1_12~0 256) 0) (<= ~var_1_5~0 ~var_1_4~0) (<= (+ 5 ~last_1_var_1_13~0) ~var_1_5~0))) (= (+ ~var_1_1~0 128) 0))) (= ~var_1_11~0 0) (= (div ~last_1_var_1_13~0 65536) 0) (= (mod ~var_1_6~0 256) 0) (= (mod ~var_1_19~0 256) (mod ~var_1_18~0 256)) (= (mod (+ (* (mod ~last_1_var_1_18~0 256) 65535) ~var_1_14~0) 65536) (mod ~var_1_13~0 65536)) (<= (+ (mod ~var_1_14~0 65536) (mod ~var_1_13~0 65536)) (+ (mod ~last_1_var_1_18~0 256) ~var_1_13~0 65535)) (or (< 0 (+ ~last_1_var_1_1~0 1)) (and (or (= (mod ~last_1_var_1_12~0 256) 0) (= (mod ~var_1_9~0 256) 0)) (= (mod ~var_1_8~0 256) 0))))";
		final String expectedResultAsString = "(let ((.cse5 (= (mod ~last_1_var_1_12~0 256) 0))) (let ((.cse0 (not .cse5)) (.cse1 (mod ~var_1_18~0 256)) (.cse6 (mod ~last_1_var_1_18~0 256))) (and (= 0 (mod ~var_1_10~0 256)) (= (div ~var_1_18~0 256) (div ~var_1_19~0 256)) (or (not (= (mod ~last_1_var_1_11~0 256) 0)) .cse0 (= .cse1 (mod ~var_1_16~0 256)) (let ((.cse3 (* ~var_1_4~0 ~last_1_var_1_1~0)) (.cse2 (mod ~last_1_var_1_17~0 65536))) (and (<= .cse2 .cse3) (not (= .cse3 .cse2))))) (let ((.cse4 (+ 5 ~last_1_var_1_13~0))) (or (and (or .cse0 (< ~var_1_5~0 .cse4) (< ~var_1_4~0 .cse4)) (= ~var_1_1~0 ~last_1_var_1_13~0)) (and (or (and .cse5 (<= .cse4 ~var_1_4~0) (<= (+ ~var_1_4~0 1) ~var_1_5~0)) (and .cse5 (<= ~var_1_5~0 ~var_1_4~0) (<= .cse4 ~var_1_5~0))) (= (+ ~var_1_1~0 128) 0)))) (<= (mod ~var_1_14~0 65536) (+ .cse6 ~var_1_13~0)) (= ~var_1_11~0 0) (= (div ~last_1_var_1_13~0 65536) 0) (= (mod ~var_1_6~0 256) 0) (= (mod ~var_1_19~0 256) .cse1) (= (mod (+ (* .cse6 65535) ~var_1_14~0) 65536) (mod ~var_1_13~0 65536)) (or (< 0 (+ ~last_1_var_1_1~0 1)) (and (or .cse5 (= (mod ~var_1_9~0 256) 0)) (= (mod ~var_1_8~0 256) 0))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2507b8e0_5e0cfffd_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~0#1.base_BEFORE_CALL_46| Int)) (and (<= 52 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~0#1.base_BEFORE_CALL_46| 4))) (<= (+ 8 |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~0#1.base_BEFORE_CALL_46|) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~0#1.base_BEFORE_CALL_43| Int)) (and (<= 52 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~0#1.base_BEFORE_CALL_43| 4))) (<= (+ 8 |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~0#1.base_BEFORE_CALL_43|) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_259339fa_a77d84d2_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_20| Int)) (= (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_20|)) 0))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_18| Int)) (= (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_18|)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2625a53a_90537ff4_Treesizes_11_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(<= (mod (+ 255 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 21))) 256) 254)";
		final String expectedResultAsString = "(not (= (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 21)) 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_26681d89_eb19089d_Treesizes_14_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#sum~0#1.base", "ULTIMATE.start_main_~a~0#1.base", "ULTIMATE.start_main_#t~mem10#1"),
		};
		final String formulaAsString = "(and (not (= |ULTIMATE.start_main_~#sum~0#1.base| (+ |ULTIMATE.start_main_~a~0#1.base| (* |ULTIMATE.start_main_~i~0#1| 4)))) (= (select |#memory_int| |ULTIMATE.start_main_~#sum~0#1.base|) |ULTIMATE.start_main_#t~mem10#1|))";
		final String expectedResultAsString = "(forall ((v_ArrVal_147 Int)) (= (select (store |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| (* |ULTIMATE.start_main_~i~0#1| 4)) v_ArrVal_147) |ULTIMATE.start_main_~#sum~0#1.base|) |ULTIMATE.start_main_#t~mem10#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_26bd8cca_3ceaf7dd_Treesizes_404_399() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "old(#memory_int)", "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "func_to_recursive_line_38_to_41_0_#in~index#1.base", "func_to_recursive_line_38_to_41_0_#in~array#1.base"),
		};
		final String formulaAsString = "(and (or (and (exists ((v_y_26 Int) (|v_func_to_recursive_line_38_to_41_0_~array#1.base_27| Int)) (and (<= (select |#memory_int| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) (+ 10000 (* v_y_26 4294967296))) (= |#memory_int| (store (store |old(#memory_int)| (+ (* (- 17179869184) v_y_26) (* (select |#memory_int| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4) (- 4) |v_func_to_recursive_line_38_to_41_0_~array#1.base_27|) (select |#memory_int| (+ (* (- 17179869184) v_y_26) (* (select |#memory_int| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4) (- 4) |v_func_to_recursive_line_38_to_41_0_~array#1.base_27|))) |func_to_recursive_line_38_to_41_0_#in~index#1.base| (select |#memory_int| |func_to_recursive_line_38_to_41_0_#in~index#1.base|))) (<= (+ |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4)) |func_to_recursive_line_38_to_41_0_#in~index#1.base|) (<= (+ (* v_y_26 4294967296) 1) (select |#memory_int| |func_to_recursive_line_38_to_41_0_#in~index#1.base|)))) (<= |func_to_recursive_line_38_to_41_0_#in~index#1.base| (+ (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4) |func_to_recursive_line_38_to_41_0_#in~array#1.base|))) (and (= |#memory_int| (store |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base| (select |#memory_int| |func_to_recursive_line_38_to_41_0_#in~index#1.base|))) (<= |func_to_recursive_line_38_to_41_0_#in~index#1.base| (+ (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4) |func_to_recursive_line_38_to_41_0_#in~array#1.base|))) (and (<= (mod (+ (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 1) 4294967296) 9999) (or (exists ((|func_to_recursive_line_38_to_41_0_~array#1.base| Int)) (and (= |#memory_int| (store (store |old(#memory_int)| (+ (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4) |func_to_recursive_line_38_to_41_0_~array#1.base|) (select |#memory_int| (+ (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4) |func_to_recursive_line_38_to_41_0_~array#1.base|))) |func_to_recursive_line_38_to_41_0_#in~index#1.base| (+ (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 2))) (<= |func_to_recursive_line_38_to_41_0_~array#1.base| |func_to_recursive_line_38_to_41_0_#in~array#1.base|))) (and (exists ((|v_func_to_recursive_line_38_to_41_0_~array#1.base_27| Int)) (and (<= (+ |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4)) |func_to_recursive_line_38_to_41_0_#in~index#1.base|) (= |#memory_int| (store (store |old(#memory_int)| (+ |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| (* (mod (+ (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 1) 4294967296) 4)) (select |#memory_int| (+ |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| (* (mod (+ (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 1) 4294967296) 4)))) |func_to_recursive_line_38_to_41_0_#in~index#1.base| (+ (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 2))))) (<= |func_to_recursive_line_38_to_41_0_#in~index#1.base| (+ (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4) |func_to_recursive_line_38_to_41_0_#in~array#1.base|))) (exists ((|func_to_recursive_line_38_to_41_0_~array#1.base| Int)) (and (exists ((|v_func_to_recursive_line_38_to_41_0_~array#1.base_27| Int)) (and (<= |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| |func_to_recursive_line_38_to_41_0_~array#1.base|) (not (= (+ (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4) |func_to_recursive_line_38_to_41_0_~array#1.base|) (+ |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| (* (mod (+ (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 1) 4294967296) 4)))) (= (store (store (store |old(#memory_int)| (+ (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4) |func_to_recursive_line_38_to_41_0_~array#1.base|) (select |#memory_int| (+ (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4) |func_to_recursive_line_38_to_41_0_~array#1.base|))) (+ |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| (* (mod (+ (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 1) 4294967296) 4)) (select |#memory_int| (+ |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| (* (mod (+ (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 1) 4294967296) 4)))) |func_to_recursive_line_38_to_41_0_#in~index#1.base| (+ (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 2)) |#memory_int|))) (not (= |func_to_recursive_line_38_to_41_0_#in~index#1.base| (+ (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4) |func_to_recursive_line_38_to_41_0_~array#1.base|))) (<= |func_to_recursive_line_38_to_41_0_~array#1.base| |func_to_recursive_line_38_to_41_0_#in~array#1.base|))))) (and (or (exists ((|func_to_recursive_line_38_to_41_0_~array#1.base| Int)) (and (<= |func_to_recursive_line_38_to_41_0_#in~index#1.base| (+ (* (mod (+ (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 1) 4294967296) 4) |func_to_recursive_line_38_to_41_0_~array#1.base|)) (= |#memory_int| (store (store |old(#memory_int)| (+ (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4) |func_to_recursive_line_38_to_41_0_~array#1.base|) (select |#memory_int| (+ (* (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 4) |func_to_recursive_line_38_to_41_0_~array#1.base|))) |func_to_recursive_line_38_to_41_0_#in~index#1.base| (select |#memory_int| |func_to_recursive_line_38_to_41_0_#in~index#1.base|))) (<= |func_to_recursive_line_38_to_41_0_~array#1.base| |func_to_recursive_line_38_to_41_0_#in~array#1.base|))) (and (exists ((|func_to_recursive_line_38_to_41_0_~array#1.base| Int)) (and (<= |func_to_recursive_line_38_to_41_0_#in~index#1.base| (+ (* (mod (+ (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 1) 4294967296) 4) |func_to_recursive_line_38_to_41_0_~array#1.base|)) (<= |func_to_recursive_line_38_to_41_0_~array#1.base| |func_to_recursive_line_38_to_41_0_#in~array#1.base|))) (= |#memory_int| (store |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base| (select |#memory_int| |func_to_recursive_line_38_to_41_0_#in~index#1.base|))))) (<= (mod (+ (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 1) 4294967296) 9999))) (<= (mod (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296) 9999) (<= 10000 (mod (select |#memory_int| |func_to_recursive_line_38_to_41_0_#in~index#1.base|) 4294967296)))";
		final String expectedResultAsString = "(let ((.cse15 (select |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base|))) (let ((.cse1 (select |#memory_int| |func_to_recursive_line_38_to_41_0_#in~index#1.base|)) (.cse0 (mod .cse15 4294967296))) (and (<= .cse0 9999) (<= 10000 (mod .cse1 4294967296)) (let ((.cse4 (* .cse0 4)) (.cse16 (mod (+ .cse15 1) 4294967296))) (let ((.cse9 (= |#memory_int| (store |old(#memory_int)| |func_to_recursive_line_38_to_41_0_#in~index#1.base| .cse1))) (.cse6 (<= .cse16 9999)) (.cse5 (<= |func_to_recursive_line_38_to_41_0_#in~index#1.base| (+ .cse4 |func_to_recursive_line_38_to_41_0_#in~array#1.base|))) (.cse7 (* .cse16 4))) (or (and (exists ((v_y_26 Int) (|v_func_to_recursive_line_38_to_41_0_~array#1.base_27| Int)) (let ((.cse2 (* v_y_26 4294967296))) (and (<= .cse1 (+ 10000 .cse2)) (= |#memory_int| (store (let ((.cse3 (+ (* (- 17179869184) v_y_26) (* .cse1 4) (- 4) |v_func_to_recursive_line_38_to_41_0_~array#1.base_27|))) (store |old(#memory_int)| .cse3 (select |#memory_int| .cse3))) |func_to_recursive_line_38_to_41_0_#in~index#1.base| .cse1)) (<= (+ |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| .cse4) |func_to_recursive_line_38_to_41_0_#in~index#1.base|) (<= (+ .cse2 1) .cse1)))) .cse5) (and .cse6 (or (exists ((|func_to_recursive_line_38_to_41_0_~array#1.base| Int)) (and (<= |func_to_recursive_line_38_to_41_0_#in~index#1.base| (+ .cse7 |func_to_recursive_line_38_to_41_0_~array#1.base|)) (= |#memory_int| (store (let ((.cse8 (+ .cse4 |func_to_recursive_line_38_to_41_0_~array#1.base|))) (store |old(#memory_int)| .cse8 (select |#memory_int| .cse8))) |func_to_recursive_line_38_to_41_0_#in~index#1.base| .cse1)) (<= |func_to_recursive_line_38_to_41_0_~array#1.base| |func_to_recursive_line_38_to_41_0_#in~array#1.base|))) (and .cse9 (<= |func_to_recursive_line_38_to_41_0_#in~index#1.base| (+ .cse7 |func_to_recursive_line_38_to_41_0_#in~array#1.base|))))) (and .cse9 .cse5) (and .cse6 (let ((.cse11 (+ .cse15 2))) (or (exists ((|func_to_recursive_line_38_to_41_0_~array#1.base| Int)) (and (= |#memory_int| (store (let ((.cse10 (+ .cse4 |func_to_recursive_line_38_to_41_0_~array#1.base|))) (store |old(#memory_int)| .cse10 (select |#memory_int| .cse10))) |func_to_recursive_line_38_to_41_0_#in~index#1.base| .cse11)) (<= |func_to_recursive_line_38_to_41_0_~array#1.base| |func_to_recursive_line_38_to_41_0_#in~array#1.base|))) (and (exists ((|v_func_to_recursive_line_38_to_41_0_~array#1.base_27| Int)) (and (<= (+ |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| .cse4) |func_to_recursive_line_38_to_41_0_#in~index#1.base|) (= |#memory_int| (store (let ((.cse12 (+ |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| .cse7))) (store |old(#memory_int)| .cse12 (select |#memory_int| .cse12))) |func_to_recursive_line_38_to_41_0_#in~index#1.base| .cse11)))) .cse5) (exists ((|func_to_recursive_line_38_to_41_0_~array#1.base| Int)) (let ((.cse13 (+ .cse4 |func_to_recursive_line_38_to_41_0_~array#1.base|))) (and (exists ((|v_func_to_recursive_line_38_to_41_0_~array#1.base_27| Int)) (let ((.cse14 (+ |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| .cse7))) (and (<= |v_func_to_recursive_line_38_to_41_0_~array#1.base_27| |func_to_recursive_line_38_to_41_0_~array#1.base|) (not (= .cse13 .cse14)) (= (store (store (store |old(#memory_int)| .cse13 (select |#memory_int| .cse13)) .cse14 (select |#memory_int| .cse14)) |func_to_recursive_line_38_to_41_0_#in~index#1.base| .cse11) |#memory_int|)))) (not (= |func_to_recursive_line_38_to_41_0_#in~index#1.base| .cse13)) (<= |func_to_recursive_line_38_to_41_0_~array#1.base| |func_to_recursive_line_38_to_41_0_#in~array#1.base|)))))))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_274e8a7b_34d6f26_Treesizes_79_72() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~double_Array_0_arraydouble_Array_0arrayVar0_Pointer~0.base", "~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base", "~double_Array_0_arraydouble_Array_0arrayVar1_Pointer~0.base", "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base", "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var4_Pointer~0.base", "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var7_Pointer~0.base", "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var0_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var7_Pointer~0.base ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base)) (or (< 1 (+ (select |#memory_int| ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base) (* 2 (select |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base)))) (and (<= (+ (select |#memory_int| ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base) 1) 0) (<= 1 (mod (select |#memory_int| ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base) 2)) (<= 0 (+ (select |#memory_int| ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base) (* 2 (select |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base)))))) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var0_Pointer~0.base)) (not (= ~double_Array_0_arraydouble_Array_0arrayVar1_Pointer~0.base ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base)) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base ~double_Array_0_arraydouble_Array_0arrayVar1_Pointer~0.base)) (not (= ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var4_Pointer~0.base ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base)) (not (= ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base ~double_Array_0_arraydouble_Array_0arrayVar0_Pointer~0.base)) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var4_Pointer~0.base)) (not (= ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var7_Pointer~0.base ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base)) (not (= ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var0_Pointer~0.base)) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base ~double_Array_0_arraydouble_Array_0arrayVar0_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var7_Pointer~0.base ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base)) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var0_Pointer~0.base)) (not (= ~double_Array_0_arraydouble_Array_0arrayVar1_Pointer~0.base ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base)) (let ((.cse1 (select |#memory_int| ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base))) (let ((.cse0 (+ .cse1 (* 2 (select |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base))))) (or (< 1 .cse0) (and (= .cse0 1) (<= (+ .cse1 1) 0))))) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base ~double_Array_0_arraydouble_Array_0arrayVar1_Pointer~0.base)) (not (= ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var4_Pointer~0.base ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base)) (not (= ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base ~double_Array_0_arraydouble_Array_0arrayVar0_Pointer~0.base)) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var4_Pointer~0.base)) (not (= ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var7_Pointer~0.base ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base)) (not (= ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var0_Pointer~0.base ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var0_Pointer~0.base)) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base ~double_Array_0_arraydouble_Array_0arrayVar0_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_27fb9fba_30679c6a_Treesizes_16_12() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "~SIZE~0"),
		};
		final String formulaAsString = "(and (= (mod ~SIZE~0 2) 0) (= |ULTIMATE.start_main_~i~0#1| 1) (or (= ~SIZE~0 4) (< 4 ~SIZE~0)))";
		final String expectedResultAsString = "(and (= (mod ~SIZE~0 2) 0) (= |ULTIMATE.start_main_~i~0#1| 1) (<= 4 ~SIZE~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2870a4ae_bfa2c964_Treesizes_23_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base"),
		};
		final String formulaAsString = "(and (<= (+ 8 |ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base|) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base|)) (<= 68 |ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base|) (exists ((|v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_37| Int)) (and (<= 68 |v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_37|) (<= (+ |v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_37| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_37|)))))";
		final String expectedResultAsString = "(and (<= (+ 8 |ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base|) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base|)) (<= 68 |ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_28b8fc84_402002fc_Treesizes_19_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#a~0#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~#a~0#1.base_BEFORE_CALL_13| Int)) (<= 7 (select |#memory_int| (+ |v_ULTIMATE.start_main_~#a~0#1.base_BEFORE_CALL_13| 20)))) (<= 7 (select |#memory_int| (+ 20 |ULTIMATE.start_main_~#a~0#1.base|))) (= |ULTIMATE.start_main_~i~0#1| 8))";
		final String expectedResultAsString = "(and (<= 7 (select |#memory_int| (+ 20 |ULTIMATE.start_main_~#a~0#1.base|))) (= |ULTIMATE.start_main_~i~0#1| 8))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_28e80fe6_7a1929a0_Treesizes_15_14() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_23~0", "~var_1_24~0", "~var_1_18~0"),
		};
		final String formulaAsString = "(and (= ~var_1_18~0 1) (<= 1 (mod ~var_1_24~0 256)) (not (= (mod ~var_1_23~0 256) 0)))";
		final String expectedResultAsString = "(and (<= 1 (mod ~var_1_23~0 256)) (= ~var_1_18~0 1) (<= 1 (mod ~var_1_24~0 256)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_295944d7_14dddaba_Treesizes_37_37() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_22| Int) (v_y_10 Int)) (and (<= (* v_y_10 4294967296) (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_22| 4))) (= (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_22| 8 (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_22| 4)) (* v_y_10 (- 4294967296)))) 0) (<= (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_22| 4)) (+ (* v_y_10 4294967296) 15))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_21| Int) (v_y_10 Int)) (let ((.cse1 (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_21| 4))) (.cse0 (* v_y_10 4294967296))) (and (<= .cse0 .cse1) (= (select |#memory_int| (+ .cse1 |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_21| 8 (* v_y_10 (- 4294967296)))) 0) (<= .cse1 (+ .cse0 15)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_295db0_c495247d_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_c_str_~buf#1.base_BEFORE_CALL_11| Int)) (<= 8681 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_eq_c_str_~buf#1.base_BEFORE_CALL_11| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_c_str_~buf#1.base_BEFORE_CALL_9| Int)) (<= 8681 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_eq_c_str_~buf#1.base_BEFORE_CALL_9| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_29d3fa4a_822b3993_Treesizes_76_74() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_45~0", "~var_1_20~0", "~var_1_16~0", "~var_1_27~0", "~var_1_15~0", "~var_1_14~0", "~var_1_37~0", "~var_1_39~0", "~var_1_7~0"),
		};
		final String formulaAsString = "(and (or (< 0 (+ (div ~var_1_20~0 65536) 1)) (and (<= (+ 16255 (mod ~var_1_15~0 256) ~var_1_27~0) (+ (mod ~var_1_14~0 256) ~var_1_45~0 (mod ~var_1_16~0 256))) (<= 0 (div ~var_1_27~0 4294967296)))) (<= (+ (mod ~var_1_37~0 256) 16319) (+ ~var_1_45~0 (mod ~var_1_16~0 256))) (<= (mod ~var_1_39~0 256) 63) (or (< (div ~var_1_20~0 65536) 0) (and (<= (mod ~var_1_37~0 256) (+ (mod ~var_1_7~0 65536) 63)) (<= (mod ~var_1_16~0 256) 127))) (<= (mod ~var_1_16~0 256) (+ (mod ~var_1_39~0 256) 127)))";
		final String expectedResultAsString = "(let ((.cse0 (mod ~var_1_37~0 256)) (.cse2 (mod ~var_1_39~0 256)) (.cse3 (div ~var_1_20~0 65536)) (.cse1 (mod ~var_1_16~0 256))) (and (<= (+ .cse0 16319) (+ ~var_1_45~0 .cse1)) (<= .cse2 63) (or (< .cse3 0) (and (<= .cse0 (+ (mod ~var_1_7~0 65536) 63)) (<= .cse1 127))) (<= .cse1 (+ .cse2 127)) (or (< 0 (+ .cse3 1)) (and (<= (+ 16255 (mod ~var_1_15~0 256) ~var_1_27~0) (+ (mod ~var_1_14~0 256) ~var_1_45~0 .cse1)) (<= 0 ~var_1_27~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2a65cd3a_1dcfaa3b_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_ring_buffer_clean_up_~ring_buf#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_ensure_ring_buffer_has_allocated_members_~ring_buf#1.base_BEFORE_CALL_3| Int)) (<= 8684 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_ensure_ring_buffer_has_allocated_members_~ring_buf#1.base_BEFORE_CALL_3| 4)))) (<= 8684 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_ring_buffer_clean_up_~ring_buf#1.base| 4))))";
		final String expectedResultAsString = "(<= 8684 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_ring_buffer_clean_up_~ring_buf#1.base| 4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2ae8244b_91cf389_Treesizes_14_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var1_Pointer~0.base", "~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var1_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var1_Pointer~0.base ~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var1_Pointer~0.base)) (<= (mod (+ (select |#memory_int| ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var1_Pointer~0.base) 65535) 65536) 65534))";
		final String expectedResultAsString = "(forall ((v_ArrVal_192 Int)) (<= 1 (mod (select (store |#memory_int| ~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var1_Pointer~0.base v_ArrVal_192) ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var1_Pointer~0.base) 65536)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2b28bfbe_827ba4e8_Treesizes_78_66() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~last_1_var_1_17~0", "~var_1_11~0", "~var_1_1~0", "~var_1_4~0", "~var_1_8~0", "~var_1_9~0", "~last_1_var_1_8~0", "~last_1_var_1_16~0"),
		};
		final String formulaAsString = "(and (<= (mod ~last_1_var_1_8~0 4294967296) (mod ~var_1_8~0 4294967296)) (<= (div ~var_1_1~0 4294967296) 0) (<= 0 (div ~last_1_var_1_8~0 4294967296)) (<= (div ~last_1_var_1_8~0 4294967296) (div ~last_1_var_1_16~0 4294967296)) (<= ~last_1_var_1_16~0 ~last_1_var_1_8~0) (<= (+ (mod ~var_1_4~0 256) 99999745 ~last_1_var_1_16~0) (+ ~var_1_1~0 ~last_1_var_1_8~0)) (= ~var_1_1~0 ~last_1_var_1_16~0) (not (= (mod ~var_1_9~0 256) 0)) (or (and (= (mod ~var_1_8~0 4294967296) ~last_1_var_1_8~0) (<= (+ ~last_1_var_1_17~0 1) (mod ~var_1_4~0 256))) (and (= (mod (+ (* 4294967295 ~last_1_var_1_8~0) ~var_1_11~0) 4294967296) (mod ~var_1_8~0 4294967296)) (<= (mod ~var_1_4~0 256) ~last_1_var_1_17~0))))";
		final String expectedResultAsString = "(let ((.cse0 (mod ~var_1_8~0 4294967296)) (.cse1 (mod ~var_1_4~0 256))) (and (<= (div ~last_1_var_1_8~0 4294967296) (div ~last_1_var_1_16~0 4294967296)) (<= ~last_1_var_1_8~0 .cse0) (<= ~last_1_var_1_16~0 ~last_1_var_1_8~0) (<= (+ .cse1 99999745 ~last_1_var_1_16~0) (+ ~var_1_1~0 ~last_1_var_1_8~0)) (= ~var_1_1~0 ~last_1_var_1_16~0) (not (= (mod ~var_1_9~0 256) 0)) (or (and (= .cse0 ~last_1_var_1_8~0) (<= (+ ~last_1_var_1_17~0 1) .cse1)) (and (= (mod (+ (* 4294967295 ~last_1_var_1_8~0) ~var_1_11~0) 4294967296) .cse0) (<= .cse1 ~last_1_var_1_17~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2bce0ac8_16009119_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_54| Int)) (and (<= (+ 16 |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_54|) |#StackAllocations|) (<= 8687 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_54| 4)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_53| Int)) (and (<= (+ 16 |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_53|) |#StackAllocations|) (<= 8687 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_53| 4)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2c6739f0_1d42e3a9_Treesizes_36_36() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base| Int) (v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_8 Int)) (and (= (mod (select |#memory_int| v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_8) 4294967296) 0) (= (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base|) (select |#memory_int| v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_8)) (<= (+ |ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base| 8) v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_8))) (exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base_23| Int) (v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_6 Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base_23| 8) v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_6) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base_23|) (select |#memory_int| v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_6)))))";
		final String expectedResultAsString = "(and (exists ((|ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base| Int) (v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_7 Int)) (let ((.cse0 (select |#memory_int| v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_7))) (and (= (mod .cse0 4294967296) 0) (<= (+ |ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base| 8) v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_7) (= (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base|) .cse0)))) (exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base_23| Int) (v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_6 Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base_23| 8) v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_6) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base_23|) (select |#memory_int| v_aws_byte_cursor_compare_lookup_~rhs.base_BEFORE_CALL_6)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2d3425ac_ab83c48e_Treesizes_145_143() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0", "~var_1_4~0", "~var_1_5~0", "~var_1_2~0", "~var_1_3~0", "~var_1_8~0", "~var_1_9~0", "~var_1_6~0", "~var_1_7~0"),
		};
		final String formulaAsString = "(or (and (or (< 32767 (mod (+ 65504 (* ~var_1_7~0 65535) ~var_1_9~0 ~var_1_6~0 (* ~var_1_8~0 65535)) 65536)) (and (or (= (mod (* ~var_1_4~0 ~var_1_5~0) 4294967296) (mod (+ 64 ~var_1_3~0) 4294967296)) (< (mod ~var_1_2~0 4294967296) (mod ~var_1_3~0 4294967296))) (or (= (mod (* ~var_1_4~0 ~var_1_5~0) 4294967296) (mod (+ 64 ~var_1_2~0) 4294967296)) (< (mod ~var_1_3~0 4294967296) (+ (mod ~var_1_2~0 4294967296) 1))))) (or (and (or (= (mod (* ~var_1_4~0 ~var_1_5~0) 4294967296) (mod (+ 64 ~var_1_3~0) 4294967296)) (< (mod ~var_1_2~0 4294967296) (mod ~var_1_3~0 4294967296))) (or (= (mod (* ~var_1_4~0 ~var_1_5~0) 4294967296) (mod (+ 64 ~var_1_2~0) 4294967296)) (< (mod ~var_1_3~0 4294967296) (+ (mod ~var_1_2~0 4294967296) 1)))) (= (+ 65536 ~var_1_1~0) (mod (+ 65504 (* ~var_1_7~0 65535) ~var_1_9~0 ~var_1_6~0 (* ~var_1_8~0 65535)) 65536)))) (and (= ~var_1_1~0 (mod (+ 65504 (* ~var_1_7~0 65535) ~var_1_9~0 ~var_1_6~0 (* ~var_1_8~0 65535)) 65536)) (<= (mod (+ 65504 (* ~var_1_7~0 65535) ~var_1_9~0 ~var_1_6~0 (* ~var_1_8~0 65535)) 65536) 32767)))";
		final String expectedResultAsString = "(let ((.cse1 (let ((.cse2 (mod (* ~var_1_4~0 ~var_1_5~0) 4294967296)) (.cse4 (mod ~var_1_3~0 4294967296)) (.cse3 (mod ~var_1_2~0 4294967296))) (and (or (= .cse2 (mod (+ 64 ~var_1_3~0) 4294967296)) (< .cse3 .cse4)) (or (= .cse2 (mod (+ 64 ~var_1_2~0) 4294967296)) (< .cse4 (+ .cse3 1)))))) (.cse0 (mod (+ 65504 (* ~var_1_7~0 65535) ~var_1_9~0 ~var_1_6~0 (* ~var_1_8~0 65535)) 65536))) (and (or (< 32767 .cse0) .cse1 (= ~var_1_1~0 .cse0)) (or .cse1 (= (+ 65536 ~var_1_1~0) .cse0) (< .cse0 32768))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2d9b2eb9_89a92e7a_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_28| Int)) (and (<= 2 (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_28|) 4294967296)) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_28| 8) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_27| Int)) (and (<= 2 (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_27|) 4294967296)) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_27| 8) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2e069454_5f41e6c8_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_eq_byte_buf_~b#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_~b#1.base_BEFORE_CALL_13| Int)) (<= 8687 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_~b#1.base_BEFORE_CALL_13| 4)))) (<= 8687 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_~b#1.base| 4))))";
		final String expectedResultAsString = "(<= 8687 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_~b#1.base| 4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2e46712e_eaadcaf7_Treesizes_10_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_21| Int)) (<= (mod (+ (select |#memory_int| |v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_21|) 4294967295) 4294967296) 4294967294))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_18| Int)) (<= (mod (+ (select |#memory_int| |v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_18|) 4294967295) 4294967296) 4294967294))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2eda1c6e_1756cbfe_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_9| Int)) (and (<= 72 |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_9|) (<= |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_9| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_9| 12)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_11| Int)) (and (<= |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_11| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_11| 12))) (<= 72 |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_11|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2f5ee766_6a9f8928_Treesizes_16_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "old(#memory_$Pointer$.base)", "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_41| Int)) (or (< 0 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_41| 4))) (< (select |old(#memory_$Pointer$.base)| (+ |v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_41| 4)) 1)))";
		final String expectedResultAsString = "(forall ((|v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_40| Int)) (let ((.cse0 (+ |v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_40| 4))) (or (< 0 (select |#memory_$Pointer$.base| .cse0)) (< (select |old(#memory_$Pointer$.base)| .cse0) 1))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3014241d_a7fe499d_Treesizes_15_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~a~0#1.base"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_369 Int)) (<= 9 (select (store |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| (* |ULTIMATE.start_main_~i~0#1| 4)) v_ArrVal_369) (+ |ULTIMATE.start_main_~a~0#1.base| 36))))";
		final String expectedResultAsString = "(and (<= 9 (select |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| 36))) (not (= 9 |ULTIMATE.start_main_~i~0#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_309f623d_80a17ee4_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_52| Int)) (and (<= (+ 16 |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_52|) |#StackAllocations|) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_52| 4)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_49| Int)) (and (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_49| 4))) (<= (+ 16 |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_49|) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3157afc1_193029b0_Treesizes_32_25() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_property_#t~ite104#1", "ULTIMATE.start_property_#t~mem105#1"),
		};
		final String formulaAsString = "(and (or (and (<= 128 (mod |ULTIMATE.start_property_#t~ite104#1| 256)) (= (+ |ULTIMATE.start_property_#t~mem105#1| 256) (mod |ULTIMATE.start_property_#t~ite104#1| 256))) (= (mod |ULTIMATE.start_property_#t~ite104#1| 256) |ULTIMATE.start_property_#t~mem105#1|)) (or (not (= (mod |ULTIMATE.start_property_#t~ite104#1| 256) |ULTIMATE.start_property_#t~mem105#1|)) (< (mod |ULTIMATE.start_property_#t~ite104#1| 256) 128)))";
		final String expectedResultAsString = "(let ((.cse0 (mod |ULTIMATE.start_property_#t~ite104#1| 256))) (or (and (<= 128 .cse0) (= (+ |ULTIMATE.start_property_#t~mem105#1| 256) .cse0)) (and (= .cse0 |ULTIMATE.start_property_#t~mem105#1|) (<= .cse0 127))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_31ef03fa_51041517_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_74| Int)) (and (<= 8425 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_74| 16))) (<= (+ |v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_74| 24) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_72| Int)) (and (<= 8425 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_72| 16))) (<= (+ |v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_72| 24) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3265127_95f1463f_Treesizes_35_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_string_new_from_array_~str~2.base"),
		};
		final String formulaAsString = "(and (<= (mod (+ 4294967295 (select |#memory_int| (+ aws_string_new_from_array_~str~2.base 4))) 4294967296) 0) (= (select |#memory_int| (+ aws_string_new_from_array_~str~2.base (select |#memory_int| (+ aws_string_new_from_array_~str~2.base 4)) 8 (* (div (+ (select |#memory_int| (+ aws_string_new_from_array_~str~2.base 4)) 2147483648) 4294967296) (- 4294967296)))) 0))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (+ aws_string_new_from_array_~str~2.base 4)))) (and (<= (mod (+ 4294967295 .cse0) 4294967296) 0) (= (select |#memory_int| (+ (mod .cse0 4294967296) aws_string_new_from_array_~str~2.base 8)) 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_328db6eb_4def818f_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_harness_~#lhs~0#1.base_BEFORE_CALL_23| Int)) (<= 8675 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_eq_harness_~#lhs~0#1.base_BEFORE_CALL_23| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_harness_~#lhs~0#1.base_BEFORE_CALL_22| Int)) (<= 8675 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_eq_harness_~#lhs~0#1.base_BEFORE_CALL_22| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_32f1b631_436a712b_Treesizes_9_7() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(<= (mod (+ (* 4294967295 |ULTIMATE.start_main_~x~0#1|) 500000) 4294967296) 499999)";
		final String expectedResultAsString = "(<= (mod (+ 4294967295 |ULTIMATE.start_main_~x~0#1|) 4294967296) 499999)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_33391fe0_4fcd39a3_Treesizes_7_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_ldv_usb_usb_instance_1_~data~2#1.base"),
		};
		final String formulaAsString = "(<= (mod (+ 4294967295 |ULTIMATE.start_ldv_usb_usb_instance_1_~data~2#1.base|) 4294967296) 4294967294)";
		final String expectedResultAsString = "(<= 1 (mod |ULTIMATE.start_ldv_usb_usb_instance_1_~data~2#1.base| 4294967296))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3373e32e_e77dbbb4_Treesizes_27_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base", "#StackAllocations"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_46| Int)) (and (<= (+ 16 |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_46|) |#StackAllocations|) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_46| 4))))) (<= 8682 (select |#memory_$Pointer$.base| (+ 4 |ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base|))) (<= (+ 16 |ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base|) |#StackAllocations|))";
		final String expectedResultAsString = "(and (<= 8682 (select |#memory_$Pointer$.base| (+ 4 |ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base|))) (<= (+ 16 |ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base|) |#StackAllocations|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_349cd226_31b7836b_Treesizes_13_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~z~0#1"),
		};
		final String formulaAsString = "(and (<= 0 (+ |ULTIMATE.start_main_~z~0#1| 1)) (<= (+ (div |ULTIMATE.start_main_~z~0#1| 4294967296) 1) 0))";
		final String expectedResultAsString = "(= 0 (+ |ULTIMATE.start_main_~z~0#1| 1))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3554f9d8_a40a6fd4_Treesizes_20_18() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base", "~#unsigned_short_int_Array_0~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var4_Pointer~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var5_Pointer~0.base", "~#signed_char_Array_0~0.base"),
		};
		final String formulaAsString = "(and (not (= ~signed_char_Array_0_arraysigned_char_Array_0Var5_Pointer~0.base ~signed_char_Array_0_arraysigned_char_Array_0Var4_Pointer~0.base)) (not (= ~signed_char_Array_0_arraysigned_char_Array_0Var4_Pointer~0.base ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base)) (not (= ~signed_char_Array_0_arraysigned_char_Array_0Var4_Pointer~0.base (+ 2 |~#unsigned_short_int_Array_0~0.base|))) (= ~signed_char_Array_0_arraysigned_char_Array_0Var4_Pointer~0.base (+ 2 |~#signed_char_Array_0~0.base|)))";
		final String expectedResultAsString = "(and (not (= ~signed_char_Array_0_arraysigned_char_Array_0Var5_Pointer~0.base ~signed_char_Array_0_arraysigned_char_Array_0Var4_Pointer~0.base)) (not (= ~signed_char_Array_0_arraysigned_char_Array_0Var4_Pointer~0.base ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base)) (not (= |~#signed_char_Array_0~0.base| |~#unsigned_short_int_Array_0~0.base|)) (= ~signed_char_Array_0_arraysigned_char_Array_0Var4_Pointer~0.base (+ 2 |~#signed_char_Array_0~0.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3603e64b_52f74204_Treesizes_45_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_42| Int)) (and (<= (+ (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_42|) 10) |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_42|) (= (select |#memory_$Pointer$.base| (+ (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_42|) 4)) |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_42|) (<= 68 (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_42|)))) (<= (+ 10 (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|)) |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|) (= |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base| (select |#memory_$Pointer$.base| (+ 4 (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|)))) (<= 68 (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|)))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|))) (and (<= (+ 10 .cse0) |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|) (= |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base| (select |#memory_$Pointer$.base| (+ 4 .cse0))) (<= 68 .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_367b9463_e1ad5f0d_Treesizes_23_23() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~f1_6~0", "~f2_7~0", "~l_4~0"),
		};
		final String formulaAsString = "(or (and (= ~l_4~0 1) (<= 1 (+ ~f2_7~0 (* ~f1_6~0 2)))) (and (<= (+ ~f2_7~0 (* ~f1_6~0 2)) 0) (= ~l_4~0 0)))";
		final String expectedResultAsString = "(let ((.cse0 (+ ~f2_7~0 (* ~f1_6~0 2)))) (and (or (= ~l_4~0 1) (< .cse0 1)) (or (< 0 .cse0) (= ~l_4~0 0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_37084b4b_9f2b1f03_Treesizes_54_52() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~path1_len~0", "ULTIMATE.start_init_input_paths_~i~2#1", "~path2_len~0", "~path1~0.base", "~path2~0.base"),
		};
		final String formulaAsString = "(and (<= ~path1_len~0 199) (or (= ~path1~0.base (+ ~path2~0.base ~path2_len~0)) (and (not (= (+ ~path2~0.base 1) ~path1~0.base)) (not (= ~path2~0.base ~path1~0.base)) (= 47 (select |#memory_int| ~path1~0.base)))) (<= 1 ~path1_len~0) (= 1 |ULTIMATE.start_init_input_paths_~i~2#1|) (or (not (= ~path1~0.base (+ ~path2~0.base ~path2_len~0))) (and (<= (+ 202 ~path1~0.base) (+ ~path2~0.base (mod ~path2_len~0 4294967296))) (<= ~path2~0.base (+ 200 ~path1~0.base)))))";
		final String expectedResultAsString = "(let ((.cse0 (= ~path1~0.base (+ ~path2~0.base ~path2_len~0)))) (and (or (not .cse0) (and (<= (+ (div ~path2_len~0 4294967296) 1) 0) (<= ~path2~0.base (+ 200 ~path1~0.base)))) (<= ~path1_len~0 199) (or .cse0 (and (not (= (+ ~path2~0.base 1) ~path1~0.base)) (not (= ~path2~0.base ~path1~0.base)) (= 47 (select |#memory_int| ~path1~0.base)))) (<= 1 ~path1_len~0) (= 1 |ULTIMATE.start_init_input_paths_~i~2#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_37b08e79_825b3138_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_with_lookup_harness_~#to~0#1.base_BEFORE_CALL_25| Int) (|v_ULTIMATE.start_aws_byte_buf_append_with_lookup_harness_~#to_old~0#1.base_BEFORE_CALL_2| Int)) (and (<= 8691 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_append_with_lookup_harness_~#to~0#1.base_BEFORE_CALL_25|))) (<= (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_append_with_lookup_harness_~#to~0#1.base_BEFORE_CALL_25|)) (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_append_with_lookup_harness_~#to_old~0#1.base_BEFORE_CALL_2| 4)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_with_lookup_harness_~#to_old~0#1.base_BEFORE_CALL_1| Int) (|v_ULTIMATE.start_aws_byte_buf_append_with_lookup_harness_~#to~0#1.base_BEFORE_CALL_24| Int)) (let ((.cse0 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_append_with_lookup_harness_~#to~0#1.base_BEFORE_CALL_24|)))) (and (<= 8691 .cse0) (<= .cse0 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_append_with_lookup_harness_~#to_old~0#1.base_BEFORE_CALL_1| 4))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_37ee198f_caf95bf2_Treesizes_24_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#volArray~0#1.base", "ULTIMATE.start_main_~MINVAL~0#1"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_291 Int) (v_ArrVal_290 Int)) (<= |ULTIMATE.start_main_~MINVAL~0#1| (select (store (store |#memory_int| (+ |ULTIMATE.start_main_~#volArray~0#1.base| (* |ULTIMATE.start_main_~i~0#1| 12) (- 8)) v_ArrVal_290) (+ |ULTIMATE.start_main_~#volArray~0#1.base| (- 12) (* |ULTIMATE.start_main_~i~0#1| 12)) v_ArrVal_291) (+ 16 |ULTIMATE.start_main_~#volArray~0#1.base|))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_280 Int)) (<= |ULTIMATE.start_main_~MINVAL~0#1| (select (store |#memory_int| (+ |ULTIMATE.start_main_~#volArray~0#1.base| (* |ULTIMATE.start_main_~i~0#1| 12) (- 8)) v_ArrVal_280) (+ 16 |ULTIMATE.start_main_~#volArray~0#1.base|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3877dbc7_35cb468f_Treesizes_53_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#volArray~0#1.base", "ULTIMATE.start_main_~MINVAL~0#1"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_230 Int) (v_ArrVal_229 Int) (v_ArrVal_228 Int) (v_ArrVal_227 Int)) (or (< |ULTIMATE.start_main_~MINVAL~0#1| (+ (select (store (store (store (store |#memory_int| (+ (- 20) (* |ULTIMATE.start_main_~i~0#1| 20) |ULTIMATE.start_main_~#volArray~0#1.base|) v_ArrVal_227) (+ (* |ULTIMATE.start_main_~i~0#1| 20) (- 16) |ULTIMATE.start_main_~#volArray~0#1.base|) v_ArrVal_228) (+ (* |ULTIMATE.start_main_~i~0#1| 20) |ULTIMATE.start_main_~#volArray~0#1.base| (- 12)) v_ArrVal_230) (+ (* |ULTIMATE.start_main_~i~0#1| 20) |ULTIMATE.start_main_~#volArray~0#1.base| (- 4)) v_ArrVal_229) (+ |ULTIMATE.start_main_~#volArray~0#1.base| 8)) 1)) (< v_ArrVal_230 (select |#memory_int| (+ (* |ULTIMATE.start_main_~i~0#1| 20) |ULTIMATE.start_main_~#volArray~0#1.base| (- 12))))))";
		final String expectedResultAsString = "(<= |ULTIMATE.start_main_~MINVAL~0#1| (select |#memory_int| (+ |ULTIMATE.start_main_~#volArray~0#1.base| 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_38a04785_bbe5d872_Treesizes_26_16() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1", "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~y~0#1| 1) (<= (+ |ULTIMATE.start_main_~n~0#1| (mod |ULTIMATE.start_main_~x~0#1| 4294967296) (mod (+ (* 4294967295 |ULTIMATE.start_main_~n~0#1|) |ULTIMATE.start_main_~x~0#1| 1) 4294967296)) (+ 4294967295 |ULTIMATE.start_main_~x~0#1|)) (<= (+ |ULTIMATE.start_main_~x~0#1| 1) |ULTIMATE.start_main_~n~0#1|))";
		final String expectedResultAsString = "(let ((.cse0 (+ |ULTIMATE.start_main_~x~0#1| 1))) (and (= |ULTIMATE.start_main_~n~0#1| .cse0) (= |ULTIMATE.start_main_~y~0#1| 1) (<= 1 (mod .cse0 4294967296))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_38ec7310_98bb9b98_Treesizes_25_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_next_harness_~#node~1#1.base_BEFORE_CALL_24| Int)) (and (<= 68 |v_ULTIMATE.start_aws_linked_list_next_harness_~#node~1#1.base_BEFORE_CALL_24|) (<= (+ |v_ULTIMATE.start_aws_linked_list_next_harness_~#node~1#1.base_BEFORE_CALL_24| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_harness_~#node~1#1.base_BEFORE_CALL_24|)))) (exists ((|v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_30| Int)) (and (<= 68 |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_30|) (<= (+ |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_30| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_30|)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_30| Int)) (and (<= 68 |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_30|) (<= (+ |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_30| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_30|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3999a0a5_a3e8cd88_Treesizes_28_28() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_5_Pointer~0.base", "~var_1_13_Pointer~0.base", "~var_1_1_Pointer~0.base", "~#var_1_18~0.base", "~#var_1_19~0.base", "~#var_1_17~0.base"),
		};
		final String formulaAsString = "(and (not (= ~var_1_13_Pointer~0.base ~var_1_1_Pointer~0.base)) (not (= ~var_1_13_Pointer~0.base |~#var_1_18~0.base|)) (not (= ~var_1_13_Pointer~0.base ~var_1_5_Pointer~0.base)) (not (= |~#var_1_19~0.base| ~var_1_13_Pointer~0.base)) (forall ((v_ArrVal_184 Int)) (<= (mod (select (store |#memory_int| |~#var_1_17~0.base| v_ArrVal_184) ~var_1_13_Pointer~0.base) 256) 0)))";
		final String expectedResultAsString = "(and (not (= ~var_1_13_Pointer~0.base ~var_1_1_Pointer~0.base)) (not (= ~var_1_13_Pointer~0.base |~#var_1_17~0.base|)) (not (= ~var_1_13_Pointer~0.base |~#var_1_18~0.base|)) (not (= ~var_1_13_Pointer~0.base ~var_1_5_Pointer~0.base)) (not (= |~#var_1_19~0.base| ~var_1_13_Pointer~0.base)) (<= (mod (select |#memory_int| ~var_1_13_Pointer~0.base) 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_39ce0b96_a2ed04a3_Treesizes_45_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#volArray~0#1.base", "ULTIMATE.start_main_~MINVAL~0#1"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_284 Int) (v_ArrVal_283 Int) (v_ArrVal_282 Int)) (or (< |ULTIMATE.start_main_~MINVAL~0#1| (+ 1 (select (store (store (store |#memory_int| (+ (- 16) |ULTIMATE.start_main_~#volArray~0#1.base| (* 16 |ULTIMATE.start_main_~i~0#1|)) v_ArrVal_284) (+ |ULTIMATE.start_main_~#volArray~0#1.base| (- 12) (* 16 |ULTIMATE.start_main_~i~0#1|)) v_ArrVal_283) (+ |ULTIMATE.start_main_~#volArray~0#1.base| (- 4) (* 16 |ULTIMATE.start_main_~i~0#1|)) v_ArrVal_282) (+ 16 |ULTIMATE.start_main_~#volArray~0#1.base|)))) (< v_ArrVal_284 (select |#memory_int| (+ (- 16) |ULTIMATE.start_main_~#volArray~0#1.base| (* 16 |ULTIMATE.start_main_~i~0#1|))))))";
		final String expectedResultAsString = "(<= |ULTIMATE.start_main_~MINVAL~0#1| (select |#memory_int| (+ 16 |ULTIMATE.start_main_~#volArray~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3a202880_9e9f40ea_Treesizes_230_110() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#BOOL_unsigned_char_Array_0~0.base", "~#unsigned_long_int_Array_0~0.base", "~#unsigned_short_int_Array_0~0.base", "~#double_Array_0~0.base", "~last_1_unsigned_long_int_Array_0_1__0_~0"),
		};
		final String formulaAsString = "(and (not (= |~#BOOL_unsigned_char_Array_0~0.base| (+ |~#unsigned_long_int_Array_0~0.base| 11))) (<= 256 (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|))) (or (and (<= (+ (mod (+ (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 65535 (* (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|)) 65535) (select |#memory_int| (+ |~#unsigned_long_int_Array_0~0.base| 4))) 65536) 65535) (+ (mod (+ 131069 (* (mod (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 65536) 4294967295) (* (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|)) 4294967295) (select |#memory_int| (+ |~#unsigned_long_int_Array_0~0.base| 4))) 4294967296) (mod (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 65536))) (<= (+ (mod (+ 131069 (* (mod (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 65536) 4294967295) (* (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|)) 4294967295) (select |#memory_int| (+ |~#unsigned_long_int_Array_0~0.base| 4))) 4294967296) (mod (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 65536) (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|)) (mod (+ (* (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 65535) (* 65535 (select |#memory_int| (+ |~#unsigned_long_int_Array_0~0.base| 4))) 65535) 65536) (* (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 2)) (+ 4295163899 (* (div (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 65536) 131072)))) (< (+ (mod (+ 131069 (* (mod (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 65536) 4294967295) (* (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|)) 4294967295) (select |#memory_int| (+ |~#unsigned_long_int_Array_0~0.base| 4))) 4294967296) (mod (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 65536) (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|)) (mod (+ (* (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 65535) (* 65535 (select |#memory_int| (+ |~#unsigned_long_int_Array_0~0.base| 4))) 65535) 65536) (* (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 2)) (+ (* (div (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|) 65536) 131072) 196604))) (not (= (+ 3 |~#unsigned_long_int_Array_0~0.base|) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (+ |~#BOOL_unsigned_char_Array_0~0.base| 1) |~#unsigned_short_int_Array_0~0.base|)) (= ~last_1_unsigned_long_int_Array_0_1__0_~0 256) (not (= |~#unsigned_short_int_Array_0~0.base| (+ |~#double_Array_0~0.base| 8))) (not (= |~#double_Array_0~0.base| (+ |~#unsigned_long_int_Array_0~0.base| 4))) (not (= (+ |~#double_Array_0~0.base| 4) |~#unsigned_long_int_Array_0~0.base|)))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|))) (.cse4 (+ |~#unsigned_long_int_Array_0~0.base| 4))) (and (not (= |~#BOOL_unsigned_char_Array_0~0.base| (+ |~#unsigned_long_int_Array_0~0.base| 11))) (<= 256 .cse0) (let ((.cse2 (select |#memory_int| .cse4)) (.cse1 (select |#memory_int| |~#unsigned_short_int_Array_0~0.base|))) (<= (+ (mod (+ .cse1 65535 (* .cse0 65535) .cse2) 65536) .cse0 (* .cse1 2)) (let ((.cse3 (div .cse1 65536))) (+ (mod .cse1 65536) (* .cse3 131072) (mod (+ .cse1 (* 4294901760 .cse3) .cse2) 4294967296) 65534)))) (not (= (+ 3 |~#unsigned_long_int_Array_0~0.base|) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (+ |~#BOOL_unsigned_char_Array_0~0.base| 1) |~#unsigned_short_int_Array_0~0.base|)) (= ~last_1_unsigned_long_int_Array_0_1__0_~0 256) (not (= |~#unsigned_short_int_Array_0~0.base| (+ |~#double_Array_0~0.base| 8))) (not (= |~#double_Array_0~0.base| .cse4)) (not (= (+ |~#double_Array_0~0.base| 4) |~#unsigned_long_int_Array_0~0.base|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3a521930_f465e7b2_Treesizes_129_16() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_40~0", "~var_1_41~0", "assume_abort_if_not_#in~cond", "~var_1_42~0", "~var_1_26~0", "~var_1_39~0"),
		};
		final String formulaAsString = "(and (or (< (mod (+ (mod ~var_1_39~0 65536) ~var_1_40~0 ~var_1_41~0) 4294967296) (div (mod ~var_1_40~0 4294967296) 256)) (and (or (< (+ (div (mod ~var_1_40~0 4294967296) 256) (mod ~var_1_39~0 65536)) (+ (mod (+ 4294967295 (mod ~var_1_39~0 65536) ~var_1_40~0 ~var_1_42~0 ~var_1_41~0) 4294967296) 2)) (< (div (mod ~var_1_40~0 4294967296) 256) 1)) (<= (div (mod ~var_1_40~0 4294967296) 256) (mod (+ (mod ~var_1_39~0 65536) ~var_1_40~0 ~var_1_42~0 ~var_1_41~0) 4294967296))) (< (+ (mod (+ 4294967295 (mod ~var_1_39~0 65536) ~var_1_40~0 ~var_1_41~0) 4294967296) 1) (+ (div (mod ~var_1_40~0 4294967296) 256) (mod ~var_1_39~0 65536))) (and (or (not (= |assume_abort_if_not_#in~cond| 0)) (< (mod ~var_1_42~0 4294967296) 536870912)) (or (< 536870911 (mod ~var_1_42~0 4294967296)) (not (= |assume_abort_if_not_#in~cond| 1)))) (< 3758096384 (mod (+ (mod ~var_1_39~0 65536) ~var_1_40~0 ~var_1_41~0) 4294967296))) (<= 0 (+ 31 ~var_1_26~0)) (not (= |assume_abort_if_not_#in~cond| 0)) (not (= (mod ~var_1_39~0 65536) 0)))";
		final String expectedResultAsString = "(and (<= 0 (+ 31 ~var_1_26~0)) (not (= |assume_abort_if_not_#in~cond| 0)) (not (= (mod ~var_1_39~0 65536) 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3b26cd81_3e51b14c_Treesizes_22_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var5_Pointer~0.base", "~#unsigned_long_int_Array_0~0.base", "~double_Array_0_arraydouble_Array_0arrayVar9_Pointer~0.base", "~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var1_Pointer~0.base"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_239 Int)) (<= (mod (+ 255 (select (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_239) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var5_Pointer~0.base)) 256) 254)) (not (= ~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var1_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var5_Pointer~0.base)) (not (= ~double_Array_0_arraydouble_Array_0arrayVar9_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var5_Pointer~0.base)))";
		final String expectedResultAsString = "(and (<= (mod (+ 255 (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var5_Pointer~0.base)) 256) 254) (not (= |~#unsigned_long_int_Array_0~0.base| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var5_Pointer~0.base)) (not (= ~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var1_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var5_Pointer~0.base)) (not (= ~double_Array_0_arraydouble_Array_0arrayVar9_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var5_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3bc53919_b3842127_Treesizes_11_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(<= (mod (+ 255 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 11))) 256) 254)";
		final String expectedResultAsString = "(<= 1 (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 11)) 256))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3c84931f_b871c1ae_Treesizes_13_11() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_4~0", "~var_1_5~0"),
		};
		final String formulaAsString = "(and (not (= (mod ~var_1_4~0 256) 0)) (not (= (mod ~var_1_5~0 256) 0)))";
		final String expectedResultAsString = "(and (<= 1 (mod ~var_1_5~0 256)) (<= 1 (mod ~var_1_4~0 256)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3d02c985_87a2094_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_ring_buffer_acquire_harness_~#buf~3#1.base_BEFORE_CALL_42| Int)) (<= 8683 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_ring_buffer_acquire_harness_~#buf~3#1.base_BEFORE_CALL_42| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_ring_buffer_acquire_harness_~#buf~3#1.base_BEFORE_CALL_41| Int)) (<= 8683 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_ring_buffer_acquire_harness_~#buf~3#1.base_BEFORE_CALL_41| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3d81936b_609378af_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_23~0"),
		};
		final String formulaAsString = "(= (mod ~var_1_23~0 4294967296) 0)";
		final String expectedResultAsString = "(<= (mod ~var_1_23~0 4294967296) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3e10ab73_6f90c598_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_insert_before_~before.base_BEFORE_CALL_7 Int)) (and (<= 77 v_aws_linked_list_insert_before_~before.base_BEFORE_CALL_7) (<= (+ v_aws_linked_list_insert_before_~before.base_BEFORE_CALL_7 8) (select |#memory_$Pointer$.base| (+ v_aws_linked_list_insert_before_~before.base_BEFORE_CALL_7 4)))))";
		final String expectedResultAsString = "(exists ((v_aws_linked_list_insert_before_~before.base_BEFORE_CALL_5 Int)) (and (<= 77 v_aws_linked_list_insert_before_~before.base_BEFORE_CALL_5) (<= (+ v_aws_linked_list_insert_before_~before.base_BEFORE_CALL_5 8) (select |#memory_$Pointer$.base| (+ v_aws_linked_list_insert_before_~before.base_BEFORE_CALL_5 4)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3e8ffbba_a458de3b_Treesizes_27_7() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~a~0"),
		};
		final String formulaAsString = "(and (<= (+ (mod (+ 4294967295 ~a~0) 4294967296) 1) (mod ~a~0 4294967296)) (<= (+ (mod (+ 4294967295 ~a~0) 4294967296) (mod (+ (* 4294967295 ~a~0) 1) 4294967296)) 4294967294))";
		final String expectedResultAsString = "(<= (mod (+ 4294967295 ~a~0) 4294967296) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3f3967e3_353c8e4f_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_6_Pointer~0.base", "~var_1_7_Pointer~0.base"),
		};
		final String formulaAsString = "(<= (+ (mod (select |#memory_int| ~var_1_7_Pointer~0.base) 4294967296) (mod (+ 4294967295 (* (select |#memory_int| ~var_1_7_Pointer~0.base) 4294967295) (select |#memory_int| ~var_1_6_Pointer~0.base)) 4294967296)) 4294967294)";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| ~var_1_6_Pointer~0.base))) (<= (+ (mod (+ 4294967295 (* (select |#memory_int| ~var_1_7_Pointer~0.base) 4294967295) .cse0) 4294967296) 1) (mod .cse0 4294967296)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3f8f7b1b_b364895e_Treesizes_24_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_16_Pointer~0.base", "~var_1_8_Pointer~0.base", "~var_1_21_Pointer~0.base", "~var_1_20_Pointer~0.base", "~var_1_19_Pointer~0.base"),
		};
		final String formulaAsString = "(and (<= (mod (select |#memory_int| ~var_1_8_Pointer~0.base) 256) 0) (not (= ~var_1_8_Pointer~0.base ~var_1_19_Pointer~0.base)) (not (= ~var_1_8_Pointer~0.base ~var_1_16_Pointer~0.base)) (not (= ~var_1_8_Pointer~0.base ~var_1_21_Pointer~0.base)) (not (= ~var_1_8_Pointer~0.base ~var_1_20_Pointer~0.base)))";
		final String expectedResultAsString = "(forall ((v_ArrVal_317 Int) (v_ArrVal_316 Int) (v_ArrVal_315 Int) (v_ArrVal_314 Int)) (<= (mod (select (store (store (store (store |#memory_int| ~var_1_16_Pointer~0.base v_ArrVal_316) ~var_1_19_Pointer~0.base v_ArrVal_315) ~var_1_20_Pointer~0.base v_ArrVal_314) ~var_1_21_Pointer~0.base v_ArrVal_317) ~var_1_8_Pointer~0.base) 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4040c04_97d6e470_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_15| Int)) (<= (mod (+ 4294967295 (select |#memory_int| (+ |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_15| 8))) 4294967296) 4294967294))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_13| Int)) (<= (mod (+ 4294967295 (select |#memory_int| (+ |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_13| 8))) 4294967296) 4294967294))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_405cd732_f078beea_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_26| Int)) (<= 8688 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_26| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_25| Int)) (<= 8688 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_25| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_40a7717b_ecd5b62f_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_22~0"),
		};
		final String formulaAsString = "(<= (mod ~var_1_22~0 256) 0)";
		final String expectedResultAsString = "(= (mod ~var_1_22~0 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_41094eac_3305809b_Treesizes_55_27() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base", "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_eq_~b#1.base", "ULTIMATE.start_aws_byte_cursor_eq_~a#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2| Int) (|v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| Int)) (and (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| 4)) 0) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2| 8) |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4|) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2|) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4|)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2| 4)) 0))) (= (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_eq_~a#1.base|) (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_eq_~b#1.base|)) (<= (+ |ULTIMATE.start_aws_byte_cursor_eq_~a#1.base| 8) |ULTIMATE.start_aws_byte_cursor_eq_~b#1.base|) (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_eq_~a#1.base| 4)) 0) (= (select |#memory_$Pointer$.base| (+ 4 |ULTIMATE.start_aws_byte_cursor_eq_~b#1.base|)) 0))";
		final String expectedResultAsString = "(and (= (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_eq_~a#1.base|) (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_eq_~b#1.base|)) (<= (+ |ULTIMATE.start_aws_byte_cursor_eq_~a#1.base| 8) |ULTIMATE.start_aws_byte_cursor_eq_~b#1.base|) (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_eq_~a#1.base| 4)) 0) (= (select |#memory_$Pointer$.base| (+ 4 |ULTIMATE.start_aws_byte_cursor_eq_~b#1.base|)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_41bc04f4_4b699d85_Treesizes_89_89() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "func_to_recursive_line_31_to_42_0_~y3.base", "func_to_recursive_line_31_to_42_0_~y1.base", "func_to_recursive_line_31_to_42_0_~x1.base", "func_to_recursive_line_31_to_42_0_~y2.base"),
		};
		final String formulaAsString = "(forall ((|v_func_to_recursive_line_31_to_42_0_#t~mem5_22| Int)) (= (+ (* |v_func_to_recursive_line_31_to_42_0_#t~mem5_22| (select (store (store |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base (+ (select |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base) 1)) func_to_recursive_line_31_to_42_0_~y3.base (+ (- 1) (select (store |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base (+ (select |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base) 1)) func_to_recursive_line_31_to_42_0_~y3.base))) func_to_recursive_line_31_to_42_0_~y1.base)) (select (store (store |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base (+ (select |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base) 1)) func_to_recursive_line_31_to_42_0_~y3.base (+ (- 1) (select (store |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base (+ (select |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base) 1)) func_to_recursive_line_31_to_42_0_~y3.base))) func_to_recursive_line_31_to_42_0_~y2.base) (select (store |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base (+ (select |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base) 1)) func_to_recursive_line_31_to_42_0_~y3.base)) (+ (select (store (store |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base (+ (select |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base) 1)) func_to_recursive_line_31_to_42_0_~y3.base (+ (- 1) (select (store |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base (+ (select |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base) 1)) func_to_recursive_line_31_to_42_0_~y3.base))) func_to_recursive_line_31_to_42_0_~x1.base) 1)))";
		final String expectedResultAsString = "(forall ((|func_to_recursive_line_31_to_42_0_#t~mem5| Int)) (let ((.cse2 (store |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base (+ (select |#memory_int| func_to_recursive_line_31_to_42_0_~y2.base) 1)))) (let ((.cse1 (select .cse2 func_to_recursive_line_31_to_42_0_~y3.base))) (let ((.cse0 (store .cse2 func_to_recursive_line_31_to_42_0_~y3.base (+ (- 1) .cse1)))) (= (+ (select .cse0 func_to_recursive_line_31_to_42_0_~x1.base) 1) (+ (* |func_to_recursive_line_31_to_42_0_#t~mem5| (select .cse0 func_to_recursive_line_31_to_42_0_~y1.base)) (select .cse0 func_to_recursive_line_31_to_42_0_~y2.base) .cse1))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4242d5e8_28e2bc7d_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_26~0"),
		};
		final String formulaAsString = "(= (mod ~var_1_26~0 256) 0)";
		final String expectedResultAsString = "(<= (mod ~var_1_26~0 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_428253d7_557a109e_Treesizes_38_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations", "ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base", "ULTIMATE.start_aws_byte_buf_advance_harness_~#output~0#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base_BEFORE_CALL_37| Int)) (and (<= 8680 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base_BEFORE_CALL_37| 4))) (<= 8682 |v_ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base_BEFORE_CALL_37|) (<= (+ |v_ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base_BEFORE_CALL_37| 32) |#StackAllocations|))) (<= 8682 |ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base|) (<= (+ 16 |ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base|) |ULTIMATE.start_aws_byte_buf_advance_harness_~#output~0#1.base|) (<= 8680 (select |#memory_$Pointer$.base| (+ 4 |ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base|))) (<= (+ |ULTIMATE.start_aws_byte_buf_advance_harness_~#output~0#1.base| 16) |#StackAllocations|))";
		final String expectedResultAsString = "(and (<= 8682 |ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base|) (<= (+ 16 |ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base|) |ULTIMATE.start_aws_byte_buf_advance_harness_~#output~0#1.base|) (<= 8680 (select |#memory_$Pointer$.base| (+ 4 |ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base|))) (<= (+ |ULTIMATE.start_aws_byte_buf_advance_harness_~#output~0#1.base| 16) |#StackAllocations|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_42a727c0_60fd5d3c_Treesizes_54_33() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_3_Pointer~0.base", "~var_1_11_Pointer~0.base", "~var_1_1_Pointer~0.base", "~var_1_4_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~var_1_1_Pointer~0.base ~var_1_4_Pointer~0.base)) (not (= ~var_1_1_Pointer~0.base ~var_1_11_Pointer~0.base)) (<= (+ (mod (+ (select |#memory_int| ~var_1_4_Pointer~0.base) (select |#memory_int| ~var_1_3_Pointer~0.base) (* 65535 (select |#memory_int| ~var_1_1_Pointer~0.base))) 65536) (mod (select |#memory_int| ~var_1_1_Pointer~0.base) 65536)) 65535) (not (= ~var_1_3_Pointer~0.base ~var_1_11_Pointer~0.base)) (not (= ~var_1_11_Pointer~0.base ~var_1_4_Pointer~0.base)) (<= (mod (+ (select |#memory_int| ~var_1_4_Pointer~0.base) (select |#memory_int| ~var_1_3_Pointer~0.base)) 65536) (mod (select |#memory_int| ~var_1_1_Pointer~0.base) 65536)))";
		final String expectedResultAsString = "(and (not (= ~var_1_1_Pointer~0.base ~var_1_4_Pointer~0.base)) (not (= ~var_1_1_Pointer~0.base ~var_1_11_Pointer~0.base)) (not (= ~var_1_3_Pointer~0.base ~var_1_11_Pointer~0.base)) (not (= ~var_1_11_Pointer~0.base ~var_1_4_Pointer~0.base)) (<= (mod (+ (select |#memory_int| ~var_1_4_Pointer~0.base) (select |#memory_int| ~var_1_3_Pointer~0.base) (* 65535 (select |#memory_int| ~var_1_1_Pointer~0.base))) 65536) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4359f630_a6e7554d_Treesizes_41_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "func_to_recursive_line_29_to_40_0_~a.base", "func_to_recursive_line_29_to_40_0_~t.base", "func_to_recursive_line_29_to_40_0_~s.base"),
		};
		final String formulaAsString = "(and (= (+ (* (select |#memory_int| func_to_recursive_line_29_to_40_0_~a.base) 2) 1) (select |#memory_int| func_to_recursive_line_29_to_40_0_~t.base)) (exists ((v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_25 Int) (v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_32 Int)) (and (not (= v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_32 v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_25)) (= (+ (* (select |#memory_int| v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_25) 2) 1) (select |#memory_int| v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_32)))) (not (= func_to_recursive_line_29_to_40_0_~a.base func_to_recursive_line_29_to_40_0_~t.base)) (not (= func_to_recursive_line_29_to_40_0_~a.base func_to_recursive_line_29_to_40_0_~s.base)) (not (= func_to_recursive_line_29_to_40_0_~s.base func_to_recursive_line_29_to_40_0_~t.base)))";
		final String expectedResultAsString = "(and (= (+ (* (select |#memory_int| func_to_recursive_line_29_to_40_0_~a.base) 2) 1) (select |#memory_int| func_to_recursive_line_29_to_40_0_~t.base)) (not (= func_to_recursive_line_29_to_40_0_~a.base func_to_recursive_line_29_to_40_0_~t.base)) (not (= func_to_recursive_line_29_to_40_0_~a.base func_to_recursive_line_29_to_40_0_~s.base)) (not (= func_to_recursive_line_29_to_40_0_~s.base func_to_recursive_line_29_to_40_0_~t.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_43afa421_8239ef4f_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_byte_buf_append_~from.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_buf_append_harness_~#from~0#1.base_BEFORE_CALL_9| Int)) (= 0 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_append_harness_~#from~0#1.base_BEFORE_CALL_9|)))) (= (select |#memory_$Pointer$.base| (+ aws_byte_buf_append_~from.base 4)) 0))";
		final String expectedResultAsString = "(= (select |#memory_$Pointer$.base| (+ aws_byte_buf_append_~from.base 4)) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_440fec24_76261110_Treesizes_15_15() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~l_8~0", "~f1_2~0"),
		};
		final String formulaAsString = "(and (or (< 0 ~f1_2~0) (= ~l_8~0 0)) (or (< ~f1_2~0 1) (= ~l_8~0 1)))";
		final String expectedResultAsString = "(or (and (<= 1 ~f1_2~0) (= ~l_8~0 1)) (and (= ~l_8~0 0) (<= ~f1_2~0 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_44d3a7a7_7ba98a92_Treesizes_22_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_11_Pointer~0.base", "~WrapperStruct00_var_1_10_Pointer~0.base", "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_13_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~WrapperStruct00_var_1_11_Pointer~0.base ~WrapperStruct00_var_1_8_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_10_Pointer~0.base ~WrapperStruct00_var_1_8_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_1_Pointer~0.base ~WrapperStruct00_var_1_8_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_13_Pointer~0.base ~WrapperStruct00_var_1_8_Pointer~0.base)) (<= 0 (select |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~WrapperStruct00_var_1_11_Pointer~0.base ~WrapperStruct00_var_1_8_Pointer~0.base)) (forall ((v_ArrVal_258 Int) (v_ArrVal_259 Int)) (<= 0 (select (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_258) ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_259) ~WrapperStruct00_var_1_8_Pointer~0.base))) (not (= ~WrapperStruct00_var_1_1_Pointer~0.base ~WrapperStruct00_var_1_8_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_45a8a80f_c87dffba_Treesizes_14_10() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "sum_#in~x.base", "sum_~x.base", "sum_~i~0", "sum_~ret~0"),
		};
		final String formulaAsString = "(and (= sum_~ret~0 0) (= |sum_#in~x.base| sum_~x.base) (= |sum_#in~x.base| (+ sum_~x.base (* sum_~i~0 4))))";
		final String expectedResultAsString = "(and (= sum_~ret~0 0) (= sum_~i~0 0) (= |sum_#in~x.base| sum_~x.base))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_461a4da8_4bcd56a2_Treesizes_27_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations", "aws_byte_cursor_read_~cur#1.base"),
		};
		final String formulaAsString = "(and (<= (+ 23 |aws_byte_cursor_read_~cur#1.base|) |#StackAllocations|) (exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30| Int)) (and (<= (+ 23 |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30|) |#StackAllocations|) (<= 2 (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30|) 4294967296)))) (<= 2 (mod (select |#memory_int| |aws_byte_cursor_read_~cur#1.base|) 4294967296)))";
		final String expectedResultAsString = "(and (<= (+ 23 |aws_byte_cursor_read_~cur#1.base|) |#StackAllocations|) (<= 2 (mod (select |#memory_int| |aws_byte_cursor_read_~cur#1.base|) 4294967296)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_46b42087_f16723c6_Treesizes_11_11() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_array_eq_harness_~lhs_len~0#1", "ULTIMATE.start_aws_array_eq_harness_~rhs_len~0#1"),
		};
		final String formulaAsString = "(and (= (mod |ULTIMATE.start_aws_array_eq_harness_~lhs_len~0#1| 4294967296) 0) (= (mod |ULTIMATE.start_aws_array_eq_harness_~rhs_len~0#1| 4294967296) 0))";
		final String expectedResultAsString = "(and (= (mod |ULTIMATE.start_aws_array_eq_harness_~rhs_len~0#1| 4294967296) 0) (<= (mod |ULTIMATE.start_aws_array_eq_harness_~lhs_len~0#1| 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_474e0392_5308c438_Treesizes_23_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ensure_array_list_has_allocated_data_member_~list.base", "ensure_array_list_has_allocated_data_member_#in~list.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ensure_array_list_has_allocated_data_member_#in~list.base_BEFORE_CALL_3| Int)) (= (mod (select |#memory_int| (+ |v_ensure_array_list_has_allocated_data_member_#in~list.base_BEFORE_CALL_3| 4)) 4294967296) 0)) (= ensure_array_list_has_allocated_data_member_~list.base |ensure_array_list_has_allocated_data_member_#in~list.base|) (= 0 (mod (select |#memory_int| (+ ensure_array_list_has_allocated_data_member_~list.base 4)) 4294967296)))";
		final String expectedResultAsString = "(and (= ensure_array_list_has_allocated_data_member_~list.base |ensure_array_list_has_allocated_data_member_#in~list.base|) (= 0 (mod (select |#memory_int| (+ ensure_array_list_has_allocated_data_member_~list.base 4)) 4294967296)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_47ba4733_5c556647_Treesizes_35_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_linked_list_remove_~node#1.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_$Pointer$.base| (+ 4 (select |#memory_$Pointer$.base| |aws_linked_list_remove_~node#1.base|))) |aws_linked_list_remove_~node#1.base|) (exists ((|v_aws_linked_list_remove_~node#1.base_BEFORE_CALL_11| Int)) (and (= |v_aws_linked_list_remove_~node#1.base_BEFORE_CALL_11| (select |#memory_$Pointer$.base| (+ (select |#memory_$Pointer$.base| |v_aws_linked_list_remove_~node#1.base_BEFORE_CALL_11|) 4))) (<= (+ (select |#memory_$Pointer$.base| |v_aws_linked_list_remove_~node#1.base_BEFORE_CALL_11|) 8) |v_aws_linked_list_remove_~node#1.base_BEFORE_CALL_11|))) (<= (+ 8 (select |#memory_$Pointer$.base| |aws_linked_list_remove_~node#1.base|)) |aws_linked_list_remove_~node#1.base|))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_$Pointer$.base| |aws_linked_list_remove_~node#1.base|))) (and (= (select |#memory_$Pointer$.base| (+ 4 .cse0)) |aws_linked_list_remove_~node#1.base|) (<= (+ 8 .cse0) |aws_linked_list_remove_~node#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4831fd63_c1c7a61_Treesizes_37_37() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_30 Int) (v_func_to_recursive_line_29_to_41_0_~n.base_BEFORE_CALL_26 Int) (v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_27 Int) (v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_22 Int)) (and (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~n.base_BEFORE_CALL_26) 0) (<= (+ v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_30 8) v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_27) (<= (+ v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_22 8) v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_30) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_27) 6) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_30) 1) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_22) 0) (<= (+ 8 v_func_to_recursive_line_29_to_41_0_~n.base_BEFORE_CALL_26) v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_22)))";
		final String expectedResultAsString = "(exists ((v_func_to_recursive_line_29_to_41_0_~n.base_BEFORE_CALL_25 Int) (v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_26 Int) (v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_29 Int) (v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_21 Int)) (and (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_29) 1) (<= (+ 8 v_func_to_recursive_line_29_to_41_0_~n.base_BEFORE_CALL_25) v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_21) (= 6 (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_26)) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_21) 0) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~n.base_BEFORE_CALL_25) 0) (<= (+ v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_21 8) v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_29) (<= (+ v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_29 8) v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_26)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_48a04491_764f7a77_Treesizes_13_12() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_10~0", "~var_1_9~0"),
		};
		final String formulaAsString = "(and (not (= 0 (mod ~var_1_10~0 256))) (not (= (mod ~var_1_9~0 256) 0)))";
		final String expectedResultAsString = "(and (not (= (mod ~var_1_9~0 256) 0)) (<= 1 (mod ~var_1_10~0 256)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_491bf059_578b652_Treesizes_16_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_8_Pointer~0.base", "~#var_1_15~0.base", "~#var_1_16~0.base"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_627 Int)) (<= (mod (select (store |#memory_int| |~#var_1_15~0.base| v_ArrVal_627) ~var_1_8_Pointer~0.base) 256) 0)) (not (= ~var_1_8_Pointer~0.base |~#var_1_16~0.base|)))";
		final String expectedResultAsString = "(and (<= (mod (select |#memory_int| ~var_1_8_Pointer~0.base) 256) 0) (not (= ~var_1_8_Pointer~0.base |~#var_1_16~0.base|)) (not (= ~var_1_8_Pointer~0.base |~#var_1_15~0.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_49be4cb7_547dabbd_Treesizes_17_12() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_16~0", "~var_1_25~0", "~var_1_29~0"),
		};
		final String formulaAsString = "(and (<= 128 ~var_1_16~0) (<= 32 ~var_1_25~0) (<= (+ 16 ~var_1_29~0) 0) (<= (+ ~var_1_16~0 ~var_1_25~0) 160))";
		final String expectedResultAsString = "(and (= 128 ~var_1_16~0) (= 32 ~var_1_25~0) (<= (+ 16 ~var_1_29~0) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4a449410_97bd76fe_Treesizes_112_108() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_11~0", "~var_1_10~0", "~var_1_14~0", "~last_1_var_1_13~0", "~var_1_13~0", "~last_1_var_1_12~0", "~var_1_8~0", "~var_1_9~0", "~var_1_19~0", "~var_1_6~0", "~last_1_var_1_18~0", "~var_1_18~0", "~last_1_var_1_1~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (<= (+ (mod ~last_1_var_1_18~0 256) ~var_1_13~0) (+ (mod ~var_1_14~0 65536) (mod ~var_1_13~0 65536))) (= 0 (mod ~var_1_10~0 256)) (or (and (or (not (= (mod ~var_1_8~0 256) 0)) (= (mod ~var_1_6~0 256) 0) (not (= (mod ~var_1_9~0 256) 0))) (or (= (mod ~var_1_6~0 256) 1) (and (= (mod ~var_1_9~0 256) 0) (= (mod ~var_1_8~0 256) 0)))) (< 0 (+ ~last_1_var_1_1~0 1))) (= ~var_1_11~0 0) (= (div ~last_1_var_1_13~0 65536) 0) (= (mod ~var_1_19~0 256) (mod ~var_1_18~0 256)) (not (= (mod ~last_1_var_1_12~0 256) 0)) (= (mod (+ (* (mod ~last_1_var_1_18~0 256) 65535) ~var_1_14~0) 65536) (mod ~var_1_13~0 65536)) (= ~var_1_1~0 ~last_1_var_1_13~0) (<= (+ (mod ~var_1_14~0 65536) (mod ~var_1_13~0 65536)) (+ (mod ~last_1_var_1_18~0 256) ~var_1_13~0 65535)))";
		final String expectedResultAsString = "(let ((.cse3 (mod ~last_1_var_1_18~0 256))) (and (= 0 (mod ~var_1_10~0 256)) (or (let ((.cse1 (mod ~var_1_6~0 256)) (.cse2 (= (mod ~var_1_9~0 256) 0)) (.cse0 (= (mod ~var_1_8~0 256) 0))) (and (or (not .cse0) (= .cse1 0) (not .cse2)) (or (= .cse1 1) (and .cse2 .cse0)))) (< 0 (+ ~last_1_var_1_1~0 1))) (= ~var_1_11~0 0) (= (div ~last_1_var_1_13~0 65536) 0) (= (mod ~var_1_19~0 256) (mod ~var_1_18~0 256)) (not (= (mod ~last_1_var_1_12~0 256) 0)) (= (mod (+ (* .cse3 65535) ~var_1_14~0) 65536) (mod ~var_1_13~0 65536)) (= ~var_1_1~0 ~last_1_var_1_13~0) (= (+ (div ~var_1_13~0 65536) (div ~var_1_14~0 65536) .cse3) (div (+ (* (- 16776960) (div ~last_1_var_1_18~0 256)) (* ~last_1_var_1_18~0 65535) ~var_1_14~0) 65536))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4ab0f568_ec8f5733_Treesizes_14_12() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~state_13~0#1", "ULTIMATE.start_main_~state_26~0#1", "ULTIMATE.start_main_~state_25~0#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~state_26~0#1| 0) (= |ULTIMATE.start_main_~state_25~0#1| 0) (<= (mod (* |ULTIMATE.start_main_~state_13~0#1| 255) 256) 0))";
		final String expectedResultAsString = "(and (<= (mod |ULTIMATE.start_main_~state_13~0#1| 256) 0) (= |ULTIMATE.start_main_~state_26~0#1| 0) (= |ULTIMATE.start_main_~state_25~0#1| 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4b1e05ba_cf8760d3_Treesizes_9_9() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~last_1_var_1_15~0", "~var_1_6~0"),
		};
		final String formulaAsString = "(<= (+ (mod ~last_1_var_1_15~0 65536) (mod ~var_1_6~0 256)) 32767)";
		final String expectedResultAsString = "(< (+ (mod ~last_1_var_1_15~0 65536) (mod ~var_1_6~0 256)) 32768)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4b6c57f_8e67dc7f_Treesizes_17_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_buf_append_harness_~#to~0#1.base_BEFORE_CALL_25| Int)) (<= 8679 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_append_harness_~#to~0#1.base_BEFORE_CALL_25| 4)))) (exists ((v_aws_byte_buf_append_~to.base_BEFORE_CALL_4 Int)) (<= 8679 (select |#memory_$Pointer$.base| (+ v_aws_byte_buf_append_~to.base_BEFORE_CALL_4 4)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_harness_~#to~0#1.base_BEFORE_CALL_25| Int)) (<= 8679 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_append_harness_~#to~0#1.base_BEFORE_CALL_25| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4c0c6daa_6f83dca6_Treesizes_34_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(<= (+ (div (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5)) 65536) 1) (+ (div (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) 65536) (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5)) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) (- 1)) 65535) 65536)))";
		final String expectedResultAsString = "(<= (+ (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) 65536) 1) (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5)) 65536))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4c85f1f7_7e6d24f1_Treesizes_13_11() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_14~0", "~var_1_19~0"),
		};
		final String formulaAsString = "(and (not (= (mod ~var_1_14~0 256) 0)) (not (= (mod ~var_1_19~0 256) 0)))";
		final String expectedResultAsString = "(and (<= 1 (mod ~var_1_19~0 256)) (<= 1 (mod ~var_1_14~0 256)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4d4beedd_5c03bfad_Treesizes_11_9() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~var_106_arg_1~0#1"),
		};
		final String formulaAsString = "(and (<= (mod |ULTIMATE.start_main_~var_106_arg_1~0#1| 256) 0) (<= 0 (div |ULTIMATE.start_main_~var_106_arg_1~0#1| 256)))";
		final String expectedResultAsString = "(and (<= (mod |ULTIMATE.start_main_~var_106_arg_1~0#1| 256) 0) (<= 0 |ULTIMATE.start_main_~var_106_arg_1~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4d79f34f_fb6a5981_Treesizes_39_39() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_6 Int) (v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_2 Int) (v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_3 Int)) (and (= 6 (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_2)) (exists ((func_to_recursive_line_29_to_41_0_~n.base Int)) (and (= (select |#memory_int| func_to_recursive_line_29_to_41_0_~n.base) 0) (<= (+ func_to_recursive_line_29_to_41_0_~n.base 8) v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_6))) (<= (+ v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_3 8) v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_2) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_3) 1) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_6) 0) (<= (+ v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_6 8) v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_3)))";
		final String expectedResultAsString = "(exists ((v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_5 Int) (v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_1 Int) (v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_2 Int)) (and (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_2) 1) (= 6 (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_1)) (<= (+ v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_2 8) v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_1) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_5) 0) (exists ((func_to_recursive_line_29_to_41_0_~n.base Int)) (and (= (select |#memory_int| func_to_recursive_line_29_to_41_0_~n.base) 0) (<= (+ func_to_recursive_line_29_to_41_0_~n.base 8) v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_5))) (<= (+ v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_5 8) v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_2)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4da1098f_6ee27df1_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_clean_up_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| (+ 8 |ULTIMATE.start_aws_byte_buf_clean_up_harness_~#buf~3#1.base|)) 0) (exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_harness_~#buf~3#1.base_BEFORE_CALL_27| Int)) (= 0 (select |#memory_int| (+ |v_ULTIMATE.start_aws_byte_buf_clean_up_harness_~#buf~3#1.base_BEFORE_CALL_27| 8)))))";
		final String expectedResultAsString = "(= (select |#memory_int| (+ 8 |ULTIMATE.start_aws_byte_buf_clean_up_harness_~#buf~3#1.base|)) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4e2a94e3_86a29c59_Treesizes_9_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_byte_cursor_is_valid_#in~cursor.base"),
		};
		final String formulaAsString = "(<= (mod (+ 4294967295 (select |#memory_int| |aws_byte_cursor_is_valid_#in~cursor.base|)) 4294967296) 4294967294)";
		final String expectedResultAsString = "(not (= (mod (select |#memory_int| |aws_byte_cursor_is_valid_#in~cursor.base|) 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4ef4a660_72f4e137_Treesizes_101_49() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base"),
		};
		final String formulaAsString = "(and (or (exists ((|v_ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base_BEFORE_CALL_27| Int)) (and (= (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base_BEFORE_CALL_27|)) 0) (exists ((v_z_16 Int)) (and (= (select |#memory_int| (+ v_z_16 4 |v_ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base_BEFORE_CALL_27|)) 0) (<= v_z_16 2147483647) (<= 0 v_z_16))))) (exists ((|v_ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base_BEFORE_CALL_27| Int)) (and (exists ((v_z_20 Int)) (and (<= v_z_20 4294967295) (<= 2147483648 v_z_20) (= (select |#memory_int| (+ (- 4294967292) v_z_20 |v_ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base_BEFORE_CALL_27|)) 0))) (= (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base_BEFORE_CALL_27|)) 0)))) (or (and (exists ((v_z_20 Int)) (and (= (select |#memory_int| (+ (- 4294967292) v_z_20 |ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base|)) 0) (<= v_z_20 4294967295) (<= 2147483648 v_z_20))) (= (select |#memory_int| (+ 4 |ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base|)) 0)) (and (exists ((v_z_16 Int)) (and (= (select |#memory_int| (+ v_z_16 4 |ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base|)) 0) (<= v_z_16 2147483647) (<= 0 v_z_16))) (= (select |#memory_int| (+ 4 |ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base|)) 0))))";
		final String expectedResultAsString = "(let ((.cse0 (= (select |#memory_int| (+ 4 |ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base|)) 0))) (or (and (exists ((v_z_20 Int)) (and (= (select |#memory_int| (+ (- 4294967292) v_z_20 |ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base|)) 0) (<= v_z_20 4294967295) (<= 2147483648 v_z_20))) .cse0) (and (exists ((v_z_16 Int)) (and (= (select |#memory_int| (+ v_z_16 4 |ULTIMATE.start_aws_priority_queue_clean_up_harness_~#queue~0#1.base|)) 0) (<= v_z_16 2147483647) (<= 0 v_z_16))) .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4f16e2cc_3ded1de7_Treesizes_497_367() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~last_1_var_1_17~0", "~last_1_var_1_37~0", "~var_1_23~0", "~var_1_11~0", "~var_1_22~0", "~var_1_20~0", "~var_1_16~0", "~last_1_var_1_11~0", "~var_1_15~0", "~var_1_5~0", "~var_1_14~0", "~var_1_25~0", "~var_1_13~0", "~var_1_24~0", "~var_1_39~0", "~var_1_9~0", "~var_1_19~0", "~var_1_18~0", "~var_1_6~0", "~var_1_17~0", "~var_1_7~0", "~last_1_var_1_19~0", "~last_1_var_1_1~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (= ~var_1_1~0 1) (or (and (or (< (mod ~var_1_14~0 4294967296) (+ (mod ~var_1_18~0 4294967296) 1)) (= (mod (+ ~var_1_15~0 ~var_1_14~0) 4294967296) (mod ~var_1_17~0 4294967296)) (< (mod ~var_1_7~0 4294967296) (+ (mod ~var_1_6~0 4294967296) 1))) (or (and (or (and (<= (+ (mod ~var_1_6~0 4294967296) 1) (mod ~var_1_7~0 4294967296)) (= (mod (+ ~var_1_18~0 ~var_1_15~0) 4294967296) (mod ~var_1_17~0 4294967296))) (< (mod ~var_1_18~0 4294967296) (mod ~var_1_14~0 4294967296))) (or (< (mod ~var_1_14~0 4294967296) (+ (mod ~var_1_18~0 4294967296) 1)) (and (<= (+ (mod ~var_1_6~0 4294967296) 1) (mod ~var_1_7~0 4294967296)) (= (mod (+ ~var_1_15~0 ~var_1_14~0) 4294967296) (mod ~var_1_17~0 4294967296))))) (= (mod (+ (* 4294967295 ~var_1_15~0) 2284571271 (* 4294967295 ~var_1_14~0)) 4294967296) (mod ~var_1_17~0 4294967296))) (or (= (mod (+ ~var_1_18~0 ~var_1_15~0) 4294967296) (mod ~var_1_17~0 4294967296)) (< (mod ~var_1_18~0 4294967296) (mod ~var_1_14~0 4294967296)) (< (mod ~var_1_7~0 4294967296) (+ (mod ~var_1_6~0 4294967296) 1))) (or (= (mod (+ ~var_1_15~0 ~var_1_14~0) 4294967296) (mod ~var_1_17~0 4294967296)) (< (mod ~var_1_16~0 4294967296) (+ (mod ~var_1_18~0 4294967296) 1)) (< (mod ~var_1_7~0 4294967296) (+ (mod ~var_1_6~0 4294967296) 1)))) (< (mod ~var_1_14~0 4294967296) (mod ~var_1_16~0 4294967296))) (or (and (<= 0 ~var_1_9~0) (= (+ 64 ~var_1_14~0) (+ ~var_1_9~0 ~var_1_16~0 ~var_1_15~0 ~var_1_13~0))) (and (<= (+ ~var_1_9~0 1) 0) (= (+ ~var_1_16~0 ~var_1_15~0 ~var_1_13~0) (+ 64 ~var_1_9~0 ~var_1_14~0)))) (= (mod ~var_1_11~0 4294967296) 4) (<= (div ~var_1_19~0 256) (div ~var_1_20~0 256)) (<= (div ~var_1_24~0 256) (div ~var_1_23~0 256)) (<= (+ (mod ~var_1_17~0 4294967296) 1) (mod ~var_1_9~0 4294967296)) (= 2 ~last_1_var_1_17~0) (<= 2 (mod ~last_1_var_1_11~0 4294967296)) (<= (mod ~var_1_20~0 256) 0) (or (and (or (= (mod ~var_1_22~0 256) (mod ~var_1_24~0 256)) (and (= (mod ~last_1_var_1_19~0 256) 0) (= (mod ~var_1_20~0 256) 0))) (or (= (mod ~var_1_22~0 256) (mod ~var_1_24~0 256)) (< (mod ~var_1_5~0 4294967296) (mod ~last_1_var_1_1~0 4294967296)))) (< (mod (+ ~last_1_var_1_37~0 (* 2147418112 (div ~last_1_var_1_37~0 65536))) 2147483648) 3)) (or (and (or (< (mod ~var_1_16~0 4294967296) (+ (mod ~var_1_18~0 4294967296) 1)) (= (mod ~var_1_17~0 4294967296) (mod (+ ~var_1_16~0 ~var_1_15~0) 4294967296)) (< (mod ~var_1_7~0 4294967296) (+ (mod ~var_1_6~0 4294967296) 1))) (or (and (or (and (<= (+ (mod ~var_1_6~0 4294967296) 1) (mod ~var_1_7~0 4294967296)) (= (mod (+ ~var_1_18~0 ~var_1_15~0) 4294967296) (mod ~var_1_17~0 4294967296))) (< (mod ~var_1_18~0 4294967296) (mod ~var_1_16~0 4294967296))) (or (and (<= (+ (mod ~var_1_6~0 4294967296) 1) (mod ~var_1_7~0 4294967296)) (= (mod ~var_1_17~0 4294967296) (mod (+ ~var_1_16~0 ~var_1_15~0) 4294967296))) (< (mod ~var_1_16~0 4294967296) (+ (mod ~var_1_18~0 4294967296) 1)))) (= (mod (+ (* 4294967295 ~var_1_15~0) 2284571271 (* 4294967295 ~var_1_14~0)) 4294967296) (mod ~var_1_17~0 4294967296))) (or (= (mod (+ ~var_1_18~0 ~var_1_15~0) 4294967296) (mod ~var_1_17~0 4294967296)) (< (mod ~var_1_18~0 4294967296) (mod ~var_1_16~0 4294967296)) (< (mod ~var_1_7~0 4294967296) (+ (mod ~var_1_6~0 4294967296) 1)))) (< (mod ~var_1_16~0 4294967296) (+ (mod ~var_1_14~0 4294967296) 1))) (= (mod ~var_1_23~0 256) (mod ~var_1_24~0 256)) (<= ~var_1_23~0 ~var_1_24~0) (= (mod ~var_1_19~0 256) 0) (or (and (<= (mod ~var_1_23~0 256) (mod ~var_1_39~0 65536)) (or (and (<= (mod ~var_1_39~0 65536) 15) (= (mod ~var_1_39~0 65536) ~var_1_25~0)) (and (<= 16 (mod ~var_1_39~0 65536)) (= 16 ~var_1_25~0)))) (and (or (and (<= 16 (mod ~var_1_23~0 256)) (= 16 ~var_1_25~0)) (and (= (mod ~var_1_23~0 256) ~var_1_25~0) (<= (mod ~var_1_23~0 256) 15))) (<= (+ (mod ~var_1_39~0 65536) 1) (mod ~var_1_23~0 256)))))";
		final String expectedResultAsString = "(let ((.cse7 (mod ~var_1_18~0 4294967296)) (.cse14 (mod ~var_1_6~0 4294967296)) (.cse13 (mod ~var_1_7~0 4294967296)) (.cse4 (mod ~var_1_17~0 4294967296))) (let ((.cse9 (mod ~var_1_24~0 256)) (.cse1 (or (< .cse14 .cse13) (= (mod (+ (* 4294967295 ~var_1_15~0) 2284571271 (* 4294967295 ~var_1_14~0)) 4294967296) .cse4))) (.cse3 (+ .cse7 1)) (.cse6 (= (mod (+ ~var_1_18~0 ~var_1_15~0) 4294967296) .cse4)) (.cse5 (< .cse13 (+ .cse14 1))) (.cse8 (mod ~var_1_16~0 4294967296)) (.cse2 (mod ~var_1_14~0 4294967296)) (.cse0 (mod ~var_1_23~0 256))) (and (= ~var_1_1~0 1) (or (and (<= 0 ~var_1_9~0) (= (+ 64 ~var_1_14~0) (+ ~var_1_9~0 ~var_1_16~0 ~var_1_15~0 ~var_1_13~0))) (and (<= (+ ~var_1_9~0 1) 0) (= (+ ~var_1_16~0 ~var_1_15~0 ~var_1_13~0) (+ 64 ~var_1_9~0 ~var_1_14~0)))) (<= ~var_1_23~0 (+ .cse0 ~var_1_24~0)) (= (mod ~var_1_11~0 4294967296) 4) (<= (div ~var_1_19~0 256) (div ~var_1_20~0 256)) (<= (div ~var_1_24~0 256) (div ~var_1_23~0 256)) (or (and .cse1 (or (< .cse2 .cse3) (= (mod (+ ~var_1_15~0 ~var_1_14~0) 4294967296) .cse4) .cse5) (or .cse6 (< .cse7 .cse2) .cse5)) (< .cse2 .cse8)) (<= (+ .cse4 1) (mod ~var_1_9~0 4294967296)) (= 2 ~last_1_var_1_17~0) (<= 2 (mod ~last_1_var_1_11~0 4294967296)) (<= (mod ~var_1_20~0 256) 0) (= .cse0 .cse9) (or (let ((.cse10 (= (mod ~var_1_22~0 256) .cse9))) (and (or (= (mod ~last_1_var_1_19~0 256) 0) .cse10) (or .cse10 (< (mod ~var_1_5~0 4294967296) (mod ~last_1_var_1_1~0 4294967296))))) (< (mod (+ ~last_1_var_1_37~0 (* 2147418112 (div ~last_1_var_1_37~0 65536))) 2147483648) 3)) (= (mod ~var_1_19~0 256) 0) (or (and .cse1 (or (< .cse8 .cse3) (= .cse4 (mod (+ ~var_1_16~0 ~var_1_15~0) 4294967296)) .cse5) (or .cse6 (< .cse7 .cse8) .cse5)) (< .cse8 (+ .cse2 1))) (let ((.cse12 (= 16 ~var_1_25~0)) (.cse11 (mod ~var_1_39~0 65536))) (or (and (<= .cse0 .cse11) (or (and (<= .cse11 15) (= .cse11 ~var_1_25~0)) (and (<= 16 .cse11) .cse12))) (and (or (and (<= 16 .cse0) .cse12) (and (= .cse0 ~var_1_25~0) (<= .cse0 15))) (<= (+ .cse11 1) .cse0)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4f93ee95_6e378cc7_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_4| Int)) (and (<= 2 (mod (select |#memory_int| |v_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_4|) 4294967296)) (<= (+ 23 |v_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_4|) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30| Int)) (and (<= (+ 23 |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30|) |#StackAllocations|) (<= 2 (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30|) 4294967296))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4fa7ca9e_d064dc63_Treesizes_17_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_13| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_13| 4)) 0)) (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_14| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_14| 4)) 0)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_13| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_13| 4)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_500d0638_b326e06f_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_17~0"),
		};
		final String formulaAsString = "(= (mod ~var_1_17~0 256) 0)";
		final String expectedResultAsString = "(<= (mod ~var_1_17~0 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_506affff_8ff51e4a_Treesizes_17_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_4 Int) (v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_6 Int)) (and (= (select |#memory_int| v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_6) 1) (= (select |#memory_int| v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_4) 0) (<= (+ 16 v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_4) v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_6)))";
		final String expectedResultAsString = "(exists ((v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_3 Int) (v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_5 Int)) (and (= (select |#memory_int| v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_3) 0) (= (select |#memory_int| v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_5) 1) (<= (+ 16 v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_3) v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_5)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_511b7db2_4f389c2d_Treesizes_8_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var5_Pointer~0.base"),
		};
		final String formulaAsString = "(not (= 0 (mod (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var5_Pointer~0.base) 256)))";
		final String expectedResultAsString = "(<= 1 (mod (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var5_Pointer~0.base) 256))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_51386586_bbca20c9_Treesizes_35_33() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "~SIZE~0", "ULTIMATE.start_main_~#a~0#1.base", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(and (<= 4 ~SIZE~0) (or (and (= ~SIZE~0 (+ 2 |ULTIMATE.start_main_~i~0#1|)) (= |ULTIMATE.start_main_~sum~0#1| (+ (select |#memory_int| (+ (- 2) |ULTIMATE.start_main_~#a~0#1.base| (* ~SIZE~0 2))) (select |#memory_int| (+ |ULTIMATE.start_main_~#a~0#1.base| 4))))) (< ~SIZE~0 (+ 2 |ULTIMATE.start_main_~i~0#1|)) (< 4 ~SIZE~0)))";
		final String expectedResultAsString = "(and (<= 4 ~SIZE~0) (or (and (= 2 |ULTIMATE.start_main_~i~0#1|) (= |ULTIMATE.start_main_~sum~0#1| (+ (select |#memory_int| (+ (- 2) |ULTIMATE.start_main_~#a~0#1.base| (* ~SIZE~0 2))) (select |#memory_int| (+ |ULTIMATE.start_main_~#a~0#1.base| 4))))) (< ~SIZE~0 (+ 2 |ULTIMATE.start_main_~i~0#1|)) (< 4 ~SIZE~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_51c36caa_ccad40e7_Treesizes_7_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ldv_xmalloc_~res~9.base"),
		};
		final String formulaAsString = "(<= (mod (+ 4294967295 ldv_xmalloc_~res~9.base) 4294967296) 4294967294)";
		final String expectedResultAsString = "(<= 1 (mod ldv_xmalloc_~res~9.base 4294967296))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_52647456_4ec0bf13_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base"),
		};
		final String formulaAsString = "(<= 67 (select |#memory_$Pointer$.base| (+ 12 |ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base|)))";
		final String expectedResultAsString = "(< 66 (select |#memory_$Pointer$.base| (+ 12 |ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_52cc705b_4b969ed3_Treesizes_32_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base", "#StackAllocations", "ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base"),
		};
		final String formulaAsString = "(and (<= 8691 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base| 4))) (<= (+ 16 |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base|) |#StackAllocations|) (<= |#StackAllocations| (+ 8 |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base|)) (exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_35| Int)) (and (<= 8691 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_35|))) (<= (+ 16 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_35|) |#StackAllocations|))))";
		final String expectedResultAsString = "(and (<= 8691 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base| 4))) (<= (+ 16 |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base|) |#StackAllocations|) (<= |#StackAllocations| (+ 8 |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5321fa59_831b6e3d_Treesizes_24_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_linked_list_init_#in~list.base"),
		};
		final String formulaAsString = "(and (exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_2| Int)) (<= (+ |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_2| 8) (select |#memory_$Pointer$.base| |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_2|))) (<= (+ |aws_linked_list_init_#in~list.base| 8) (select |#memory_$Pointer$.base| |aws_linked_list_init_#in~list.base|)) (exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_5| Int)) (<= (+ |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_5| 8) (select |#memory_$Pointer$.base| |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_5|))))";
		final String expectedResultAsString = "(and (exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_2| Int)) (<= (+ |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_2| 8) (select |#memory_$Pointer$.base| |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_2|))) (<= (+ |aws_linked_list_init_#in~list.base| 8) (select |#memory_$Pointer$.base| |aws_linked_list_init_#in~list.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_53b697e6_35a42180_Treesizes_7_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~var_47_arg_0~0#1"),
		};
		final String formulaAsString = "(<= (mod (+ |ULTIMATE.start_main_~var_47_arg_0~0#1| 1) 256) 0)";
		final String expectedResultAsString = "(<= 255 (mod |ULTIMATE.start_main_~var_47_arg_0~0#1| 256))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_544ce045_cb1674e_Treesizes_102_63() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~k~0#1", "ULTIMATE.start_main_~x~0#1", "ULTIMATE.start_main_~a~0#1", "ULTIMATE.start_main_~q~0#1", "ULTIMATE.start_main_~r~0#1", "ULTIMATE.start_main_~s~0#1", "ULTIMATE.start_main_~b~0#1", "ULTIMATE.start_main_~p~0#1", "ULTIMATE.start_main_~c~0#1"),
		};
		final String formulaAsString = "(and (or (< |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_main_~b~0#1|) (= (+ (* |ULTIMATE.start_main_~r~0#1| |ULTIMATE.start_main_~y~0#1|) |ULTIMATE.start_main_~b~0#1| (* |ULTIMATE.start_main_~p~0#1| |ULTIMATE.start_main_~x~0#1|)) (+ |ULTIMATE.start_main_~a~0#1| (* |ULTIMATE.start_main_~s~0#1| |ULTIMATE.start_main_~y~0#1|) (* |ULTIMATE.start_main_~q~0#1| |ULTIMATE.start_main_~x~0#1|))) (< (* 2 |ULTIMATE.start_main_~b~0#1|) (+ |ULTIMATE.start_main_~a~0#1| 1)) (= |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_main_~b~0#1|)) (= (+ (* |ULTIMATE.start_main_~s~0#1| |ULTIMATE.start_main_~y~0#1|) (* |ULTIMATE.start_main_~q~0#1| |ULTIMATE.start_main_~x~0#1|)) |ULTIMATE.start_main_~b~0#1|) (or (= |ULTIMATE.start_main_~c~0#1| 0) (= (+ (* |ULTIMATE.start_main_~r~0#1| |ULTIMATE.start_main_~y~0#1|) (* |ULTIMATE.start_main_~p~0#1| |ULTIMATE.start_main_~x~0#1|)) (+ (* |ULTIMATE.start_main_~k~0#1| |ULTIMATE.start_main_~q~0#1| |ULTIMATE.start_main_~x~0#1|) (* |ULTIMATE.start_main_~k~0#1| |ULTIMATE.start_main_~s~0#1| |ULTIMATE.start_main_~y~0#1|) |ULTIMATE.start_main_~c~0#1|))) (or (= (+ (* |ULTIMATE.start_main_~k~0#1| |ULTIMATE.start_main_~q~0#1| |ULTIMATE.start_main_~x~0#1|) (* |ULTIMATE.start_main_~k~0#1| |ULTIMATE.start_main_~s~0#1| |ULTIMATE.start_main_~y~0#1|) |ULTIMATE.start_main_~c~0#1| (* |ULTIMATE.start_main_~s~0#1| |ULTIMATE.start_main_~y~0#1|) (* |ULTIMATE.start_main_~q~0#1| |ULTIMATE.start_main_~x~0#1|)) (+ (* |ULTIMATE.start_main_~r~0#1| |ULTIMATE.start_main_~y~0#1|) |ULTIMATE.start_main_~b~0#1| (* |ULTIMATE.start_main_~p~0#1| |ULTIMATE.start_main_~x~0#1|))) (= |ULTIMATE.start_main_~b~0#1| |ULTIMATE.start_main_~c~0#1|) (< (* 2 |ULTIMATE.start_main_~b~0#1|) (+ |ULTIMATE.start_main_~c~0#1| 1)) (< |ULTIMATE.start_main_~c~0#1| |ULTIMATE.start_main_~b~0#1|)))";
		final String expectedResultAsString = "(let ((.cse2 (* |ULTIMATE.start_main_~s~0#1| |ULTIMATE.start_main_~y~0#1|)) (.cse3 (* |ULTIMATE.start_main_~q~0#1| |ULTIMATE.start_main_~x~0#1|)) (.cse0 (* |ULTIMATE.start_main_~r~0#1| |ULTIMATE.start_main_~y~0#1|)) (.cse1 (* |ULTIMATE.start_main_~p~0#1| |ULTIMATE.start_main_~x~0#1|))) (and (or (< |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_main_~b~0#1|) (= (+ .cse0 |ULTIMATE.start_main_~b~0#1| .cse1) (+ |ULTIMATE.start_main_~a~0#1| .cse2 .cse3)) (< (* 2 |ULTIMATE.start_main_~b~0#1|) (+ |ULTIMATE.start_main_~a~0#1| 1)) (= |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_main_~b~0#1|)) (= (+ .cse2 .cse3) |ULTIMATE.start_main_~b~0#1|) (or (= |ULTIMATE.start_main_~c~0#1| 0) (= (+ .cse0 .cse1) (+ (* |ULTIMATE.start_main_~k~0#1| |ULTIMATE.start_main_~q~0#1| |ULTIMATE.start_main_~x~0#1|) (* |ULTIMATE.start_main_~k~0#1| |ULTIMATE.start_main_~s~0#1| |ULTIMATE.start_main_~y~0#1|) |ULTIMATE.start_main_~c~0#1|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_54d56524_1ddac4a3_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0"),
		};
		final String formulaAsString = "(= (mod ~var_1_1~0 256) 0)";
		final String expectedResultAsString = "(<= (mod ~var_1_1~0 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5547956d_a257cbc9_Treesizes_261_252() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~last_1_var_1_17~0", "~var_1_11~0", "~var_1_10~0", "~var_1_4~0", "~last_1_var_1_11~0", "~var_1_16~0", "~var_1_5~0", "~var_1_14~0", "~last_1_var_1_13~0", "~last_1_var_1_12~0", "~var_1_13~0", "~var_1_8~0", "~var_1_19~0", "~var_1_9~0", "~var_1_18~0", "~var_1_6~0", "~last_1_var_1_18~0", "~last_1_var_1_1~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (or (and (or (not (= (mod ~var_1_8~0 256) 0)) (and (not (= (mod ~last_1_var_1_12~0 256) 0)) (not (= (mod ~var_1_9~0 256) 0))) (= (mod ~var_1_6~0 256) 0)) (or (and (or (= (mod ~last_1_var_1_12~0 256) 0) (= (mod ~var_1_9~0 256) 0)) (= (mod ~var_1_8~0 256) 0)) (= (mod ~var_1_6~0 256) 1))) (< 0 (+ ~last_1_var_1_1~0 1))) (= 0 (mod ~var_1_10~0 256)) (<= (mod (+ (* (mod ~last_1_var_1_18~0 256) 65535) ~var_1_14~0) 65536) (mod ~var_1_13~0 65536)) (<= (+ (mod ~last_1_var_1_18~0 256) ~var_1_13~0) (mod ~var_1_14~0 65536)) (or (and (or (not (= (mod ~last_1_var_1_11~0 256) 0)) (< (mod ~last_1_var_1_17~0 65536) (+ (* ~var_1_4~0 ~last_1_var_1_1~0) 1)) (not (= (mod ~last_1_var_1_12~0 256) 0))) (= (mod ~var_1_19~0 256) (mod ~var_1_18~0 256)) (or (not (= (mod ~last_1_var_1_11~0 256) 0)) (not (= (* ~var_1_4~0 ~last_1_var_1_1~0) (mod ~last_1_var_1_17~0 65536))) (not (= (mod ~last_1_var_1_12~0 256) 0)))) (and (or (and (= (mod ~last_1_var_1_12~0 256) 0) (= (mod ~last_1_var_1_11~0 256) 0) (= (* ~var_1_4~0 ~last_1_var_1_1~0) (mod ~last_1_var_1_17~0 65536))) (and (= (mod ~last_1_var_1_12~0 256) 0) (= (mod ~last_1_var_1_11~0 256) 0) (<= (+ (* ~var_1_4~0 ~last_1_var_1_1~0) 1) (mod ~last_1_var_1_17~0 65536)))) (= (mod ~var_1_18~0 256) (mod ~var_1_16~0 256)))) (= ~var_1_11~0 0) (= (+ (div ~var_1_13~0 65536) (div ~var_1_14~0 65536) (mod ~last_1_var_1_18~0 256)) (div (+ (* (- 16776960) (div ~last_1_var_1_18~0 256)) (* ~last_1_var_1_18~0 65535) ~var_1_14~0) 65536)) (or (and (= (mod ~last_1_var_1_12~0 256) 0) (<= (+ 5 (mod ~last_1_var_1_13~0 65536)) ~var_1_4~0) (<= (+ 5 (mod ~last_1_var_1_13~0 65536)) ~var_1_5~0) (= (+ ~var_1_1~0 128) 0)) (and (= (mod ~last_1_var_1_13~0 65536) ~var_1_1~0) (or (not (= (mod ~last_1_var_1_12~0 256) 0)) (< ~var_1_5~0 (+ 5 (mod ~last_1_var_1_13~0 65536))) (< ~var_1_4~0 (+ 5 (mod ~last_1_var_1_13~0 65536)))))))";
		final String expectedResultAsString = "(let ((.cse4 (= (mod ~last_1_var_1_12~0 256) 0))) (let ((.cse12 (mod ~last_1_var_1_18~0 256)) (.cse1 (not .cse4))) (and (or (let ((.cse2 (= (mod ~var_1_9~0 256) 0)) (.cse0 (= (mod ~var_1_8~0 256) 0)) (.cse3 (mod ~var_1_6~0 256))) (and (or (not .cse0) (and .cse1 (not .cse2)) (= .cse3 0)) (or (and (or .cse4 .cse2) .cse0) (= .cse3 1)))) (< 0 (+ ~last_1_var_1_1~0 1))) (= 0 (mod ~var_1_10~0 256)) (let ((.cse11 (* ~var_1_4~0 ~last_1_var_1_1~0)) (.cse6 (mod ~last_1_var_1_17~0 65536))) (let ((.cse9 (= .cse11 .cse6)) (.cse10 (= (mod ~last_1_var_1_11~0 256) 0)) (.cse7 (+ .cse11 1)) (.cse8 (mod ~var_1_18~0 256))) (or (let ((.cse5 (not .cse10))) (and (or .cse5 (< .cse6 .cse7) .cse1) (= (mod ~var_1_19~0 256) .cse8) (or .cse5 (not .cse9) .cse1))) (and (or (and .cse4 .cse10 .cse9) (and .cse4 .cse10 (<= .cse7 .cse6))) (= .cse8 (mod ~var_1_16~0 256)))))) (= ~var_1_11~0 0) (= (mod (+ (* .cse12 65535) ~var_1_14~0) 65536) (mod ~var_1_13~0 65536)) (= (+ (div ~var_1_13~0 65536) (div ~var_1_14~0 65536) .cse12) (div (+ (* (- 16776960) (div ~last_1_var_1_18~0 256)) (* ~last_1_var_1_18~0 65535) ~var_1_14~0) 65536)) (let ((.cse14 (mod ~last_1_var_1_13~0 65536))) (let ((.cse13 (+ 5 .cse14))) (or (and .cse4 (<= .cse13 ~var_1_4~0) (<= .cse13 ~var_1_5~0) (= (+ ~var_1_1~0 128) 0)) (and (= .cse14 ~var_1_1~0) (or .cse1 (< ~var_1_5~0 .cse13) (< ~var_1_4~0 .cse13)))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_55bc03c5_23d80567_Treesizes_27_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base", "#StackAllocations"),
		};
		final String formulaAsString = "(and (exists ((|v_aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_1| Int)) (and (<= 2 (mod (select |#memory_int| |v_aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_1|) 4294967296)) (<= (+ 31 |v_aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_1|) |#StackAllocations|))) (<= (+ 31 |aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base|) |#StackAllocations|) (<= 2 (mod (select |#memory_int| |aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base|) 4294967296)))";
		final String expectedResultAsString = "(and (<= (+ 31 |aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base|) |#StackAllocations|) (<= 2 (mod (select |#memory_int| |aws_byte_cursor_read_aws_byte_cursor_advance_nospec_~cursor#1.base|) 4294967296)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_55e55541_f7f8ad8e_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_next_harness_~#node~1#1.base_BEFORE_CALL_5| Int)) (and (= |v_ULTIMATE.start_aws_linked_list_next_harness_~#node~1#1.base_BEFORE_CALL_5| (select |#memory_$Pointer$.base| (+ (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_harness_~#node~1#1.base_BEFORE_CALL_5|) 4))) (<= (+ |v_ULTIMATE.start_aws_linked_list_next_harness_~#node~1#1.base_BEFORE_CALL_5| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_harness_~#node~1#1.base_BEFORE_CALL_5|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_19| Int)) (let ((.cse0 (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_19|))) (and (<= (+ |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_19| 8) .cse0) (= |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_19| (select |#memory_$Pointer$.base| (+ .cse0 4))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_560f6157_77b3c104_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#buf~3#1.base_BEFORE_CALL_73| Int)) (and (<= (+ 24 |v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#buf~3#1.base_BEFORE_CALL_73|) |#StackAllocations|) (<= 8696 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#buf~3#1.base_BEFORE_CALL_73|)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#buf~3#1.base_BEFORE_CALL_71| Int)) (and (<= (+ 24 |v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#buf~3#1.base_BEFORE_CALL_71|) |#StackAllocations|) (<= 8696 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#buf~3#1.base_BEFORE_CALL_71|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_56df01d7_447d1dc9_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_eq_byte_buf_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_36| Int)) (<= 8687 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_36| 4)))) (<= 8687 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_harness_~#buf~3#1.base| 4))))";
		final String expectedResultAsString = "(<= 8687 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_harness_~#buf~3#1.base| 4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_575f243e_811ee60_Treesizes_11_11() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_16~0", "~var_1_17~0"),
		};
		final String formulaAsString = "(and (= (mod ~var_1_17~0 256) 0) (= (mod ~var_1_16~0 256) 0))";
		final String expectedResultAsString = "(and (<= (mod ~var_1_17~0 256) 0) (<= (mod ~var_1_16~0 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_57de5d22_bec4662e_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_22~0"),
		};
		final String formulaAsString = "(<= 1073741823 (mod (+ 4087318057 ~var_1_22~0) 4294967296))";
		final String expectedResultAsString = "(< 1073741822 (mod (+ 4087318057 ~var_1_22~0) 4294967296))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_586360f0_2c92c7ce_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_15 Int)) (and (<= 69 v_aws_linked_list_front_~list.base_BEFORE_CALL_15) (<= (+ v_aws_linked_list_front_~list.base_BEFORE_CALL_15 8) (select |#memory_$Pointer$.base| v_aws_linked_list_front_~list.base_BEFORE_CALL_15))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_23| Int)) (and (<= 69 |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_23|) (<= (+ |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_23| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_23|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5899ada_7d1d26ad_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "old(#memory_int)", "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "func_to_recursive_line_29_to_33_0_#in~n.base", "func_to_recursive_line_29_to_33_0_#in~q.base", "func_to_recursive_line_29_to_33_0_#t~mem97", "func_to_recursive_line_29_to_33_0_#t~mem96"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| |func_to_recursive_line_29_to_33_0_#in~q.base|) |func_to_recursive_line_29_to_33_0_#t~mem96|) (= |old(#memory_int)| |#memory_int|) (= (select |#memory_int| |func_to_recursive_line_29_to_33_0_#in~n.base|) |func_to_recursive_line_29_to_33_0_#t~mem97|))";
		final String expectedResultAsString = "(and (= (select |#memory_int| |func_to_recursive_line_29_to_33_0_#in~q.base|) |func_to_recursive_line_29_to_33_0_#t~mem96|) (= |old(#memory_int)| |#memory_int|) (= (select |old(#memory_int)| |func_to_recursive_line_29_to_33_0_#in~n.base|) |func_to_recursive_line_29_to_33_0_#t~mem97|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_595a0d3a_466e3144_Treesizes_12_7() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_10~0", "~var_1_18~0"),
		};
		final String formulaAsString = "(and (<= (+ ~var_1_18~0 ~var_1_10~0) 164) (<= 64 ~var_1_10~0) (<= 100 ~var_1_18~0))";
		final String expectedResultAsString = "(and (= ~var_1_18~0 100) (= 64 ~var_1_10~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_599e6599_e44a063c_Treesizes_11_5() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~m~0#1.base"),
		};
		final String formulaAsString = "(or (< (select |#memory_int| |ULTIMATE.start_main_~m~0#1.base|) 100) (= (select |#memory_int| |ULTIMATE.start_main_~m~0#1.base|) 100))";
		final String expectedResultAsString = "(<= (select |#memory_int| |ULTIMATE.start_main_~m~0#1.base|) 100)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5a002814_9593a829_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_13| Int)) (<= 67 (select |#memory_$Pointer$.base| (+ 12 |v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_13|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_55| Int)) (<= 67 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_55| 12))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5a55abe8_555a1792_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_25| Int)) (<= 8691 (select |#memory_$Pointer$.base| (+ |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_25| 4))))";
		final String expectedResultAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_20| Int)) (<= 8691 (select |#memory_$Pointer$.base| (+ |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_20| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5a8fab31_4c807239_Treesizes_9_9() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_14~0", "~var_1_13~0"),
		};
		final String formulaAsString = "(and (<= (mod ~var_1_14~0 256) 0) (= ~var_1_13~0 0))";
		final String expectedResultAsString = "(and (= (mod ~var_1_14~0 256) 0) (= ~var_1_13~0 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5b348137_ba9be829_Treesizes_73_36() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "func_to_recursive_line_29_to_41_0_~x.base", "func_to_recursive_line_29_to_41_0_~z.base", "func_to_recursive_line_29_to_41_0_~y.base", "func_to_recursive_line_29_to_41_0_~n.base"),
		};
		final String formulaAsString = "(and (<= (+ func_to_recursive_line_29_to_41_0_~x.base 8) func_to_recursive_line_29_to_41_0_~y.base) (= (select |#memory_int| func_to_recursive_line_29_to_41_0_~y.base) 1) (= (select |#memory_int| func_to_recursive_line_29_to_41_0_~n.base) 0) (<= (+ func_to_recursive_line_29_to_41_0_~n.base 8) func_to_recursive_line_29_to_41_0_~x.base) (= 6 (select |#memory_int| func_to_recursive_line_29_to_41_0_~z.base)) (= (select |#memory_int| func_to_recursive_line_29_to_41_0_~x.base) 0) (<= (+ func_to_recursive_line_29_to_41_0_~y.base 8) func_to_recursive_line_29_to_41_0_~z.base) (exists ((v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_34 Int) (v_func_to_recursive_line_29_to_41_0_~n.base_BEFORE_CALL_45 Int) (v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_31 Int) (v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_31 Int)) (and (<= (+ v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_31 8) v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_34) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_31) 6) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~n.base_BEFORE_CALL_45) 0) (<= (+ v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_34 8) v_func_to_recursive_line_29_to_41_0_~z.base_BEFORE_CALL_31) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_31) 0) (<= (+ 8 v_func_to_recursive_line_29_to_41_0_~n.base_BEFORE_CALL_45) v_func_to_recursive_line_29_to_41_0_~x.base_BEFORE_CALL_31) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_34) 1))))";
		final String expectedResultAsString = "(and (<= (+ func_to_recursive_line_29_to_41_0_~x.base 8) func_to_recursive_line_29_to_41_0_~y.base) (= (select |#memory_int| func_to_recursive_line_29_to_41_0_~y.base) 1) (= (select |#memory_int| func_to_recursive_line_29_to_41_0_~n.base) 0) (<= (+ func_to_recursive_line_29_to_41_0_~n.base 8) func_to_recursive_line_29_to_41_0_~x.base) (= 6 (select |#memory_int| func_to_recursive_line_29_to_41_0_~z.base)) (= (select |#memory_int| func_to_recursive_line_29_to_41_0_~x.base) 0) (<= (+ func_to_recursive_line_29_to_41_0_~y.base 8) func_to_recursive_line_29_to_41_0_~z.base))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5b628269_8b5ff7f4_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_9_Pointer~0.base"),
		};
		final String formulaAsString = "(= (mod (select |#memory_int| ~var_1_9_Pointer~0.base) 256) 0)";
		final String expectedResultAsString = "(<= (mod (select |#memory_int| ~var_1_9_Pointer~0.base) 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5b972260_d0fee22f_Treesizes_20_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14| Int)) (<= (mod (* (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14|) 4294967295) 4294967296) 0)) (<= (mod (* 4294967295 (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base|)) 4294967296) 0))";
		final String expectedResultAsString = "(<= (mod (* 4294967295 (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base|)) 4294967296) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5c1585e0_15b27d59_Treesizes_34_34() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#var_1_11~0.base", "~#var_1_13~0.base", "~var_1_1_Pointer~0.base", "~var_1_7_Pointer~0.base", "~#var_1_14~0.base", "~#var_1_15~0.base", "~#var_1_16~0.base", "~var_1_4_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~var_1_1_Pointer~0.base ~var_1_4_Pointer~0.base)) (not (= ~var_1_7_Pointer~0.base ~var_1_4_Pointer~0.base)) (not (= |~#var_1_15~0.base| ~var_1_4_Pointer~0.base)) (forall ((v_ArrVal_215 Int)) (<= 0 (select (store |#memory_int| |~#var_1_11~0.base| v_ArrVal_215) ~var_1_4_Pointer~0.base))) (not (= |~#var_1_13~0.base| ~var_1_4_Pointer~0.base)) (not (= |~#var_1_14~0.base| ~var_1_4_Pointer~0.base)) (not (= |~#var_1_16~0.base| ~var_1_4_Pointer~0.base)))";
		final String expectedResultAsString = "(and (<= 0 (select |#memory_int| ~var_1_4_Pointer~0.base)) (not (= ~var_1_1_Pointer~0.base ~var_1_4_Pointer~0.base)) (not (= ~var_1_7_Pointer~0.base ~var_1_4_Pointer~0.base)) (not (= |~#var_1_15~0.base| ~var_1_4_Pointer~0.base)) (not (= |~#var_1_11~0.base| ~var_1_4_Pointer~0.base)) (not (= |~#var_1_13~0.base| ~var_1_4_Pointer~0.base)) (not (= |~#var_1_14~0.base| ~var_1_4_Pointer~0.base)) (not (= |~#var_1_16~0.base| ~var_1_4_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5cda7385_16e5651_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_12| Int)) (and (<= |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_12| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_12| 12))) (<= 72 |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_12|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_15| Int)) (and (<= |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_15| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_15| 12))) (<= 72 |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_15|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5d13da16_7872c0a6_Treesizes_18_16() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~mask_SORT_1~0#1", "ULTIMATE.start_main_~var_46_arg_0~0#1", "ULTIMATE.start_main_~var_46_arg_1~0#1"),
		};
		final String formulaAsString = "(and (<= 0 (div |ULTIMATE.start_main_~var_46_arg_1~0#1| 256)) (<= (+ |ULTIMATE.start_main_~var_46_arg_1~0#1| (mod (+ |ULTIMATE.start_main_~var_46_arg_0~0#1| 3 (* 255 |ULTIMATE.start_main_~mask_SORT_1~0#1|)) 256)) 1))";
		final String expectedResultAsString = "(and (<= (+ |ULTIMATE.start_main_~var_46_arg_1~0#1| (mod (+ |ULTIMATE.start_main_~var_46_arg_0~0#1| 3 (* 255 |ULTIMATE.start_main_~mask_SORT_1~0#1|)) 256)) 1) (<= 0 |ULTIMATE.start_main_~var_46_arg_1~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5d74c494_23f6d363_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base", "~#unsigned_char_Array_0~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (forall ((v_ArrVal_271 Int)) (<= (mod (select (store |#memory_int| (+ |~#unsigned_char_Array_0~0.base| 1) v_ArrVal_271) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base) 256) 0)))";
		final String expectedResultAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (<= (mod (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base) 256) 0) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base (+ |~#unsigned_char_Array_0~0.base| 1))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5dec70e2_537fb9b7_Treesizes_38_38() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_5_Pointer~0.base", "~#var_1_13~0.base", "~#var_1_11~0.base", "~var_1_7_Pointer~0.base", "~#var_1_12~0.base", "~#var_1_9~0.base", "~#var_1_14~0.base", "~#var_1_16~0.base"),
		};
		final String formulaAsString = "(and (not (= |~#var_1_14~0.base| ~var_1_7_Pointer~0.base)) (not (= ~var_1_7_Pointer~0.base |~#var_1_13~0.base|)) (not (= |~#var_1_12~0.base| ~var_1_7_Pointer~0.base)) (not (= ~var_1_7_Pointer~0.base |~#var_1_11~0.base|)) (not (= ~var_1_7_Pointer~0.base |~#var_1_16~0.base|)) (not (= ~var_1_7_Pointer~0.base ~var_1_5_Pointer~0.base)) (forall ((v_ArrVal_108 Int)) (<= (mod (+ 255 (select (store |#memory_int| |~#var_1_9~0.base| v_ArrVal_108) ~var_1_7_Pointer~0.base)) 256) 254)))";
		final String expectedResultAsString = "(and (not (= |~#var_1_14~0.base| ~var_1_7_Pointer~0.base)) (not (= ~var_1_7_Pointer~0.base |~#var_1_13~0.base|)) (not (= |~#var_1_12~0.base| ~var_1_7_Pointer~0.base)) (not (= ~var_1_7_Pointer~0.base |~#var_1_11~0.base|)) (not (= |~#var_1_9~0.base| ~var_1_7_Pointer~0.base)) (not (= ~var_1_7_Pointer~0.base |~#var_1_16~0.base|)) (not (= ~var_1_7_Pointer~0.base ~var_1_5_Pointer~0.base)) (<= (mod (+ (select |#memory_int| ~var_1_7_Pointer~0.base) 255) 256) 254))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5e7c21b2_561b1d47_Treesizes_19_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(and (<= (mod (+ 2147483649 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 78))) 4294967296) 2147483648) (= (select |#memory_int| (+ |~#WrapperStruct00~0.base| 74)) 128))";
		final String expectedResultAsString = "(and (= (select |#memory_int| (+ |~#WrapperStruct00~0.base| 74)) 128) (<= 2147483647 (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 78)) 4294967296)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5ecc69be_ce128e9d_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_~dest#1.base_BEFORE_CALL_1| Int)) (<= 8696 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_~dest#1.base_BEFORE_CALL_1| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_harness_~#buf~3#1.base_BEFORE_CALL_6| Int)) (<= 8696 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_harness_~#buf~3#1.base_BEFORE_CALL_6| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5eeb27c8_bd259bde_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_front_~list#1.base_BEFORE_CALL_11| Int)) (and (<= |v_ULTIMATE.start_aws_linked_list_pop_front_~list#1.base_BEFORE_CALL_11| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_pop_front_~list#1.base_BEFORE_CALL_11| 12))) (<= 73 |v_ULTIMATE.start_aws_linked_list_pop_front_~list#1.base_BEFORE_CALL_11|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_front_harness_~#list~0#1.base_BEFORE_CALL_11| Int)) (and (<= 73 |v_ULTIMATE.start_aws_linked_list_pop_front_harness_~#list~0#1.base_BEFORE_CALL_11|) (<= |v_ULTIMATE.start_aws_linked_list_pop_front_harness_~#list~0#1.base_BEFORE_CALL_11| (select |#memory_$Pointer$.base| (+ 12 |v_ULTIMATE.start_aws_linked_list_pop_front_harness_~#list~0#1.base_BEFORE_CALL_11|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5f3de7ac_c989da7a_Treesizes_6_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_48~0"),
		};
		final String formulaAsString = "(not (= (mod ~var_1_48~0 256) 0))";
		final String expectedResultAsString = "(<= 1 (mod ~var_1_48~0 256))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5f6e4f69_a397e1ac_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~var_31~0#1", "ULTIMATE.start_main_~mask_SORT_1~0#1"),
		};
		final String formulaAsString = "(or (not (= (mod |ULTIMATE.start_main_~mask_SORT_1~0#1| 256) (mod |ULTIMATE.start_main_~var_31~0#1| 256))) (= (mod |ULTIMATE.start_main_~mask_SORT_1~0#1| 256) 0))";
		final String expectedResultAsString = "(let ((.cse0 (mod |ULTIMATE.start_main_~var_31~0#1| 256))) (or (not (= (mod |ULTIMATE.start_main_~mask_SORT_1~0#1| 256) .cse0)) (= .cse0 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_602fe258_b43201fc_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~WrapperStruct00_var_1_15_Pointer~0.base"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_196 Int)) (<= (mod (+ 255 (select (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_196) ~WrapperStruct00_var_1_15_Pointer~0.base)) 256) 254)) (not (= ~WrapperStruct00_var_1_3_Pointer~0.base ~WrapperStruct00_var_1_15_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~WrapperStruct00_var_1_15_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (<= (mod (+ (select |#memory_int| ~WrapperStruct00_var_1_15_Pointer~0.base) 255) 256) 254) (not (= ~WrapperStruct00_var_1_3_Pointer~0.base ~WrapperStruct00_var_1_15_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_60ec1cf7_3d0d4aff_Treesizes_77_70() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_12~0", "~var_1_11~0", "~var_1_10~0", "~last_1_var_1_11~0", "~var_1_15~0", "~var_1_5~0", "~var_1_14~0", "~var_1_13~0", "~var_1_8~0", "~var_1_7~0"),
		};
		final String formulaAsString = "(and (or (< (mod ~var_1_13~0 65536) (mod ~var_1_12~0 65536)) (= (mod (+ (* ~var_1_14~0 65535) ~last_1_var_1_11~0 (* ~var_1_15~0 65535) ~var_1_13~0) 65536) (mod ~var_1_11~0 65536))) (not (= (mod ~var_1_8~0 256) 0)) (or (= (mod (+ (* ~var_1_14~0 65535) ~last_1_var_1_11~0 (* ~var_1_15~0 65535) ~var_1_12~0) 65536) (mod ~var_1_11~0 65536)) (< (mod ~var_1_12~0 65536) (+ (mod ~var_1_13~0 65536) 1))) (<= ~var_1_5~0 ~var_1_7~0) (= (mod ~var_1_7~0 256) (mod ~var_1_5~0 256)) (<= (div ~var_1_7~0 256) (div ~var_1_5~0 256)) (= ~var_1_10~0 (mod ~var_1_5~0 256)))";
		final String expectedResultAsString = "(let ((.cse2 (* ~var_1_14~0 65535)) (.cse3 (* ~var_1_15~0 65535)) (.cse4 (mod ~var_1_11~0 65536)) (.cse1 (mod ~var_1_12~0 65536)) (.cse0 (mod ~var_1_13~0 65536))) (and (or (< .cse0 .cse1) (= (mod (+ .cse2 ~last_1_var_1_11~0 .cse3 ~var_1_13~0) 65536) .cse4)) (not (= (mod ~var_1_8~0 256) 0)) (or (= (mod (+ .cse2 ~last_1_var_1_11~0 .cse3 ~var_1_12~0) 65536) .cse4) (< .cse1 (+ .cse0 1))) (= (div ~var_1_7~0 256) (div ~var_1_5~0 256)) (= ~var_1_7~0 ~var_1_5~0) (= ~var_1_10~0 (mod ~var_1_5~0 256))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_616dffcd_c273a00b_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_be32_~cur#1.base_BEFORE_CALL_8| Int)) (and (<= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_be32_~cur#1.base_BEFORE_CALL_8|) 4294967296) 0) (<= (+ 25 |v_ULTIMATE.start_aws_byte_cursor_read_be32_~cur#1.base_BEFORE_CALL_8|) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30| Int)) (and (<= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30|) 4294967296) 0) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30| 25) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_61c2448c_7e633fbb_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_back_~list.base_BEFORE_CALL_19 Int)) (<= 67 (select |#memory_$Pointer$.base| (+ v_aws_linked_list_back_~list.base_BEFORE_CALL_19 12))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_51| Int)) (<= 67 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_51| 12))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6241d7ac_b1c642d2_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~b#1.base_BEFORE_CALL_15| Int)) (<= 8699 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~b#1.base_BEFORE_CALL_15| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~b#1.base_BEFORE_CALL_13| Int)) (<= 8699 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~b#1.base_BEFORE_CALL_13| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_62830340_51e74908_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_advance_~output#1.base_BEFORE_CALL_14| Int)) (<= 8680 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_advance_~output#1.base_BEFORE_CALL_14| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base_BEFORE_CALL_31| Int)) (<= 8680 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_advance_harness_~#buf~3#1.base_BEFORE_CALL_31| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6292a43c_455410d7_Treesizes_32_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base", "#StackAllocations", "ULTIMATE.start_aws_byte_cursor_read_common_harness_~#dest_copy~0#1.base"),
		};
		final String formulaAsString = "(and (<= 4 (mod (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base|) 4294967296)) (exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30| Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30| 25) |#StackAllocations|) (<= 4 (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30|) 4294967296)))) (<= (+ 21 |ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base|) |ULTIMATE.start_aws_byte_cursor_read_common_harness_~#dest_copy~0#1.base|) (<= (+ 25 |ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base|) |#StackAllocations|))";
		final String expectedResultAsString = "(and (<= 4 (mod (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base|) 4294967296)) (<= (+ 21 |ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base|) |ULTIMATE.start_aws_byte_cursor_read_common_harness_~#dest_copy~0#1.base|) (<= (+ 25 |ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base|) |#StackAllocations|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_62f78474_f17a752b_Treesizes_26_12() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_10~0", "~var_1_15~0", "~var_1_14~0", "~var_1_13~0", "~var_1_3~0"),
		};
		final String formulaAsString = "(and (= ~var_1_13~0 ~var_1_10~0) (= ~var_1_15~0 ~var_1_14~0) (<= 0 (div ~var_1_15~0 65536)) (= ~var_1_15~0 (mod ~var_1_3~0 256)) (<= (+ (mod ~var_1_14~0 65536) ~var_1_15~0) (+ ~var_1_14~0 65535)))";
		final String expectedResultAsString = "(and (= ~var_1_13~0 ~var_1_10~0) (= ~var_1_15~0 ~var_1_14~0) (= ~var_1_15~0 (mod ~var_1_3~0 256)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_636800_8165f98c_Treesizes_7_3() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1"),
		};
		final String formulaAsString = "(or (< |ULTIMATE.start_main_~i~0#1| 99999) (= 99999 |ULTIMATE.start_main_~i~0#1|))";
		final String expectedResultAsString = "(<= |ULTIMATE.start_main_~i~0#1| 99999)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_640b4752_2dfa8513_Treesizes_21_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base", "ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base"),
		};
		final String formulaAsString = "(and (<= 58 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base| 4))) (<= (+ 8 |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base|) |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base|) (exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_23| Int)) (<= 58 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_23|)))))";
		final String expectedResultAsString = "(and (<= 58 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base| 4))) (<= (+ 8 |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base|) |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_647ced26_a2caa344_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_41~0"),
		};
		final String formulaAsString = "(<= (mod ~var_1_41~0 256) 0)";
		final String expectedResultAsString = "(= (mod ~var_1_41~0 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_650870f7_55026537_Treesizes_37_35() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0", "~var_1_33~0", "~last_1_var_1_10~0", "~var_1_18~0"),
		};
		final String formulaAsString = "(and (<= 0 (div ~last_1_var_1_10~0 65536)) (<= 0 (div ~var_1_1~0 4294967296)) (<= (+ 2147417948 ~var_1_1~0 ~last_1_var_1_10~0 ~var_1_18~0) (+ (mod ~var_1_33~0 4294967296) (mod ~last_1_var_1_10~0 65536))) (<= (div (+ (* 4294967295 ~var_1_18~0) ~var_1_33~0) 4294967296) (+ (div ~var_1_33~0 4294967296) ~var_1_18~0)))";
		final String expectedResultAsString = "(and (<= 0 (div ~last_1_var_1_10~0 65536)) (<= 0 ~var_1_1~0) (<= (+ 2147417948 ~var_1_1~0 ~last_1_var_1_10~0 ~var_1_18~0) (+ (mod ~var_1_33~0 4294967296) (mod ~last_1_var_1_10~0 65536))) (<= (div (+ (* 4294967295 ~var_1_18~0) ~var_1_33~0) 4294967296) (+ (div ~var_1_33~0 4294967296) ~var_1_18~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_65ea53d2_ed3b3c41_Treesizes_10_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_priority_queue_is_valid_aws_priority_queue_backpointers_valid_~queue#1.base"),
		};
		final String formulaAsString = "(not (= (mod (select |#memory_int| (+ |aws_priority_queue_is_valid_aws_priority_queue_backpointers_valid_~queue#1.base| 28)) 4294967296) 0))";
		final String expectedResultAsString = "(<= 1 (mod (select |#memory_int| (+ |aws_priority_queue_is_valid_aws_priority_queue_backpointers_valid_~queue#1.base| 28)) 4294967296))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_666107e3_f192ee18_Treesizes_44_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_11_Pointer~0.base", "~WrapperStruct00_var_1_6_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~WrapperStruct00_var_1_11_Pointer~0.base ~WrapperStruct00_var_1_6_Pointer~0.base)) (<= (+ (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base) (mod (select |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base) 256)) (+ 255 (select |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base))) (not (= ~WrapperStruct00_var_1_11_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (<= (select |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base) (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base)) (<= (mod (+ (* 255 (select |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base)) (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base)) 256) 0))";
		final String expectedResultAsString = "(and (not (= ~WrapperStruct00_var_1_11_Pointer~0.base ~WrapperStruct00_var_1_6_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_11_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (= (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base) (select |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_66edc334_f679ee54_Treesizes_24_19() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~last_1_var_1_59~0", "~last_1_var_1_87~0", "~var_1_14~0"),
		};
		final String formulaAsString = "(and (<= (div ~last_1_var_1_59~0 65536) 0) (<= (+ (mod ~var_1_14~0 256) ~last_1_var_1_59~0) 355) (<= (div ~last_1_var_1_87~0 4294967296) 0) (<= 100 ~last_1_var_1_59~0) (<= 64 ~last_1_var_1_87~0))";
		final String expectedResultAsString = "(and (<= (+ (mod ~var_1_14~0 256) ~last_1_var_1_59~0) 355) (<= (div ~last_1_var_1_87~0 4294967296) 0) (<= 100 ~last_1_var_1_59~0) (<= 64 ~last_1_var_1_87~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6770be8a_4ae11815_Treesizes_11_11() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_46~0", "~var_1_48~0"),
		};
		final String formulaAsString = "(and (= (mod ~var_1_46~0 256) 0) (= (mod ~var_1_48~0 256) 0))";
		final String expectedResultAsString = "(and (<= (mod ~var_1_46~0 256) 0) (<= (mod ~var_1_48~0 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_67ab2b01_666f2b04_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_byte_cursor_compare_lexical_~lhs#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_23| Int)) (<= 58 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_23|)))) (<= 58 (select |#memory_$Pointer$.base| (+ |aws_byte_cursor_compare_lexical_~lhs#1.base| 4))))";
		final String expectedResultAsString = "(<= 58 (select |#memory_$Pointer$.base| (+ |aws_byte_cursor_compare_lexical_~lhs#1.base| 4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_67c1c950_67e074a4_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_3| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_3| 8)) 0)) (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base| 8)) 0))";
		final String expectedResultAsString = "(= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base| 8)) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6835dba6_7c621e9d_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_25| Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_25| 8) |#StackAllocations|) (<= 47 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_25| 4)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_24| Int)) (and (<= 47 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_24| 4))) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_24| 8) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_69193fd_ecdfefd1_Treesizes_10_9() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~a~0#1", "ULTIMATE.start_main_#t~ret7#1", "ULTIMATE.start_main_~b~0#1"),
		};
		final String formulaAsString = "(<= (mod (+ |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_main_~b~0#1| (* |ULTIMATE.start_main_#t~ret7#1| 4294967295)) 4294967296) 0)";
		final String expectedResultAsString = "(= (mod (+ |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_main_~b~0#1|) 4294967296) (mod |ULTIMATE.start_main_#t~ret7#1| 4294967296))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_69bfe348_9bdd17a9_Treesizes_25_15() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(<= (+ (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5)) 65536) (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5)) 65535) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 7))) 65536)) 65535)";
		final String expectedResultAsString = "(<= (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5)) 65536) (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 7)) 65536))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6a08a8e1_d0677eff_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_13| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_13| 4)) 0)) (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base| 4)) 0))";
		final String expectedResultAsString = "(= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base| 4)) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6a8dc1f0_7b590b56_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_trim_pred_~source#1.base_BEFORE_CALL_15| Int)) (<= 8685 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_trim_pred_~source#1.base_BEFORE_CALL_15| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_18| Int)) (<= 8685 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_18| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6b231a07_f17de067_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_append_harness_~#from~0#1.base"),
		};
		final String formulaAsString = "(and (exists ((|ULTIMATE.start_aws_byte_buf_append_harness_~#from_old~0#1.base| Int)) (= (select |#memory_int| |ULTIMATE.start_aws_byte_buf_append_harness_~#from_old~0#1.base|) (select |#memory_int| |ULTIMATE.start_aws_byte_buf_append_harness_~#from~0#1.base|))) (<= (mod (select |#memory_int| |ULTIMATE.start_aws_byte_buf_append_harness_~#from~0#1.base|) 4294967296) 0))";
		final String expectedResultAsString = "(<= (mod (select |#memory_int| |ULTIMATE.start_aws_byte_buf_append_harness_~#from~0#1.base|) 4294967296) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6c527868_8fd5665d_Treesizes_14_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~data_init~0#1", "ULTIMATE.start_sll_circular_create_~head~0#1.base", "ULTIMATE.start_sll_circular_create_~last~0#1.base"),
		};
		final String formulaAsString = "(and (not (= (+ |ULTIMATE.start_sll_circular_create_~head~0#1.base| 4) |ULTIMATE.start_sll_circular_create_~last~0#1.base|)) (= (select |#memory_int| (+ |ULTIMATE.start_sll_circular_create_~head~0#1.base| 4)) |ULTIMATE.start_main_~data_init~0#1|))";
		final String expectedResultAsString = "(forall ((v_ArrVal_72 Int)) (= |ULTIMATE.start_main_~data_init~0#1| (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~last~0#1.base| v_ArrVal_72) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.base| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6dac1ded_a0d7d583_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_pop_front_~list#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_pop_front_harness_~#list~0#1.base_BEFORE_CALL_15| Int)) (= (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_linked_list_pop_front_harness_~#list~0#1.base_BEFORE_CALL_15|)) 0)) (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_pop_front_~list#1.base| 4)) 0))";
		final String expectedResultAsString = "(= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_pop_front_~list#1.base| 4)) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6e37dff4_32657113_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_hash_byte_cursor_ptr_ignore_case_harness_~#cur~3#1.base_BEFORE_CALL_11| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_hash_byte_cursor_ptr_ignore_case_harness_~#cur~3#1.base_BEFORE_CALL_11| 4)) 0))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_hash_byte_cursor_ptr_ignore_case_harness_~#cur~3#1.base_BEFORE_CALL_10| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_hash_byte_cursor_ptr_ignore_case_harness_~#cur~3#1.base_BEFORE_CALL_10| 4)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6ebf06ae_2a41bcce_Treesizes_13_11() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~var_44_arg_1~0#1"),
		};
		final String formulaAsString = "(and (<= (+ (div |ULTIMATE.start_main_~var_44_arg_1~0#1| 256) 1) 0) (<= 0 (+ |ULTIMATE.start_main_~var_44_arg_1~0#1| 2)))";
		final String expectedResultAsString = "(and (<= (+ |ULTIMATE.start_main_~var_44_arg_1~0#1| 1) 0) (<= 0 (+ |ULTIMATE.start_main_~var_44_arg_1~0#1| 2)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6efd4dac_828571b2_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_31| Int)) (<= 8837 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_31|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_26| Int)) (<= 8837 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_26|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6fbc0ef3_cb0767e8_Treesizes_14_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_my_drv_disconnect_~#status~0#1.base", "ULTIMATE.start_main_~#data~1#1.base"),
		};
		final String formulaAsString = "(and (not (= (+ |ULTIMATE.start_main_~#data~1#1.base| 28) |ULTIMATE.start_my_drv_disconnect_~#status~0#1.base|)) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#data~1#1.base| 28)) 2))";
		final String expectedResultAsString = "(forall ((v_ArrVal_469 Int)) (= 2 (select (store |#memory_int| |ULTIMATE.start_my_drv_disconnect_~#status~0#1.base| v_ArrVal_469) (+ |ULTIMATE.start_main_~#data~1#1.base| 28))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6fe5b48c_a139d6ca_Treesizes_17_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#Ultimate.C_memset_#t~loopctr1366", "#Ultimate.C_memset_#ptr.base"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_518 Int)) (= (select (store |#memory_$Pointer$.base| (+ |#Ultimate.C_memset_#t~loopctr1366| |#Ultimate.C_memset_#ptr.base|) v_ArrVal_518) (+ 4 |#Ultimate.C_memset_#ptr.base|)) 0)) (<= 4 |#Ultimate.C_memset_#t~loopctr1366|))";
		final String expectedResultAsString = "(and (= (select |#memory_$Pointer$.base| (+ 4 |#Ultimate.C_memset_#ptr.base|)) 0) (<= 5 |#Ultimate.C_memset_#t~loopctr1366|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_70bf48ae_cb0767e8_Treesizes_14_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_my_drv_disconnect_~#status~0#1.base", "ULTIMATE.start_main_~#data~1#1.base"),
		};
		final String formulaAsString = "(and (not (= (+ |ULTIMATE.start_main_~#data~1#1.base| 28) |ULTIMATE.start_my_drv_disconnect_~#status~0#1.base|)) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#data~1#1.base| 28)) 2))";
		final String expectedResultAsString = "(forall ((v_ArrVal_808 Int)) (= (select (store |#memory_int| |ULTIMATE.start_my_drv_disconnect_~#status~0#1.base| v_ArrVal_808) (+ |ULTIMATE.start_main_~#data~1#1.base| 28)) 2))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_70da7472_2d5877f9_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_19| Int)) (and (<= |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_19| (select |#memory_$Pointer$.base| (+ 12 |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_19|))) (<= 67 |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_19|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_18| Int)) (and (<= 67 |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_18|) (<= |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_18| (select |#memory_$Pointer$.base| (+ 12 |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_18|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_71441af9_f780e844_Treesizes_79_46() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~num~0#1", "ULTIMATE.start_main_~#array~0#1.base", "~ARR_SIZE~0", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| Int)) (and (= (select |#memory_int| (+ (* ~ARR_SIZE~0 4) |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| 4)) 0) (= (select |#memory_int| (+ |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| 4)) 0) (= (select |#memory_int| (+ (* ~ARR_SIZE~0 4) |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1|)) 0) (= (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1|) 0))) (<= |ULTIMATE.start_main_~sum~0#1| 0) (= (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| (* ~ARR_SIZE~0 4) 4)) 0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| (* ~ARR_SIZE~0 4))) 0) (= (+ |ULTIMATE.start_main_~num~0#1| 1) 0) (<= 2 ~ARR_SIZE~0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 4)) 0) (<= ~ARR_SIZE~0 32767))";
		final String expectedResultAsString = "(let ((.cse0 (* ~ARR_SIZE~0 4))) (and (<= |ULTIMATE.start_main_~sum~0#1| 0) (= (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| .cse0 4)) 0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| .cse0)) 0) (= (+ |ULTIMATE.start_main_~num~0#1| 1) 0) (<= 2 ~ARR_SIZE~0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 4)) 0) (<= ~ARR_SIZE~0 32767)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7214297c_2da34149_Treesizes_32_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations", "ULTIMATE.start_save_byte_from_array_~storage#1.base", "ULTIMATE.start_aws_byte_buf_write_be64_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_buf_write_be64_harness_~#buf~3#1.base_BEFORE_CALL_39| Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_buf_write_be64_harness_~#buf~3#1.base_BEFORE_CALL_39| 37) |#StackAllocations|) (<= 8683 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_write_be64_harness_~#buf~3#1.base_BEFORE_CALL_39| 4))))) (<= 8683 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_write_be64_harness_~#buf~3#1.base| 4))) (<= (+ |ULTIMATE.start_aws_byte_buf_write_be64_harness_~#buf~3#1.base| 37) |#StackAllocations|) (<= |#StackAllocations| (+ |ULTIMATE.start_save_byte_from_array_~storage#1.base| 5)))";
		final String expectedResultAsString = "(and (<= 8683 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_write_be64_harness_~#buf~3#1.base| 4))) (<= (+ |ULTIMATE.start_aws_byte_buf_write_be64_harness_~#buf~3#1.base| 37) |#StackAllocations|) (<= |#StackAllocations| (+ |ULTIMATE.start_save_byte_from_array_~storage#1.base| 5)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_729069da_4db19255_Treesizes_17_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_from_c_str_~#cur~1#1.base"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_aws_byte_cursor_from_c_str_harness_~#cur~3#1.base| Int)) (or (not (= (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_from_c_str_harness_~#cur~3#1.base|) (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_from_c_str_~#cur~1#1.base|))) (< (mod (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_from_c_str_harness_~#cur~3#1.base|) 4294967296) 1)))";
		final String expectedResultAsString = "(<= (mod (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_from_c_str_~#cur~1#1.base|) 4294967296) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_72feb8bf_db502eda_Treesizes_27_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_read_~cur#1.base", "#StackAllocations"),
		};
		final String formulaAsString = "(and (<= (+ 29 |ULTIMATE.start_aws_byte_cursor_read_~cur#1.base|) |#StackAllocations|) (<= 50 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_read_~cur#1.base| 4))) (exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_16| Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_16| 29) |#StackAllocations|) (<= 50 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_16| 4))))))";
		final String expectedResultAsString = "(and (<= (+ 29 |ULTIMATE.start_aws_byte_cursor_read_~cur#1.base|) |#StackAllocations|) (<= 50 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_read_~cur#1.base| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_735338d_612a3e9f_Treesizes_22_20() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~var_30_arg_0~0#1", "ULTIMATE.start_main_~var_27~0#1", "ULTIMATE.start_main_~var_30_arg_1~0#1"),
		};
		final String formulaAsString = "(and (<= (mod (+ |ULTIMATE.start_main_~var_27~0#1| 2) 256) 1) (<= 0 (div |ULTIMATE.start_main_~var_30_arg_1~0#1| 256)) (<= |ULTIMATE.start_main_~var_30_arg_1~0#1| 1) (<= 0 |ULTIMATE.start_main_~var_30_arg_0~0#1|) (<= |ULTIMATE.start_main_~var_30_arg_0~0#1| 1))";
		final String expectedResultAsString = "(and (<= (mod (+ |ULTIMATE.start_main_~var_27~0#1| 2) 256) 1) (<= 0 |ULTIMATE.start_main_~var_30_arg_1~0#1|) (<= |ULTIMATE.start_main_~var_30_arg_1~0#1| 1) (<= 0 |ULTIMATE.start_main_~var_30_arg_0~0#1|) (<= |ULTIMATE.start_main_~var_30_arg_0~0#1| 1))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_73d284f8_3f75a38a_Treesizes_43_29() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0", "~var_1_4~0", "~var_1_5~0", "~var_1_3~0", "~last_1_var_1_6~0"),
		};
		final String formulaAsString = "(and (or (and (<= (+ ~var_1_3~0 1) 0) (<= 0 (+ ~var_1_3~0 ~last_1_var_1_6~0))) (not (= (mod ~var_1_4~0 256) 0)) (and (<= 0 ~var_1_3~0) (<= ~var_1_3~0 ~last_1_var_1_6~0))) (<= ~var_1_5~0 ~var_1_1~0) (<= (mod ~var_1_1~0 4294967296) (mod ~var_1_5~0 4294967296)) (<= ~var_1_1~0 (+ (mod ~var_1_1~0 4294967296) ~var_1_5~0)))";
		final String expectedResultAsString = "(and (or (and (<= (+ ~var_1_3~0 1) 0) (<= 0 (+ ~var_1_3~0 ~last_1_var_1_6~0))) (not (= (mod ~var_1_4~0 256) 0)) (and (<= 0 ~var_1_3~0) (<= ~var_1_3~0 ~last_1_var_1_6~0))) (= ~var_1_1~0 ~var_1_5~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7488afb0_5a505c17_Treesizes_32_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~res3~0", "thread2Thread1of1ForFork1_#t~mem7#1", "thread2Thread1of1ForFork1_~i~1#1", "~a3~0.base", "~a1~0.base", "thread2Thread1of1ForFork1_#t~mem8#1"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| ~a1~0.base) |thread2Thread1of1ForFork1_#t~mem7#1|) (= (select |#memory_int| ~a3~0.base) |thread2Thread1of1ForFork1_#t~mem8#1|) (= |thread2Thread1of1ForFork1_~i~1#1| 0) (exists ((~a2~0.base Int)) (and (= (+ ~res3~0 (select |#memory_int| ~a3~0.base)) (select |#memory_int| ~a2~0.base)) (= (select |#memory_int| ~a1~0.base) (select |#memory_int| ~a2~0.base)))))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| ~a1~0.base))) (and (= .cse0 (+ ~res3~0 |thread2Thread1of1ForFork1_#t~mem8#1|)) (= .cse0 |thread2Thread1of1ForFork1_#t~mem7#1|) (= (select |#memory_int| ~a3~0.base) |thread2Thread1of1ForFork1_#t~mem8#1|) (= |thread2Thread1of1ForFork1_~i~1#1| 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_74dcc8bb_190c8280_Treesizes_120_108() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#BOOL_unsigned_char_Array_0~0.base", "ULTIMATE.start_step_#t~mem21#1", "~#unsigned_short_int_Array_0~0.base", "~#signed_char_Array_0~0.base"),
		};
		final String formulaAsString = "(and (not (= (+ |~#BOOL_unsigned_char_Array_0~0.base| 3) |~#unsigned_short_int_Array_0~0.base|)) (or (and (= (+ 256 (select |#memory_int| 52)) (mod (+ 206 (select |#memory_int| 50) (select |#memory_int| 51)) 256)) (<= (mod (+ 78 (select |#memory_int| 50) (select |#memory_int| 51)) 256) 127) (not (= |~#BOOL_unsigned_char_Array_0~0.base| 50))) (and (<= (+ (select |#memory_int| 50) (select |#memory_int| 51)) 177) (not (= |~#BOOL_unsigned_char_Array_0~0.base| 50)) (<= (+ (* (div |ULTIMATE.start_step_#t~mem21#1| 65536) 256) 1) (div (+ |ULTIMATE.start_step_#t~mem21#1| 206 (select |#memory_int| 50) (* (- 1) (mod |ULTIMATE.start_step_#t~mem21#1| 65536)) (select |#memory_int| 51)) 256)) (= (+ (select |#memory_int| 52) 50) (+ (select |#memory_int| 50) (select |#memory_int| 51))))) (not (= 49 |~#BOOL_unsigned_char_Array_0~0.base|)) (= |~#signed_char_Array_0~0.base| 50) (not (= (+ |~#BOOL_unsigned_char_Array_0~0.base| 1) |~#unsigned_short_int_Array_0~0.base|)) (not (= |~#BOOL_unsigned_char_Array_0~0.base| 47)) (not (= |~#BOOL_unsigned_char_Array_0~0.base| 48)) (= (select |#memory_int| (+ |~#BOOL_unsigned_char_Array_0~0.base| 3)) 1))";
		final String expectedResultAsString = "(let ((.cse6 (+ |~#BOOL_unsigned_char_Array_0~0.base| 3))) (and (let ((.cse2 (select |#memory_int| 50)) (.cse3 (select |#memory_int| 51))) (let ((.cse4 (not (= |~#BOOL_unsigned_char_Array_0~0.base| 50))) (.cse1 (+ 206 .cse2 .cse3)) (.cse0 (select |#memory_int| 52))) (or (and (= (+ 256 .cse0) (mod .cse1 256)) (<= (mod (+ 78 .cse2 .cse3) 256) 127) .cse4) (let ((.cse5 (+ .cse2 .cse3))) (and (<= .cse5 177) .cse4 (<= 1 (div .cse1 256)) (= (+ .cse0 50) .cse5)))))) (not (= .cse6 |~#unsigned_short_int_Array_0~0.base|)) (not (= 49 |~#BOOL_unsigned_char_Array_0~0.base|)) (= |~#signed_char_Array_0~0.base| 50) (not (= (+ |~#BOOL_unsigned_char_Array_0~0.base| 1) |~#unsigned_short_int_Array_0~0.base|)) (not (= |~#BOOL_unsigned_char_Array_0~0.base| 47)) (not (= |~#BOOL_unsigned_char_Array_0~0.base| 48)) (= (select |#memory_int| .cse6) 1)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_75475b5e_8730e8d3_Treesizes_20_15() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_52~0", "~var_1_43~0", "~var_1_44~0"),
		};
		final String formulaAsString = "(and (<= 0 ~var_1_52~0) (not (= (mod ~var_1_44~0 65536) 0)) (not (= (mod ~var_1_43~0 256) 0)) (not (= ~var_1_52~0 0)))";
		final String expectedResultAsString = "(and (not (= (mod ~var_1_43~0 256) 0)) (<= 1 (mod ~var_1_44~0 65536)) (<= 1 ~var_1_52~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_75a5a5a2_435e9580_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~3#1.base_BEFORE_CALL_50| Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~3#1.base_BEFORE_CALL_50| 8) |#StackAllocations|) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~3#1.base_BEFORE_CALL_50| 4)) 0)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~3#1.base_BEFORE_CALL_47| Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~3#1.base_BEFORE_CALL_47| 8) |#StackAllocations|) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~3#1.base_BEFORE_CALL_47| 4)) 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_75f54be8_73dc20df_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_rbegin_~list#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_32| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_32| 8)) 0)) (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_rbegin_~list#1.base| 8)) 0))";
		final String expectedResultAsString = "(= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_rbegin_~list#1.base| 8)) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_76b9b6c4_180ce9b8_Treesizes_215_188() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_12~0", "~var_1_11~0", "~var_1_10~0", "~var_1_20~0", "~var_1_16~0", "~var_1_4~0", "~var_1_5~0", "~var_1_15~0", "~var_1_2~0", "~var_1_14~0", "~var_1_3~0", "~var_1_8~0", "~var_1_19~0", "~var_1_9~0", "~var_1_18~0", "~var_1_6~0", "~var_1_17~0", "~var_1_1~0", "~last_1_var_1_20~0"),
		};
		final String formulaAsString = "(and (= (mod ~var_1_17~0 65536) ~var_1_20~0) (not (= (mod ~var_1_4~0 4294967296) ~var_1_12~0)) (<= (mod ~var_1_8~0 65536) ~var_1_20~0) (or (< (mod ~var_1_19~0 65536) (+ 32 ~last_1_var_1_20~0 (mod ~var_1_16~0 256))) (= (mod ~var_1_17~0 65536) (mod ~var_1_9~0 65536))) (= ~var_1_5~0 (mod ~var_1_9~0 65536)) (not (= (mod ~var_1_6~0 256) 0)) (or (< (mod ~var_1_19~0 65536) (+ (div (+ (* (div ~var_1_8~0 65536) (- 65536)) ~var_1_8~0) ~var_1_11~0) 32 (mod ~var_1_16~0 256))) (= (mod ~var_1_17~0 65536) (mod ~var_1_9~0 65536))) (or (< (mod ~var_1_19~0 65536) (+ (div (+ (* (div ~var_1_8~0 65536) (- 65536)) ~var_1_8~0) ~var_1_11~0) ~var_1_18~0 (mod ~var_1_16~0 256))) (= (mod ~var_1_17~0 65536) (mod ~var_1_9~0 65536))) (or (= (mod ~var_1_17~0 65536) (mod ~var_1_9~0 65536)) (< 64 (+ ~var_1_2~0 ~var_1_18~0 (mod ~var_1_16~0 256)))) (or (and (<= (+ ~var_1_4~0 ~var_1_3~0 ~var_1_2~0) 8) (or (and (= (mod (+ ~var_1_4~0 ~var_1_3~0 ~var_1_2~0) 256) ~var_1_1~0) (<= (mod (+ ~var_1_4~0 ~var_1_3~0 ~var_1_2~0) 256) 127)) (and (= (+ 256 ~var_1_1~0) (mod (+ ~var_1_4~0 ~var_1_3~0 ~var_1_2~0) 256)) (<= 128 (mod (+ ~var_1_4~0 ~var_1_3~0 ~var_1_2~0) 256))))) (and (<= 9 (+ ~var_1_4~0 ~var_1_3~0 ~var_1_2~0)) (= ~var_1_1~0 8))) (or (= (mod (+ 60 ~var_1_16~0) 256) (mod ~var_1_14~0 256)) (= (mod ~var_1_15~0 256) 0)) (<= ~var_1_10~0 (mod ~var_1_9~0 65536)) (= ~var_1_10~0 ~var_1_20~0) (or (< (mod ~var_1_19~0 65536) (+ ~last_1_var_1_20~0 ~var_1_18~0 (mod ~var_1_16~0 256))) (= (mod ~var_1_17~0 65536) (mod ~var_1_9~0 65536))) (= ~var_1_12~0 (mod ~var_1_8~0 65536)))";
		final String expectedResultAsString = "(let ((.cse0 (mod ~var_1_17~0 65536)) (.cse2 (mod ~var_1_9~0 65536)) (.cse1 (mod ~var_1_8~0 65536))) (and (= .cse0 ~var_1_20~0) (not (= (mod ~var_1_4~0 4294967296) ~var_1_12~0)) (<= .cse1 ~var_1_20~0) (= ~var_1_5~0 .cse2) (or (= .cse0 .cse2) (let ((.cse3 (mod ~var_1_19~0 65536))) (let ((.cse5 (+ .cse3 1)) (.cse6 (div (+ (* (div ~var_1_8~0 65536) (- 65536)) ~var_1_8~0) ~var_1_11~0)) (.cse4 (mod ~var_1_16~0 256))) (and (<= .cse3 (+ 31 ~last_1_var_1_20~0 .cse4)) (<= .cse5 (+ ~last_1_var_1_20~0 ~var_1_18~0 .cse4)) (<= .cse5 (+ .cse6 ~var_1_18~0 .cse4)) (<= .cse3 (+ .cse6 31 .cse4)) (<= 65 (+ ~var_1_2~0 ~var_1_18~0 .cse4)))))) (not (= (mod ~var_1_6~0 256) 0)) (let ((.cse7 (+ ~var_1_4~0 ~var_1_3~0 ~var_1_2~0))) (or (and (<= .cse7 8) (let ((.cse8 (mod .cse7 256))) (or (and (= .cse8 ~var_1_1~0) (<= .cse8 127)) (and (= (+ 256 ~var_1_1~0) .cse8) (<= 128 .cse8))))) (and (<= 9 .cse7) (= ~var_1_1~0 8)))) (or (= (mod (+ 60 ~var_1_16~0) 256) (mod ~var_1_14~0 256)) (= (mod ~var_1_15~0 256) 0)) (<= ~var_1_10~0 .cse2) (= ~var_1_10~0 ~var_1_20~0) (= ~var_1_12~0 .cse1)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_773c0ad6_a2ca4a29_Treesizes_26_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_2_Pointer~0.base", "~var_1_1_Pointer~0.base", "~var_1_7_Pointer~0.base", "~#var_1_14~0.base", "~#var_1_15~0.base", "~#var_1_16~0.base"),
		};
		final String formulaAsString = "(and (not (= ~var_1_2_Pointer~0.base |~#var_1_15~0.base|)) (not (= ~var_1_2_Pointer~0.base ~var_1_7_Pointer~0.base)) (forall ((v_ArrVal_158 Int)) (<= 0 (select (store |#memory_int| |~#var_1_14~0.base| v_ArrVal_158) ~var_1_2_Pointer~0.base))) (not (= ~var_1_2_Pointer~0.base ~var_1_1_Pointer~0.base)) (not (= ~var_1_2_Pointer~0.base |~#var_1_16~0.base|)))";
		final String expectedResultAsString = "(and (not (= ~var_1_2_Pointer~0.base |~#var_1_15~0.base|)) (not (= |~#var_1_14~0.base| ~var_1_2_Pointer~0.base)) (not (= ~var_1_2_Pointer~0.base ~var_1_7_Pointer~0.base)) (<= 0 (select |#memory_int| ~var_1_2_Pointer~0.base)) (not (= ~var_1_2_Pointer~0.base ~var_1_1_Pointer~0.base)) (not (= ~var_1_2_Pointer~0.base |~#var_1_16~0.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_77678d89_c28c5419_Treesizes_51_5() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#volArray~0#1.base", "ULTIMATE.start_main_~MINVAL~0#1"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_75 Int) (v_ArrVal_72 Int) (v_ArrVal_73 Int) (v_ArrVal_74 Int)) (or (< v_ArrVal_74 (select |#memory_int| (+ (- 20) (* |ULTIMATE.start_main_~i~0#1| 20) |ULTIMATE.start_main_~#volArray~0#1.base|))) (< |ULTIMATE.start_main_~MINVAL~0#1| (+ (select (store (store (store (store |#memory_int| (+ (- 20) (* |ULTIMATE.start_main_~i~0#1| 20) |ULTIMATE.start_main_~#volArray~0#1.base|) v_ArrVal_74) (+ (* |ULTIMATE.start_main_~i~0#1| 20) (- 16) |ULTIMATE.start_main_~#volArray~0#1.base|) v_ArrVal_75) (+ (* |ULTIMATE.start_main_~i~0#1| 20) |ULTIMATE.start_main_~#volArray~0#1.base| (- 12)) v_ArrVal_72) (+ (* |ULTIMATE.start_main_~i~0#1| 20) |ULTIMATE.start_main_~#volArray~0#1.base| (- 8)) v_ArrVal_73) |ULTIMATE.start_main_~#volArray~0#1.base|) 1))))";
		final String expectedResultAsString = "(<= |ULTIMATE.start_main_~MINVAL~0#1| (select |#memory_int| |ULTIMATE.start_main_~#volArray~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7797d56_1f7b5c99_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base", "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var3_Pointer~0.base", "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_139 Int)) (<= (mod (select (store |#memory_int| ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var3_Pointer~0.base v_ArrVal_139) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base) 256) 0)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var3_Pointer~0.base)) (<= (mod (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base) 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_786b6615_668dff21_Treesizes_19_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_~src#1.base_BEFORE_CALL_31| Int)) (not (= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_init_copy_~src#1.base_BEFORE_CALL_31|) 4294967296) 0))) (exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_67| Int)) (not (= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_67|) 4294967296) 0))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_67| Int)) (not (= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_67|) 4294967296) 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_793f975c_8159ec91_Treesizes_393_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#signed_short_int_Array_0~0.base", "~#unsigned_short_int_Array_0~0.base"),
		};
		final String formulaAsString = "(and (or (and (forall ((v_ArrVal_174 Int)) (<= 32768 (mod (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (+ (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) (- 65536))) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 4)) 65536))) (forall ((v_ArrVal_174 Int)) (or (= (mod (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (+ (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) (- 65536))) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) (+ 65536 (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (+ (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) (- 65536))) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 10)))) (< (mod (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (+ (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) (- 65536))) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) 32768))) (forall ((v_ArrVal_174 Int)) (or (= (mod (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (+ (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) (- 65536))) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (+ (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) (- 65536))) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 10))) (= (mod (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (+ (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) (- 65536))) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) (+ 65536 (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (+ (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) (- 65536))) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 10))))))) (< (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) 32768)) (or (< 32767 (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)) (and (forall ((v_ArrVal_174 Int)) (or (= (+ 65536 (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 10))) (mod (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)) (= (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 10)) (mod (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)))) (forall ((v_ArrVal_174 Int)) (or (< 32767 (mod (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)) (= (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 10)) (mod (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)))) (forall ((v_ArrVal_174 Int)) (<= (mod (select (store (store |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 10) (mod (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)) 65536)) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_174) (+ |~#signed_short_int_Array_0~0.base| 4)) 65536) 32767)))))";
		final String expectedResultAsString = "(and (not (= (+ |~#signed_short_int_Array_0~0.base| 4) |~#unsigned_short_int_Array_0~0.base|)) (not (= (+ |~#signed_short_int_Array_0~0.base| 10) |~#unsigned_short_int_Array_0~0.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_798481c7_3092e4a1_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_from_c_str_harness_~#cur~3#1.base"),
		};
		final String formulaAsString = "(= (mod (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_from_c_str_harness_~#cur~3#1.base|) 4294967296) 0)";
		final String expectedResultAsString = "(<= (mod (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_from_c_str_harness_~#cur~3#1.base|) 4294967296) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_79fbbe25_7ce71ce3_Treesizes_14_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base", "~#unsigned_char_Array_0~0.base"),
		};
		final String formulaAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ 2 |~#unsigned_char_Array_0~0.base|))) (<= (mod (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base) 256) 0))";
		final String expectedResultAsString = "(forall ((v_ArrVal_668 Int)) (<= (mod (select (store |#memory_int| (+ 2 |~#unsigned_char_Array_0~0.base|) v_ArrVal_668) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base) 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7a86211b_67c7fa8a_Treesizes_9_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base"),
		};
		final String formulaAsString = "(<= (mod (+ 255 (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base)) 256) 254)";
		final String expectedResultAsString = "(not (= (mod (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base) 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7b1d40e_21c2de04_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_15| Int)) (<= 8688 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_15|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_46| Int)) (<= 8688 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_46| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7b857e07_54d97a36_Treesizes_18_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~a~0#1.base", "ULTIMATE.start_main_~p~0#1.base"),
		};
		final String formulaAsString = "(and (not (= (+ |ULTIMATE.start_main_~a~0#1.base| 4) |ULTIMATE.start_main_~p~0#1.base|)) (not (= |ULTIMATE.start_main_~a~0#1.base| |ULTIMATE.start_main_~p~0#1.base|)) (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_main_~a~0#1.base| 4)) |ULTIMATE.start_main_~p~0#1.base|))";
		final String expectedResultAsString = "(forall ((v_ArrVal_58 Int) (v_ArrVal_56 Int)) (= (select (store (store |#memory_$Pointer$.base| |ULTIMATE.start_main_~p~0#1.base| v_ArrVal_56) (+ 4 |ULTIMATE.start_main_~p~0#1.base|) v_ArrVal_58) (+ |ULTIMATE.start_main_~a~0#1.base| 4)) |ULTIMATE.start_main_~p~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7c4f6134_db2b8668_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base", "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_558 Int)) (<= (mod (+ 255 (select (store |#memory_int| ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base v_ArrVal_558) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)) 256) 254)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)) (<= (mod (+ (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base) 255) 256) 254) (not (= ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7d100023_799d35fd_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_buf_write_~buf.base_BEFORE_CALL_8 Int)) (<= 8678 (select |#memory_$Pointer$.base| (+ 4 v_aws_byte_buf_write_~buf.base_BEFORE_CALL_8))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base_BEFORE_CALL_44| Int)) (<= 8678 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base_BEFORE_CALL_44| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7e1b260c_7d079687_Treesizes_155_89() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#signed_short_int_Array_0~0.base", "ULTIMATE.start_property_#t~mem81#1"),
		};
		final String formulaAsString = "(and (or (and (<= 32768 (mod (+ (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 2)) (* 65535 (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)))) 65536)) (= (+ 65536 (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 6))) (mod (+ (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 2)) (* 65535 (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)))) 65536))) (and (= (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 6)) (mod (+ (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 2)) (* 65535 (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)))) 65536)) (<= (mod (+ (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 2)) (* 65535 (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)))) 65536) 32767))) (or (and (= |ULTIMATE.start_property_#t~mem81#1| (mod (+ (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 2)) (* 65535 (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)))) 65536)) (<= (mod (+ (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 2)) (* 65535 (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)))) 65536) 32767)) (and (= (+ 65536 |ULTIMATE.start_property_#t~mem81#1|) (mod (+ (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 2)) (* 65535 (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)))) 65536)) (<= 32768 (mod (+ (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 2)) (* 65535 (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)))) 65536)))))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 6)))) (and (= .cse0 |ULTIMATE.start_property_#t~mem81#1|) (let ((.cse1 (mod (+ (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 2)) (* 65535 (select |#memory_int| (+ |~#signed_short_int_Array_0~0.base| 4)))) 65536))) (or (and (<= 32768 .cse1) (= (+ 65536 .cse0) .cse1)) (and (= .cse0 .cse1) (<= .cse1 32767))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7e85d977_8434fd33_Treesizes_30_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_ensure_array_list_has_allocated_data_member_~list#1.base", "#StackAllocations", "ULTIMATE.start_aws_array_list_clear_harness_~#list~0#1.base"),
		};
		final String formulaAsString = "(and (<= |ULTIMATE.start_ensure_array_list_has_allocated_data_member_~list#1.base| |ULTIMATE.start_aws_array_list_clear_harness_~#list~0#1.base|) (exists ((|v_ULTIMATE.start_aws_array_list_clear_harness_~#list~0#1.base_BEFORE_CALL_13| Int)) (and (<= (+ |v_ULTIMATE.start_aws_array_list_clear_harness_~#list~0#1.base_BEFORE_CALL_13| 20) |#StackAllocations|) (= (select |#memory_$Pointer$.base| (+ 16 |v_ULTIMATE.start_aws_array_list_clear_harness_~#list~0#1.base_BEFORE_CALL_13|)) 0))) (= (select |#memory_$Pointer$.base| (+ 16 |ULTIMATE.start_aws_array_list_clear_harness_~#list~0#1.base|)) 0) (<= (+ |ULTIMATE.start_aws_array_list_clear_harness_~#list~0#1.base| 20) |#StackAllocations|))";
		final String expectedResultAsString = "(and (<= |ULTIMATE.start_ensure_array_list_has_allocated_data_member_~list#1.base| |ULTIMATE.start_aws_array_list_clear_harness_~#list~0#1.base|) (= (select |#memory_$Pointer$.base| (+ 16 |ULTIMATE.start_aws_array_list_clear_harness_~#list~0#1.base|)) 0) (<= (+ |ULTIMATE.start_aws_array_list_clear_harness_~#list~0#1.base| 20) |#StackAllocations|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7f3679d2_80d6a7b1_Treesizes_6_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ldv_xmalloc_~res~6.base"),
		};
		final String formulaAsString = "(not (= (mod ldv_xmalloc_~res~6.base 4294967296) 0))";
		final String expectedResultAsString = "(<= 1 (mod ldv_xmalloc_~res~6.base 4294967296))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7f8f5e5d_2c7bf9d6_Treesizes_33_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "func_to_recursive_line_29_to_41_0_~n.base", "func_to_recursive_line_29_to_41_0_~y.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| func_to_recursive_line_29_to_41_0_~n.base) 1) (exists ((v_func_to_recursive_line_29_to_41_0_~n.base_BEFORE_CALL_18 Int) (v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_27 Int)) (and (<= (+ 16 v_func_to_recursive_line_29_to_41_0_~n.base_BEFORE_CALL_18) v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_27) (= (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~n.base_BEFORE_CALL_18) 1) (= 7 (select |#memory_int| v_func_to_recursive_line_29_to_41_0_~y.base_BEFORE_CALL_27)))) (<= (+ func_to_recursive_line_29_to_41_0_~n.base 16) func_to_recursive_line_29_to_41_0_~y.base) (= 7 (select |#memory_int| func_to_recursive_line_29_to_41_0_~y.base)))";
		final String expectedResultAsString = "(and (= (select |#memory_int| func_to_recursive_line_29_to_41_0_~n.base) 1) (<= (+ func_to_recursive_line_29_to_41_0_~n.base 16) func_to_recursive_line_29_to_41_0_~y.base) (= 7 (select |#memory_int| func_to_recursive_line_29_to_41_0_~y.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_80811a50_8895097c_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base| 4)) 0) (exists ((|v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_19| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_19| 4)) 0)))";
		final String expectedResultAsString = "(= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base| 4)) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_809a7983_b062ece3_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_with_lookup_~from#1.base_BEFORE_CALL_3| Int)) (<= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_append_with_lookup_~from#1.base_BEFORE_CALL_3|) 4294967296) 0))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_with_lookup_harness_~#from~0#1.base_BEFORE_CALL_10| Int)) (<= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_append_with_lookup_harness_~#from~0#1.base_BEFORE_CALL_10|) 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_80f1a1f4_9516b0cc_Treesizes_23_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base"),
		};
		final String formulaAsString = "(and (<= 69 |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|) (<= |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base| (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base| 12))) (exists ((|v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_14| Int)) (and (<= |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_14| (select |#memory_$Pointer$.base| (+ 12 |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_14|))) (<= 69 |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_14|))))";
		final String expectedResultAsString = "(and (<= 69 |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|) (<= |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base| (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base| 12))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_816dd1a1_5ef69ba0_Treesizes_7_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "memset_impl_#in~n"),
		};
		final String formulaAsString = "(<= (mod (* |memset_impl_#in~n| 4294967295) 4294967296) 0)";
		final String expectedResultAsString = "(<= (mod |memset_impl_#in~n| 4294967296) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_81d3b3c3_535bfd88_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_6 Int)) (<= (mod (select |#memory_int| v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_6) 4294967296) 0))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base_BEFORE_CALL_18| Int)) (<= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base_BEFORE_CALL_18|) 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_81f4ad73_def8035e_Treesizes_27_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations", "aws_byte_cursor_read_~cur#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30| Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30| 25) |#StackAllocations|) (<= 4 (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30|) 4294967296)))) (<= (+ |aws_byte_cursor_read_~cur#1.base| 25) |#StackAllocations|) (<= 4 (mod (select |#memory_int| |aws_byte_cursor_read_~cur#1.base|) 4294967296)))";
		final String expectedResultAsString = "(and (<= (+ |aws_byte_cursor_read_~cur#1.base| 25) |#StackAllocations|) (<= 4 (mod (select |#memory_int| |aws_byte_cursor_read_~cur#1.base|) 4294967296)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_827e4433_6b8e0076_Treesizes_30_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "check_~a.base", "check_~x"),
		};
		final String formulaAsString = "(and (<= (select |#memory_int| check_~a.base) 0) (= check_~x 0) (<= 0 (select |#memory_int| (+ check_~a.base 8))) (exists ((v_check_~a.base_BEFORE_CALL_9 Int)) (and (<= 0 (select |#memory_int| (+ 8 v_check_~a.base_BEFORE_CALL_9))) (<= (select |#memory_int| v_check_~a.base_BEFORE_CALL_9) 0))))";
		final String expectedResultAsString = "(and (<= (select |#memory_int| check_~a.base) 0) (= check_~x 0) (<= 0 (select |#memory_int| (+ check_~a.base 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_82cf9404_6d8a4c24_Treesizes_28_28() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base", "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3| Int) (|v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_5| Int)) (and (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_5|) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3| 4)) 0) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3| 8) |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_5|) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_5| 4)) 0)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2| Int) (|v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| Int)) (and (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| 4)) 0) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2| 8) |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4|) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2|) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4|)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2| 4)) 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_837e0699_b10f39d5_Treesizes_74_40() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_16_Pointer~0.base", "~WrapperStruct00_var_1_17_Pointer~0.base", "~WrapperStruct00_var_1_6_Pointer~0.base", "~WrapperStruct00_var_1_19_Pointer~0.base", "~WrapperStruct00_var_1_7_Pointer~0.base"),
		};
		final String formulaAsString = "(and (<= (+ (mod (+ (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base) (* 4294967295 (select |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base))) 4294967296) (mod (select |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base) 4294967296)) 4294967295) (<= (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base) (select |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_6_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_17_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_6_Pointer~0.base ~WrapperStruct00_var_1_16_Pointer~0.base)) (<= (+ (mod (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base) 4294967296) (select |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base)) (+ (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base) 4294967295)) (not (= ~WrapperStruct00_var_1_19_Pointer~0.base ~WrapperStruct00_var_1_6_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_6_Pointer~0.base ~WrapperStruct00_var_1_17_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_16_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_19_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_6_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_17_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (= (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base) (select |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_6_Pointer~0.base ~WrapperStruct00_var_1_16_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_19_Pointer~0.base ~WrapperStruct00_var_1_6_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_6_Pointer~0.base ~WrapperStruct00_var_1_17_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_16_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_19_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_83c2ed68_93d43bcc_Treesizes_10_7() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "thread3Thread1of1ForFork0_~i~2", "thread2Thread1of1ForFork1_~i~1"),
		};
		final String formulaAsString = "(and (<= thread3Thread1of1ForFork0_~i~2 thread2Thread1of1ForFork1_~i~1) (<= thread2Thread1of1ForFork1_~i~1 0) (<= 0 thread3Thread1of1ForFork0_~i~2))";
		final String expectedResultAsString = "(and (= thread2Thread1of1ForFork1_~i~1 0) (= thread3Thread1of1ForFork0_~i~2 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8435773_c0ebc5e3_Treesizes_387_381() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0", "~var_1_10~0", "~var_1_4~0", "~var_1_5~0", "~var_1_8~0", "~var_1_9~0", "~var_1_6~0", "~var_1_7~0"),
		};
		final String formulaAsString = "(and (not (= (mod ~var_1_8~0 256) 0)) (or (and (<= (mod ~var_1_5~0 256) 0) (or (and (<= (+ (div ~var_1_5~0 256) ~var_1_6~0 (div ~var_1_4~0 256)) (+ (div (+ ~var_1_4~0 ~var_1_5~0 (* 255 ~var_1_6~0)) 256) (div ~var_1_6~0 256))) (<= (mod ~var_1_4~0 256) 1)) (and (<= (+ (div ~var_1_5~0 256) ~var_1_6~0) (+ (div (+ ~var_1_5~0 1 (* 255 ~var_1_6~0)) 256) (div ~var_1_6~0 256))) (<= 2 (mod ~var_1_4~0 256))))) (< (div ~var_1_1~0 256) 0)) (or (< (+ (mod ~var_1_4~0 256) (mod ~var_1_5~0 256)) (+ ~var_1_1~0 (mod ~var_1_6~0 256) 1)) (and (or (< (+ (div (+ ~var_1_4~0 ~var_1_5~0 (* 255 ~var_1_6~0)) 256) (div ~var_1_6~0 256)) (+ (div ~var_1_5~0 256) ~var_1_6~0 (div ~var_1_4~0 256))) (< 1 (mod ~var_1_4~0 256))) (or (< (mod ~var_1_4~0 256) 2) (< (+ (div (+ ~var_1_5~0 1 (* 255 ~var_1_6~0)) 256) (div ~var_1_6~0 256)) (+ (div ~var_1_5~0 256) ~var_1_6~0)))) (< (mod ~var_1_5~0 256) (+ ~var_1_1~0 (mod ~var_1_6~0 256)))) (or (and (<= (mod (+ ~var_1_5~0 1 (* 255 ~var_1_6~0)) 256) (mod ~var_1_1~0 256)) (<= 2 (mod ~var_1_4~0 256))) (and (<= (mod (+ ~var_1_4~0 ~var_1_5~0 (* 255 ~var_1_6~0)) 256) (mod ~var_1_1~0 256)) (<= (mod ~var_1_4~0 256) 1))) (or (< (mod ~var_1_1~0 256) (+ (mod (+ ~var_1_4~0 ~var_1_5~0 (* 255 ~var_1_6~0)) 256) 1)) (< 1 (mod ~var_1_4~0 256))) (or (and (<= (mod (+ ~var_1_9~0 ~var_1_6~0) 256) 127) (or (and (<= (mod (+ 5 ~var_1_6~0) 256) 127) (or (and (= ~var_1_7~0 (mod (+ 5 ~var_1_6~0) 256)) (<= 6 ~var_1_9~0)) (and (= ~var_1_7~0 (mod (+ ~var_1_9~0 ~var_1_6~0) 256)) (<= ~var_1_9~0 5)))) (and (<= 128 (mod (+ 5 ~var_1_6~0) 256)) (or (and (= (+ 256 ~var_1_7~0) (mod (+ 5 ~var_1_6~0) 256)) (<= 6 ~var_1_9~0)) (and (= ~var_1_7~0 (mod (+ ~var_1_9~0 ~var_1_6~0) 256)) (<= ~var_1_9~0 5)))))) (and (or (and (or (and (= ~var_1_7~0 (mod (+ 5 ~var_1_6~0) 256)) (<= 6 ~var_1_9~0)) (and (= (+ 256 ~var_1_7~0) (mod (+ ~var_1_9~0 ~var_1_6~0) 256)) (<= ~var_1_9~0 5))) (<= (mod (+ 5 ~var_1_6~0) 256) 127)) (and (<= 128 (mod (+ 5 ~var_1_6~0) 256)) (or (and (= (+ 256 ~var_1_7~0) (mod (+ 5 ~var_1_6~0) 256)) (<= 6 ~var_1_9~0)) (and (= (+ 256 ~var_1_7~0) (mod (+ ~var_1_9~0 ~var_1_6~0) 256)) (<= ~var_1_9~0 5))))) (<= 128 (mod (+ ~var_1_9~0 ~var_1_6~0) 256)))) (<= (mod ~var_1_5~0 256) (mod ~var_1_4~0 256)) (= (mod ~var_1_4~0 256) ~var_1_10~0) (or (< (mod ~var_1_4~0 256) 2) (< (mod ~var_1_1~0 256) (+ (mod (+ ~var_1_5~0 1 (* 255 ~var_1_6~0)) 256) 1))))";
		final String expectedResultAsString = "(let ((.cse28 (* 255 ~var_1_6~0))) (let ((.cse0 (mod ~var_1_4~0 256)) (.cse24 (+ ~var_1_5~0 1 .cse28)) (.cse25 (+ ~var_1_4~0 ~var_1_5~0 .cse28)) (.cse26 (div ~var_1_6~0 256)) (.cse27 (div ~var_1_5~0 256))) (let ((.cse4 (+ .cse27 ~var_1_6~0 (div ~var_1_4~0 256))) (.cse3 (+ (div .cse25 256) .cse26)) (.cse8 (+ .cse27 ~var_1_6~0)) (.cse7 (+ (div .cse24 256) .cse26)) (.cse10 (<= 2 .cse0)) (.cse9 (<= .cse0 1)) (.cse12 (mod .cse25 256)) (.cse5 (< 1 .cse0)) (.cse2 (mod ~var_1_5~0 256)) (.cse6 (< .cse0 2)) (.cse1 (mod ~var_1_1~0 256)) (.cse11 (mod .cse24 256))) (and (not (= (mod ~var_1_8~0 256) 0)) (or (< (+ .cse0 .cse1 .cse2) (+ 256 ~var_1_1~0 (mod ~var_1_6~0 256))) (and (or (< .cse3 .cse4) .cse5) (or .cse6 (< .cse7 .cse8)))) (or (and (<= .cse2 0) (or (and (<= .cse4 .cse3) .cse9) (and (<= .cse8 .cse7) .cse10))) (< (div ~var_1_1~0 256) 0)) (or (and (<= .cse11 .cse1) .cse10) (and (<= .cse12 .cse1) .cse9)) (or (< .cse1 (+ .cse12 1)) .cse5) (let ((.cse21 (+ 256 ~var_1_7~0)) (.cse22 (mod (+ 5 ~var_1_6~0) 256)) (.cse23 (<= 6 ~var_1_9~0))) (let ((.cse15 (and (= ~var_1_7~0 .cse22) .cse23)) (.cse14 (<= .cse22 127)) (.cse17 (<= 128 .cse22)) (.cse18 (and (= .cse21 .cse22) .cse23)) (.cse19 (<= ~var_1_9~0 5)) (.cse13 (mod (+ ~var_1_9~0 ~var_1_6~0) 256))) (or (and (<= .cse13 127) (let ((.cse16 (and (= ~var_1_7~0 .cse13) .cse19))) (or (and .cse14 (or .cse15 .cse16)) (and .cse17 (or .cse18 .cse16))))) (and (let ((.cse20 (and (= .cse21 .cse13) .cse19))) (or (and (or .cse15 .cse20) .cse14) (and .cse17 (or .cse18 .cse20)))) (<= 128 .cse13))))) (<= .cse2 .cse0) (= .cse0 ~var_1_10~0) (or .cse6 (< .cse1 (+ .cse11 1)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_85c57001_77e7a7f2_Treesizes_24_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_byte_buf_secure_zero_~buf#1.base"),
		};
		final String formulaAsString = "(and (<= (mod (+ 4294967295 (select |#memory_int| (+ |aws_byte_buf_secure_zero_~buf#1.base| 8))) 4294967296) 4294967294) (exists ((|v_ULTIMATE.start_aws_byte_buf_reset_harness_~#buf~3#1.base_BEFORE_CALL_30| Int)) (<= (mod (+ (select |#memory_int| (+ |v_ULTIMATE.start_aws_byte_buf_reset_harness_~#buf~3#1.base_BEFORE_CALL_30| 8)) 4294967295) 4294967296) 4294967294)))";
		final String expectedResultAsString = "(<= (mod (+ 4294967295 (select |#memory_int| (+ |aws_byte_buf_secure_zero_~buf#1.base| 8))) 4294967296) 4294967294)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_86478230_2dffa02e_Treesizes_71_43() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~num~0#1", "ULTIMATE.start_main_~#array~0#1.base", "~ARR_SIZE~0", "ULTIMATE.start_main_~index1~0#1", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(and (<= 0 (+ |ULTIMATE.start_main_~index1~0#1| 32768)) (= |ULTIMATE.start_main_~sum~0#1| 0) (= (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) (exists ((|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| Int)) (and (= (select |#memory_int| (+ |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| 8)) 0) (= (select |#memory_int| (+ |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| 4)) 0) (= (select |#memory_int| (+ |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| 12)) 0) (= (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1|) 0))) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 12)) 0) (= 2 ~ARR_SIZE~0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 8)) 0) (= (+ |ULTIMATE.start_main_~num~0#1| 1) 0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 4)) 0))";
		final String expectedResultAsString = "(and (<= 0 (+ |ULTIMATE.start_main_~index1~0#1| 32768)) (= |ULTIMATE.start_main_~sum~0#1| 0) (= (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 12)) 0) (= 2 ~ARR_SIZE~0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 8)) 0) (= (+ |ULTIMATE.start_main_~num~0#1| 1) 0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 4)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_86fcd2c7_b2c99a68_Treesizes_29_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations", "ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (not (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_harness_~#buf~3#1.base| 4)) 0)) (exists ((|v_ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_harness_~#buf~3#1.base_BEFORE_CALL_22| Int)) (and (not (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_harness_~#buf~3#1.base_BEFORE_CALL_22| 4)) 0)) (<= (+ 16 |v_ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_harness_~#buf~3#1.base_BEFORE_CALL_22|) |#StackAllocations|))) (<= (+ |ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_harness_~#buf~3#1.base| 16) |#StackAllocations|))";
		final String expectedResultAsString = "(and (not (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_harness_~#buf~3#1.base| 4)) 0)) (<= (+ |ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_harness_~#buf~3#1.base| 16) |#StackAllocations|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_877902fa_4d082cae_Treesizes_14_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_choose_next_~q#1.base", "ULTIMATE.start_choose_next_~node~0#1.base"),
		};
		final String formulaAsString = "(and (not (= |ULTIMATE.start_choose_next_~q#1.base| (+ 8 |ULTIMATE.start_choose_next_~node~0#1.base|))) (= (select |#memory_$Pointer$.base| (+ 8 |ULTIMATE.start_choose_next_~node~0#1.base|)) 0))";
		final String expectedResultAsString = "(forall ((v_ArrVal_248 Int)) (= (select (store |#memory_$Pointer$.base| |ULTIMATE.start_choose_next_~q#1.base| v_ArrVal_248) (+ 8 |ULTIMATE.start_choose_next_~node~0#1.base|)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_881c2d91_513cc1df_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_~src#1.base_BEFORE_CALL_19| Int)) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_~src#1.base_BEFORE_CALL_19| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_53| Int)) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_53| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_88d367d9_99aec485_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_step_#t~bitwise4#1"),
		};
		final String formulaAsString = "(<= (mod |ULTIMATE.start_step_#t~bitwise4#1| 4294967296) 0)";
		final String expectedResultAsString = "(= (mod |ULTIMATE.start_step_#t~bitwise4#1| 4294967296) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_895a27d4_c2138cd_Treesizes_14_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#vectorx~0#1.base", "ULTIMATE.start_main_~element~0#1"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_1244 Int)) (not (= (select (store |#memory_int| (+ (* |ULTIMATE.start_main_~i~0#1| 4) |ULTIMATE.start_main_~#vectorx~0#1.base|) v_ArrVal_1244) |ULTIMATE.start_main_~#vectorx~0#1.base|) |ULTIMATE.start_main_~element~0#1|)))";
		final String expectedResultAsString = "(and (not (= |ULTIMATE.start_main_~i~0#1| 0)) (not (= |ULTIMATE.start_main_~element~0#1| (select |#memory_int| |ULTIMATE.start_main_~#vectorx~0#1.base|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_89fb7b25_438c4cd5_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_25~0"),
		};
		final String formulaAsString = "(<= (mod ~var_1_25~0 256) 0)";
		final String expectedResultAsString = "(= (mod ~var_1_25~0 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8acd6607_9af36fa6_Treesizes_41_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~maxb~0", "thread3Thread1of1ForFork2_~i~2", "~maxc~0", "~maxa~0", "~C~0.base"),
		};
		final String formulaAsString = "(and (or (< (select |#memory_int| (+ ~C~0.base (* thread3Thread1of1ForFork2_~i~2 4))) (+ ~maxb~0 ~maxa~0 1)) (< (select |#memory_int| (+ ~C~0.base (* thread3Thread1of1ForFork2_~i~2 4))) ~maxc~0)) (or (< ~maxc~0 (+ (select |#memory_int| (+ ~C~0.base (* thread3Thread1of1ForFork2_~i~2 4))) 1)) (< ~maxc~0 (+ ~maxb~0 ~maxa~0 1))))";
		final String expectedResultAsString = "(let ((.cse0 (+ ~maxb~0 ~maxa~0))) (and (<= ~maxc~0 .cse0) (<= (select |#memory_int| (+ ~C~0.base (* thread3Thread1of1ForFork2_~i~2 4))) .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8b2b9780_8060b56b_Treesizes_11_3() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~j~0#1"),
		};
		final String formulaAsString = "(and (<= 0 (div (+ (- 2) |ULTIMATE.start_main_~j~0#1|) 4294967296)) (<= |ULTIMATE.start_main_~j~0#1| 2))";
		final String expectedResultAsString = "(= 2 |ULTIMATE.start_main_~j~0#1|)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8bef7741_6e8872b5_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_~dest#1.base_BEFORE_CALL_8| Int)) (<= 8696 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_~dest#1.base_BEFORE_CALL_8| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_~dest#1.base_BEFORE_CALL_7| Int)) (<= 8696 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_and_fill_buffer_~dest#1.base_BEFORE_CALL_7| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8c80cf8a_9ad9f4ba_Treesizes_13_9() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~An~0", "~Bn~0", "~i_AB~0"),
		};
		final String formulaAsString = "(and (<= (+ ~i_AB~0 1) ~An~0) (not (= ~i_AB~0 ~An~0)) (<= ~Bn~0 ~i_AB~0))";
		final String expectedResultAsString = "(and (<= (+ ~i_AB~0 1) ~An~0) (<= ~Bn~0 ~i_AB~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8d330645_e709f998_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~3#1.base_BEFORE_CALL_56| Int)) (and (<= 8698 |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~3#1.base_BEFORE_CALL_56|) (= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~3#1.base_BEFORE_CALL_56|) 4294967296) 0)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~3#1.base_BEFORE_CALL_53| Int)) (and (<= 8698 |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~3#1.base_BEFORE_CALL_53|) (= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~3#1.base_BEFORE_CALL_53|) 4294967296) 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8ddf0be9_b6e6d2f6_Treesizes_30_25() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(and (<= (mod |ULTIMATE.start_main_~n~0#1| 4294967296) (+ |ULTIMATE.start_main_~y~0#1| 1)) (<= |ULTIMATE.start_main_~y~0#1| 3) (<= (+ (mod (+ 4294967292 |ULTIMATE.start_main_~n~0#1|) 4294967296) 4) (+ (mod |ULTIMATE.start_main_~n~0#1| 4294967296) (mod (+ 2 (* 4294967295 |ULTIMATE.start_main_~y~0#1|)) 4294967296))))";
		final String expectedResultAsString = "(let ((.cse0 (mod |ULTIMATE.start_main_~n~0#1| 4294967296))) (and (<= (+ (mod (+ 4294967295 |ULTIMATE.start_main_~n~0#1| (* 4294967295 |ULTIMATE.start_main_~y~0#1|)) 4294967296) 4) .cse0) (<= .cse0 (+ |ULTIMATE.start_main_~y~0#1| 1)) (<= |ULTIMATE.start_main_~y~0#1| 3)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8ea989e5_1babdbab_Treesizes_18_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#unsigned_long_int_Array_0~0.base", "~#unsigned_short_int_Array_0~0.base"),
		};
		final String formulaAsString = "(and (not (= (+ 2 |~#unsigned_long_int_Array_0~0.base|) |~#unsigned_short_int_Array_0~0.base|)) (<= (mod (+ (select |#memory_int| (+ 2 |~#unsigned_short_int_Array_0~0.base|)) 65535) 65536) 65534))";
		final String expectedResultAsString = "(forall ((v_ArrVal_190 Int)) (<= (mod (+ (select (store |#memory_int| (+ |~#unsigned_long_int_Array_0~0.base| 4) v_ArrVal_190) (+ 2 |~#unsigned_short_int_Array_0~0.base|)) 65535) 65536) 65534))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8f272016_4ee83797_Treesizes_26_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~num~0#1", "ULTIMATE.start_main_~#array~0#1.base", "~ARR_SIZE~0", "ULTIMATE.start_main_~index1~0#1", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(and (= ~ARR_SIZE~0 1) (= |ULTIMATE.start_main_~sum~0#1| 0) (= (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) (<= |ULTIMATE.start_main_~index1~0#1| 32767) (= (+ |ULTIMATE.start_main_~num~0#1| 1) 0) (exists ((|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| Int)) (= (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1|) 0)))";
		final String expectedResultAsString = "(and (= ~ARR_SIZE~0 1) (= |ULTIMATE.start_main_~sum~0#1| 0) (= (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) (<= |ULTIMATE.start_main_~index1~0#1| 32767) (= (+ |ULTIMATE.start_main_~num~0#1| 1) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8f71c6cf_15323a97_Treesizes_9_7() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~var_15_arg_0~0#1"),
		};
		final String formulaAsString = "(and (<= |ULTIMATE.start_main_~var_15_arg_0~0#1| 255) (<= 0 (div |ULTIMATE.start_main_~var_15_arg_0~0#1| 256)))";
		final String expectedResultAsString = "(and (<= 0 |ULTIMATE.start_main_~var_15_arg_0~0#1|) (<= |ULTIMATE.start_main_~var_15_arg_0~0#1| 255))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8fd35f77_6c21f1d6_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "max_#in~n.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_$Pointer$.base| (+ |max_#in~n.base| 4)) 0) (exists ((|v_max_#in~n.base_BEFORE_CALL_6| Int)) (= (select |#memory_$Pointer$.base| (+ |v_max_#in~n.base_BEFORE_CALL_6| 4)) 0)))";
		final String expectedResultAsString = "(= (select |#memory_$Pointer$.base| (+ |max_#in~n.base| 4)) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_900fb760_5e0b94af_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base_BEFORE_CALL_13| Int)) (and (<= 52 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base_BEFORE_CALL_13| 4))) (<= (+ 23 |v_ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base_BEFORE_CALL_13|) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~0#1.base_BEFORE_CALL_50| Int)) (and (<= 52 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~0#1.base_BEFORE_CALL_50| 4))) (<= (+ 23 |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~0#1.base_BEFORE_CALL_50|) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_90a31de2_2311ec51_Treesizes_39_39() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~#y~0#1.base_BEFORE_CALL_16| Int) (|v_ULTIMATE.start_main_~#z~0#1.base_BEFORE_CALL_16| Int) (|v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_11| Int)) (and (= (select |#memory_int| |v_ULTIMATE.start_main_~#z~0#1.base_BEFORE_CALL_16|) 6) (= (select |#memory_int| |v_ULTIMATE.start_main_~#y~0#1.base_BEFORE_CALL_16|) 1) (<= (+ |v_ULTIMATE.start_main_~#y~0#1.base_BEFORE_CALL_16| 8) |v_ULTIMATE.start_main_~#z~0#1.base_BEFORE_CALL_16|) (= (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_11|) 0) (<= (+ |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_11| 8) |v_ULTIMATE.start_main_~#y~0#1.base_BEFORE_CALL_16|) (exists ((|ULTIMATE.start_main_~#n~0#1.base| Int)) (and (<= (+ |ULTIMATE.start_main_~#n~0#1.base| 8) |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_11|) (= (select |#memory_int| |ULTIMATE.start_main_~#n~0#1.base|) 0)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_main_~#y~0#1.base_BEFORE_CALL_15| Int) (|v_ULTIMATE.start_main_~#z~0#1.base_BEFORE_CALL_15| Int) (|v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_10| Int)) (and (= (select |#memory_int| |v_ULTIMATE.start_main_~#y~0#1.base_BEFORE_CALL_15|) 1) (= (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_10|) 0) (<= (+ |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_10| 8) |v_ULTIMATE.start_main_~#y~0#1.base_BEFORE_CALL_15|) (exists ((|ULTIMATE.start_main_~#n~0#1.base| Int)) (and (<= (+ |ULTIMATE.start_main_~#n~0#1.base| 8) |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_10|) (= (select |#memory_int| |ULTIMATE.start_main_~#n~0#1.base|) 0))) (<= (+ |v_ULTIMATE.start_main_~#y~0#1.base_BEFORE_CALL_15| 8) |v_ULTIMATE.start_main_~#z~0#1.base_BEFORE_CALL_15|) (= 6 (select |#memory_int| |v_ULTIMATE.start_main_~#z~0#1.base_BEFORE_CALL_15|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_90e0786f_c3e973d9_Treesizes_30_18() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "mult_~m", "mult_~n", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (<= (+ (* 5 |mult_#in~n|) (* 2 |mult_#in~m|)) (+ (* 2 mult_~m) (* 5 mult_~n))) (= |mult_#in~n| mult_~n) (<= (+ (* 2 mult_~m) |mult_#in~n|) (+ (* 2 |mult_#in~m|) mult_~n)))";
		final String expectedResultAsString = "(and (<= |mult_#in~n| mult_~n) (= |mult_#in~m| mult_~m) (<= (+ (* 3 mult_~m) mult_~n) (+ (* 3 |mult_#in~m|) |mult_#in~n|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_91164c1f_675979f1_Treesizes_91_71() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(and (<= (mod (+ (* 65535 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 4))) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 6)) 65535) 16) 65536) 32767) (= (mod (+ (* 65535 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 4))) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 6)) 65535) 16) 65536) (select |#memory_int| |~#WrapperStruct00~0.base|)) (<= (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) 1) (mod (+ (* 65535 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 4))) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 6)) 65535) 16) 65536)) (<= 0 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2))))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)))) (let ((.cse2 (mod (+ (* 65535 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 4))) .cse0 (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 6)) 65535) 16) 65536)) (.cse1 (select |#memory_int| |~#WrapperStruct00~0.base|))) (and (<= (+ .cse0 1) .cse1) (<= .cse2 32767) (= .cse2 .cse1) (<= 0 .cse0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_916f7c70_44248920_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_19| Int)) (and (<= 70 |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_19|) (<= |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_19| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_19| 12)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_18| Int)) (and (<= 70 |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_18|) (<= |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_18| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_18| 12)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_91d17af5_4638c57_Treesizes_77_50() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#BOOL_unsigned_char_Array_0~0.base", "~#unsigned_long_int_Array_0~0.base", "~#double_Array_0~0.base", "~last_1_unsigned_long_int_Array_0_1__0_~0"),
		};
		final String formulaAsString = "(and (not (= |~#BOOL_unsigned_char_Array_0~0.base| (+ 7 |~#unsigned_long_int_Array_0~0.base|))) (not (= |~#double_Array_0~0.base| |~#unsigned_long_int_Array_0~0.base|)) (or (and (<= (mod ~last_1_unsigned_long_int_Array_0_1__0_~0 4294967296) 24) (<= 25 (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|)))) (and (<= ~last_1_unsigned_long_int_Array_0_1__0_~0 (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|))) (<= 25 (mod ~last_1_unsigned_long_int_Array_0_1__0_~0 4294967296)))) (not (= |~#BOOL_unsigned_char_Array_0~0.base| (+ |~#unsigned_long_int_Array_0~0.base| 11))) (or (and (<= 25 (mod ~last_1_unsigned_long_int_Array_0_1__0_~0 4294967296)) (<= (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|)) ~last_1_unsigned_long_int_Array_0_1__0_~0)) (and (<= (mod ~last_1_unsigned_long_int_Array_0_1__0_~0 4294967296) 24) (<= (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|)) 25))) (not (= |~#double_Array_0~0.base| (+ |~#unsigned_long_int_Array_0~0.base| 4))))";
		final String expectedResultAsString = "(and (not (= |~#BOOL_unsigned_char_Array_0~0.base| (+ 7 |~#unsigned_long_int_Array_0~0.base|))) (not (= |~#double_Array_0~0.base| |~#unsigned_long_int_Array_0~0.base|)) (not (= |~#BOOL_unsigned_char_Array_0~0.base| (+ |~#unsigned_long_int_Array_0~0.base| 11))) (not (= |~#double_Array_0~0.base| (+ |~#unsigned_long_int_Array_0~0.base| 4))) (let ((.cse0 (select |#memory_int| (+ 12 |~#unsigned_long_int_Array_0~0.base|))) (.cse1 (mod ~last_1_unsigned_long_int_Array_0_1__0_~0 4294967296))) (or (and (= .cse0 25) (<= .cse1 24)) (and (= ~last_1_unsigned_long_int_Array_0_1__0_~0 .cse0) (<= 25 .cse1)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9235fb10_65f6e0f8_Treesizes_45_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#volArray~0#1.base", "ULTIMATE.start_main_~MINVAL~0#1"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_368 Int) (v_ArrVal_367 Int) (v_ArrVal_366 Int)) (or (< v_ArrVal_368 (select |#memory_int| (+ |ULTIMATE.start_main_~#volArray~0#1.base| (- 12) (* 16 |ULTIMATE.start_main_~i~0#1|)))) (< |ULTIMATE.start_main_~MINVAL~0#1| (+ (select (store (store (store |#memory_int| (+ (- 16) |ULTIMATE.start_main_~#volArray~0#1.base| (* 16 |ULTIMATE.start_main_~i~0#1|)) v_ArrVal_366) (+ |ULTIMATE.start_main_~#volArray~0#1.base| (- 12) (* 16 |ULTIMATE.start_main_~i~0#1|)) v_ArrVal_368) (+ |ULTIMATE.start_main_~#volArray~0#1.base| (- 4) (* 16 |ULTIMATE.start_main_~i~0#1|)) v_ArrVal_367) (+ |ULTIMATE.start_main_~#volArray~0#1.base| 20)) 1))))";
		final String expectedResultAsString = "(<= |ULTIMATE.start_main_~MINVAL~0#1| (select |#memory_int| (+ |ULTIMATE.start_main_~#volArray~0#1.base| 20)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_92a8dca3_4894fb43_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_12| Int)) (<= 8834 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_12| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_9| Int)) (<= 8834 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_9| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_931510e4_a1bdba2_Treesizes_5_3() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~path1_len~0"),
		};
		final String formulaAsString = "(<= 0 (div ~path1_len~0 4294967296))";
		final String expectedResultAsString = "(<= 0 ~path1_len~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_93c36711_7bfc3189_Treesizes_275_158() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(and (or (and (<= (+ (mod (+ (* 65535 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 4))) 63 (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) (* (- 4294967296) (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 1) 4294967296))) (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) 4294967296))) 65536) (mod (+ (* (mod (+ (* 65535 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 4))) 63 (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) (* (- 4294967296) (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 1) 4294967296))) (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) 4294967296))) 65536) 4294967295) 63 (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) (* (- 4294967296) (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 1) 4294967296))) (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) 4294967296))) 4294967296)) (+ (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 4)) 65536) 4294967294)) (<= 0 (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) 32768)) (<= (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) 1) 0)) (and (<= (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) 32767) (<= (+ (mod (+ (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) (* (- 4294967296) (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 1) 4294967296))) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2))) (* 4294967295 (mod (+ (* 65535 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 4))) (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) (* (- 4294967296) (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 1) 4294967296))) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2))) 63) 65536)) 63) 4294967296) (mod (+ (* 65535 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 4))) (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) (* (- 4294967296) (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 1) 4294967296))) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2))) 63) 65536)) (+ (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 4)) 65536) 4294967294)) (<= 0 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2))))) (<= (div (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 1) 4294967296) (div (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 4294967296)))";
		final String expectedResultAsString = "(let ((.cse1 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13))) (.cse0 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)))) (and (<= .cse0 32767) (<= 0 (+ .cse0 32768)) (<= (mod .cse1 4294967296) 4294967294) (let ((.cse4 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 4)))) (<= (let ((.cse3 (div (+ .cse1 (* (- 4294967296) (div .cse1 4294967296))) (+ .cse0 (* (div .cse0 4294967296) (- 4294967296)))))) (let ((.cse2 (mod (+ (* 65535 .cse4) .cse3 63) 65536))) (+ .cse2 (mod (+ .cse3 (* 4294967295 .cse2) 63) 4294967296)))) (+ (mod .cse4 65536) 4294967294)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9454414f_f4e969fe_Treesizes_49_28() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base", "ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base| 4)) 0) (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_5| Int) (|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base_BEFORE_CALL_7| Int)) (and (= (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base_BEFORE_CALL_7|)) 0) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_5| 4)) 0) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_5| 8) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base_BEFORE_CALL_7|))) (<= (+ |ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base| 8) |ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base|) (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base| 4)) 0) (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_13| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_13| 4)) 0)))";
		final String expectedResultAsString = "(and (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base| 4)) 0) (<= (+ |ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base| 8) |ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base|) (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base| 4)) 0) (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_13| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_13| 4)) 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_94731bc9_c45462f8_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (<= 8688 (select |#memory_$Pointer$.base| (+ 4 |ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base|))) (exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_38| Int)) (<= 8688 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_38| 4)))))";
		final String expectedResultAsString = "(<= 8688 (select |#memory_$Pointer$.base| (+ 4 |ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_95130afd_d7ed085a_Treesizes_86_48() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_12~0", "~var_1_16~0", "ULTIMATE.start_step_~stepLocal_1~0#1", "~var_1_9~0", "~var_1_18~0", "~var_1_17~0"),
		};
		final String formulaAsString = "(and (or (and (= (mod (+ (* 255 ~var_1_18~0) ~var_1_17~0) 256) ~var_1_16~0) (<= (mod (+ (* 255 ~var_1_18~0) ~var_1_17~0) 256) 127)) (and (= (mod (+ (* 255 ~var_1_18~0) ~var_1_17~0) 256) (+ 256 ~var_1_16~0)) (<= 128 (mod (+ (* 255 ~var_1_18~0) ~var_1_17~0) 256)))) (or (and (= (mod (+ (* 255 ~var_1_18~0) ~var_1_17~0) 256) |ULTIMATE.start_step_~stepLocal_1~0#1|) (<= (mod (+ (* 255 ~var_1_18~0) ~var_1_17~0) 256) 127)) (and (= (+ 256 |ULTIMATE.start_step_~stepLocal_1~0#1|) (mod (+ (* 255 ~var_1_18~0) ~var_1_17~0) 256)) (<= 128 (mod (+ (* 255 ~var_1_18~0) ~var_1_17~0) 256)))) (= ~var_1_9~0 ~var_1_12~0))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_step_~stepLocal_1~0#1| ~var_1_16~0) (let ((.cse0 (mod (+ (* 255 ~var_1_18~0) ~var_1_17~0) 256))) (or (and (= .cse0 ~var_1_16~0) (<= .cse0 127)) (and (= .cse0 (+ 256 ~var_1_16~0)) (<= 128 .cse0)))) (= ~var_1_9~0 ~var_1_12~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_95b1dbc5_ca72ba02_Treesizes_32_32() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "old(#memory_int)", "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#vfio~0.base", "ldv_memset_#Ultimate.C_memset_#t~loopctr859#1", "#HeapAllocations", "ldv_memset_#in~s#1.base", "ldv_memset_#Ultimate.C_memset_#ptr#1.base"),
		};
		final String formulaAsString = "(and (<= 5567 |#HeapAllocations|) (<= |~#vfio~0.base| 3991) (<= |ldv_memset_#in~s#1.base| |ldv_memset_#Ultimate.C_memset_#ptr#1.base|) (exists ((|v_ldv_memset_#Ultimate.C_memset_#t~loopctr859#1_114| Int)) (and (<= 0 |v_ldv_memset_#Ultimate.C_memset_#t~loopctr859#1_114|) (= (store |old(#memory_int)| (+ |ldv_memset_#Ultimate.C_memset_#ptr#1.base| |v_ldv_memset_#Ultimate.C_memset_#t~loopctr859#1_114|) (select |#memory_int| (+ |ldv_memset_#Ultimate.C_memset_#ptr#1.base| |v_ldv_memset_#Ultimate.C_memset_#t~loopctr859#1_114|))) |#memory_int|) (<= (+ |v_ldv_memset_#Ultimate.C_memset_#t~loopctr859#1_114| 1) |ldv_memset_#Ultimate.C_memset_#t~loopctr859#1|))))";
		final String expectedResultAsString = "(and (<= 5567 |#HeapAllocations|) (<= |~#vfio~0.base| 3991) (<= |ldv_memset_#in~s#1.base| |ldv_memset_#Ultimate.C_memset_#ptr#1.base|) (exists ((|v_ldv_memset_#Ultimate.C_memset_#t~loopctr859#1_109| Int)) (and (= |#memory_int| (let ((.cse0 (+ |ldv_memset_#Ultimate.C_memset_#ptr#1.base| |v_ldv_memset_#Ultimate.C_memset_#t~loopctr859#1_109|))) (store |old(#memory_int)| .cse0 (select |#memory_int| .cse0)))) (<= 0 |v_ldv_memset_#Ultimate.C_memset_#t~loopctr859#1_109|) (<= (+ |v_ldv_memset_#Ultimate.C_memset_#t~loopctr859#1_109| 1) |ldv_memset_#Ultimate.C_memset_#t~loopctr859#1|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9685bc51_92a8dd2_Treesizes_14_12() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (<= |ULTIMATE.start_main_~y~0#1| (+ 9999999 (mod |ULTIMATE.start_main_~y~0#1| 4294967296))) (<= 10000000 |ULTIMATE.start_main_~y~0#1|) (= |ULTIMATE.start_main_~x~0#1| 0))";
		final String expectedResultAsString = "(and (<= 10000000 |ULTIMATE.start_main_~y~0#1|) (<= (div |ULTIMATE.start_main_~y~0#1| 4294967296) 0) (= |ULTIMATE.start_main_~x~0#1| 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_96e204a7_c916d213_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_array_eq_c_str_~array_len#1"),
		};
		final String formulaAsString = "(<= (mod |ULTIMATE.start_aws_array_eq_c_str_~array_len#1| 4294967296) 0)";
		final String expectedResultAsString = "(= (mod |ULTIMATE.start_aws_array_eq_c_str_~array_len#1| 4294967296) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9765659b_21fdc2_Treesizes_23_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~a~0#1.base"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_103 Int) (v_ArrVal_98 Int)) (= (+ (select (store (store |#memory_int| (+ (* |ULTIMATE.start_main_~i~0#1| 8) |ULTIMATE.start_main_~a~0#1.base|) v_ArrVal_98) (+ (* |ULTIMATE.start_main_~i~0#1| 8) |ULTIMATE.start_main_~a~0#1.base| 8) v_ArrVal_103) |ULTIMATE.start_main_~a~0#1.base|) 1) 0))";
		final String expectedResultAsString = "(forall ((v_ArrVal_103 Int) (v_ArrVal_102 Int)) (= (+ (select (let ((.cse0 (* |ULTIMATE.start_main_~i~0#1| 8))) (store (store |#memory_int| (+ .cse0 |ULTIMATE.start_main_~a~0#1.base|) v_ArrVal_102) (+ .cse0 |ULTIMATE.start_main_~a~0#1.base| 8) v_ArrVal_103)) |ULTIMATE.start_main_~a~0#1.base|) 1) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_97f12394_fc7f3e8d_Treesizes_221_207() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_11~0", "~var_1_1~0", "~var_1_10~0", "~var_1_16~0", "~var_1_5~0", "~var_1_2~0", "~var_1_8~0", "~last_1_var_1_14~0", "~var_1_9~0", "~var_1_18~0", "~var_1_7~0", "~var_1_17~0"),
		};
		final String formulaAsString = "(and (or (and (or (< (mod (* 255 ~var_1_11~0) 256) 128) (= (mod (* 255 ~var_1_11~0) 256) (+ 256 ~var_1_10~0))) (<= 128 (mod ~var_1_11~0 256)) (or (< 127 (mod (* 255 ~var_1_11~0) 256)) (and (or (< 0 (+ ~var_1_11~0 1)) (= (mod (* 255 ~var_1_11~0) 256) ~var_1_10~0)) (or (< ~var_1_11~0 0) (= (mod ~var_1_11~0 256) (+ 256 ~var_1_10~0)))))) (and (or (and (= (mod ~var_1_11~0 256) ~var_1_10~0) (<= (mod (* 255 ~var_1_11~0) 256) 127)) (and (<= 128 (mod (* 255 ~var_1_11~0) 256)) (or (and (= (mod (* 255 ~var_1_11~0) 256) (+ 256 ~var_1_10~0)) (<= (+ ~var_1_11~0 1) 0)) (and (= (mod ~var_1_11~0 256) ~var_1_10~0) (<= 0 ~var_1_11~0))))) (<= (mod ~var_1_11~0 256) 127))) (<= (mod ~var_1_8~0 65536) (+ ~var_1_18~0 (mod ~var_1_9~0 65536))) (= ~var_1_18~0 (mod ~var_1_8~0 65536)) (or (and (<= (+ (mod ~var_1_8~0 65536) 1) (+ ~last_1_var_1_14~0 (mod ~var_1_9~0 65536))) (= (+ ~var_1_7~0 ~last_1_var_1_14~0) (mod ~var_1_8~0 65536))) (and (= ~var_1_7~0 (mod ~var_1_9~0 65536)) (<= (+ ~last_1_var_1_14~0 (mod ~var_1_9~0 65536)) (mod ~var_1_8~0 65536)))) (or (and (= (mod ~var_1_7~0 65536) (+ 65536 ~var_1_1~0)) (<= 32768 (mod ~var_1_7~0 65536))) (and (<= (mod ~var_1_7~0 65536) 32767) (= (mod ~var_1_7~0 65536) ~var_1_1~0))) (not (= (mod ~var_1_2~0 256) 0)) (or (not (= (mod ~var_1_5~0 256) 0)) (not (= (mod ~var_1_17~0 256) 0))) (<= (div ~var_1_18~0 4294967296) 0) (= ~var_1_16~0 1) (<= (+ (mod ~var_1_9~0 65536) 1) (mod ~var_1_8~0 65536)))";
		final String expectedResultAsString = "(let ((.cse8 (mod ~var_1_9~0 65536)) (.cse6 (mod ~var_1_8~0 65536))) (and (let ((.cse0 (mod (* 255 ~var_1_11~0) 256)) (.cse4 (+ 256 ~var_1_10~0))) (let ((.cse1 (= .cse0 .cse4)) (.cse3 (+ ~var_1_11~0 1)) (.cse2 (mod ~var_1_11~0 256))) (or (and (or (< .cse0 128) .cse1) (<= 128 .cse2) (or (< 127 .cse0) (and (or (< 0 .cse3) (= .cse0 ~var_1_10~0)) (or (< ~var_1_11~0 0) (= .cse2 .cse4))))) (and (let ((.cse5 (= .cse2 ~var_1_10~0))) (or (and .cse5 (<= .cse0 127)) (and (<= 128 .cse0) (or (and .cse1 (<= .cse3 0)) (and .cse5 (<= 0 ~var_1_11~0)))))) (<= .cse2 127))))) (= ~var_1_18~0 .cse6) (let ((.cse7 (+ ~last_1_var_1_14~0 .cse8))) (or (and (<= (+ .cse6 1) .cse7) (= (+ ~var_1_7~0 ~last_1_var_1_14~0) .cse6)) (and (= ~var_1_7~0 .cse8) (<= .cse7 .cse6)))) (let ((.cse9 (mod ~var_1_7~0 65536))) (or (and (= .cse9 (+ 65536 ~var_1_1~0)) (<= 32768 .cse9)) (and (<= .cse9 32767) (= .cse9 ~var_1_1~0)))) (not (= (mod ~var_1_2~0 256) 0)) (or (not (= (mod ~var_1_5~0 256) 0)) (not (= (mod ~var_1_17~0 256) 0))) (= ~var_1_16~0 1) (<= (+ .cse8 1) .cse6)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_98238079_28e08e45_Treesizes_23_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ensure_array_list_has_allocated_data_member_~list.base", "ensure_array_list_has_allocated_data_member_#in~list.base"),
		};
		final String formulaAsString = "(and (exists ((v_ensure_array_list_has_allocated_data_member_~list.base_BEFORE_CALL_1 Int)) (= (mod (select |#memory_int| (+ v_ensure_array_list_has_allocated_data_member_~list.base_BEFORE_CALL_1 8)) 4294967296) 0)) (= ensure_array_list_has_allocated_data_member_~list.base |ensure_array_list_has_allocated_data_member_#in~list.base|) (= (mod (select |#memory_int| (+ ensure_array_list_has_allocated_data_member_~list.base 8)) 4294967296) 0))";
		final String expectedResultAsString = "(and (= ensure_array_list_has_allocated_data_member_~list.base |ensure_array_list_has_allocated_data_member_#in~list.base|) (= (mod (select |#memory_int| (+ ensure_array_list_has_allocated_data_member_~list.base 8)) 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_98a52df8_3880184c_Treesizes_25_25() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~k~0#1", "~SIZE~0"),
		};
		final String formulaAsString = "(and (<= 1 (mod (+ 4294967295 |ULTIMATE.start_main_~k~0#1|) 4294967296)) (<= 4 (mod (+ 3 |ULTIMATE.start_main_~k~0#1|) 4294967296)) (= ~SIZE~0 20000001) (<= (mod (+ 3 |ULTIMATE.start_main_~k~0#1|) 4294967296) 20000001))";
		final String expectedResultAsString = "(let ((.cse0 (mod (+ 2 |ULTIMATE.start_main_~k~0#1|) 4294967296))) (and (<= 4 .cse0) (= ~SIZE~0 20000001) (<= (mod (+ 3 |ULTIMATE.start_main_~k~0#1|) 4294967296) 20000001) (<= .cse0 20000001)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_996b5ab6_44516ccb_Treesizes_27_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations", "ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#to~0#1.base"),
		};
		final String formulaAsString = "(and (<= (+ 16 |ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#to~0#1.base|) |#StackAllocations|) (= (select |#memory_$Pointer$.base| (+ 12 |ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#to~0#1.base|)) 0) (exists ((|v_ULTIMATE.start_ensure_byte_buf_has_allocated_buffer_member_~buf#1.base_BEFORE_CALL_6| Int)) (and (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_ensure_byte_buf_has_allocated_buffer_member_~buf#1.base_BEFORE_CALL_6| 12)) 0) (<= (+ 16 |v_ULTIMATE.start_ensure_byte_buf_has_allocated_buffer_member_~buf#1.base_BEFORE_CALL_6|) |#StackAllocations|))))";
		final String expectedResultAsString = "(and (<= (+ 16 |ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#to~0#1.base|) |#StackAllocations|) (= (select |#memory_$Pointer$.base| (+ 12 |ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#to~0#1.base|)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_99a666e5_bf51dd66_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_from_buf_~buf.base_BEFORE_CALL_4 Int)) (<= 8684 (select |#memory_$Pointer$.base| (+ v_aws_byte_cursor_from_buf_~buf.base_BEFORE_CALL_4 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_from_buf_harness_~#buf~3#1.base_BEFORE_CALL_20| Int)) (<= 8684 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_from_buf_harness_~#buf~3#1.base_BEFORE_CALL_20| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_99faab3d_7df27028_Treesizes_196_45() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "memset_impl_#in~c", "memset_impl_#in~s.base", "memset_impl_~sp~0.base", "memset_impl_#in~n", "memset_impl_~c"),
		};
		final String formulaAsString = "(and (or (and (<= (mod memset_impl_~c 256) 127) (exists ((v_DerPreprocessor_5 Int) (v_z_12 Int)) (and (= (select |#memory_int| (+ memset_impl_~sp~0.base v_z_12)) (mod memset_impl_~c 256)) (<= 0 v_z_12) (= (select (store (store |#memory_int| (+ memset_impl_~sp~0.base v_z_12) v_DerPreprocessor_5) (+ memset_impl_~sp~0.base v_z_12 (- 4294967296)) (select |#memory_int| (+ memset_impl_~sp~0.base v_z_12))) (+ memset_impl_~sp~0.base 4)) (mod memset_impl_~c 256)) (<= v_z_12 2147483647)))) (and (or (and (exists ((v_z_12 Int)) (and (<= 2147483648 v_z_12) (<= v_z_12 4294967295) (= (select |#memory_int| (+ memset_impl_~sp~0.base v_z_12 (- 4294967296))) (mod memset_impl_~c 256)))) (<= (mod memset_impl_~c 256) 127)) (and (exists ((v_z_12 Int)) (and (<= 2147483648 v_z_12) (<= v_z_12 4294967295) (= (+ 256 (select |#memory_int| (+ memset_impl_~sp~0.base v_z_12 (- 4294967296)))) (mod memset_impl_~c 256)))) (<= 128 (mod memset_impl_~c 256)))) (or (and (= (+ 256 (select |#memory_int| (+ memset_impl_~sp~0.base 4))) (mod memset_impl_~c 256)) (<= 128 (mod memset_impl_~c 256))) (and (<= (mod memset_impl_~c 256) 127) (= (select |#memory_int| (+ memset_impl_~sp~0.base 4)) (mod memset_impl_~c 256))))) (and (exists ((v_DerPreprocessor_5 Int) (v_z_12 Int)) (and (<= 0 v_z_12) (= (+ 256 (select |#memory_int| (+ memset_impl_~sp~0.base v_z_12))) (mod memset_impl_~c 256)) (= (mod memset_impl_~c 256) (+ 256 (select (store (store |#memory_int| (+ memset_impl_~sp~0.base v_z_12) v_DerPreprocessor_5) (+ memset_impl_~sp~0.base v_z_12 (- 4294967296)) (select |#memory_int| (+ memset_impl_~sp~0.base v_z_12))) (+ memset_impl_~sp~0.base 4)))) (<= v_z_12 2147483647))) (<= 128 (mod memset_impl_~c 256)))) (= memset_impl_~sp~0.base |memset_impl_#in~s.base|) (= |memset_impl_#in~c| memset_impl_~c) (<= 5 (mod |memset_impl_#in~n| 4294967296)))";
		final String expectedResultAsString = "(and (= memset_impl_~sp~0.base |memset_impl_#in~s.base|) (= |memset_impl_#in~c| memset_impl_~c) (<= 5 (mod |memset_impl_#in~n| 4294967296)) (let ((.cse0 (select |#memory_int| (+ memset_impl_~sp~0.base 4))) (.cse1 (mod memset_impl_~c 256))) (or (and (= (+ 256 .cse0) .cse1) (<= 128 .cse1)) (and (<= .cse1 127) (= .cse0 .cse1)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9a93dcad_fd368cec_Treesizes_125_119() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_12~0", "~var_1_1~0", "~var_1_11~0", "~var_1_10~0", "~var_1_4~0", "~var_1_5~0", "~var_1_2~0", "~var_1_14~0", "~var_1_3~0", "~var_1_13~0", "~var_1_9~0"),
		};
		final String formulaAsString = "(and (= (mod ~var_1_14~0 256) 0) (= (mod ~var_1_9~0 256) (mod (+ ~var_1_4~0 ~var_1_10~0) 256)) (= ~var_1_3~0 ~var_1_5~0) (= ~var_1_13~0 0) (or (and (or (= ~var_1_4~0 ~var_1_1~0) (< ~var_1_3~0 ~var_1_4~0)) (= (mod ~var_1_2~0 256) 0)) (and (<= 1 (mod ~var_1_2~0 256)) (or (and (= (mod (+ ~var_1_3~0 (* 255 ~var_1_4~0)) 256) (+ 256 ~var_1_1~0)) (<= 128 (mod (+ ~var_1_3~0 (* 255 ~var_1_4~0)) 256))) (and (= (mod (+ ~var_1_3~0 (* 255 ~var_1_4~0)) 256) ~var_1_1~0) (<= (mod (+ ~var_1_3~0 (* 255 ~var_1_4~0)) 256) 127))))) (<= (div (+ ~var_1_4~0 ~var_1_10~0) 256) (+ (div ~var_1_10~0 256) (div ~var_1_9~0 256))) (or (< ~var_1_1~0 (+ ~var_1_5~0 1)) (and (or (= (mod ~var_1_12~0 256) 0) (= (mod ~var_1_11~0 256) 1)) (or (= (mod ~var_1_11~0 256) 0) (not (= (mod ~var_1_12~0 256) 0))))))";
		final String expectedResultAsString = "(and (<= (+ ~var_1_4~0 (mod ~var_1_10~0 256)) ~var_1_9~0) (= (mod ~var_1_14~0 256) 0) (= (mod ~var_1_9~0 256) (mod (+ ~var_1_4~0 ~var_1_10~0) 256)) (= ~var_1_3~0 ~var_1_5~0) (= ~var_1_13~0 0) (let ((.cse0 (mod ~var_1_2~0 256))) (or (and (or (= ~var_1_4~0 ~var_1_1~0) (< ~var_1_3~0 ~var_1_4~0)) (= .cse0 0)) (and (<= 1 .cse0) (let ((.cse1 (mod (+ ~var_1_3~0 (* 255 ~var_1_4~0)) 256))) (or (and (= .cse1 (+ 256 ~var_1_1~0)) (<= 128 .cse1)) (and (= .cse1 ~var_1_1~0) (<= .cse1 127))))))) (or (< ~var_1_1~0 (+ ~var_1_5~0 1)) (let ((.cse3 (mod ~var_1_11~0 256)) (.cse2 (= (mod ~var_1_12~0 256) 0))) (and (or .cse2 (= .cse3 1)) (or (= .cse3 0) (not .cse2))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9b59fba3_63ba2699_Treesizes_21_17() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~0#1"),
		};
		final String formulaAsString = "(and (<= (div |ULTIMATE.start_main_~y~0#1| 2) 4) (<= (+ |ULTIMATE.start_main_~y~0#1| 1) (* (div (+ 89478484 (* 178956971 (div |ULTIMATE.start_main_~y~0#1| 2))) 268435456) 3)))";
		final String expectedResultAsString = "(and (<= (+ |ULTIMATE.start_main_~y~0#1| 1) (* (div (+ (* |ULTIMATE.start_main_~y~0#1| 178956971) 178956968) 536870912) 3)) (<= |ULTIMATE.start_main_~y~0#1| 8))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9ba0b713_9cfef732_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_4| Int)) (and (<= (+ |v_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_4| 25) |#StackAllocations|) (<= 4 (mod (select |#memory_int| |v_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_4|) 4294967296))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30| Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30| 25) |#StackAllocations|) (<= 4 (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_30|) 4294967296))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9c06fee6_660142c9_Treesizes_23_18() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_23~0", "~var_1_28~0"),
		};
		final String formulaAsString = "(and (<= (div ~var_1_28~0 256) 0) (<= (div (+ ~var_1_23~0 ~var_1_28~0 (* (- 256) (div ~var_1_28~0 256))) 4294967296) (div ~var_1_23~0 4294967296)) (<= 100 ~var_1_28~0))";
		final String expectedResultAsString = "(and (<= 100 ~var_1_28~0) (<= (div (+ ~var_1_23~0 ~var_1_28~0) 4294967296) (div ~var_1_23~0 4294967296)) (= (div ~var_1_28~0 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9c74d838_d39ed91b_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base| 4)) 0) (exists ((|v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_14| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_14| 4)) 0)))";
		final String expectedResultAsString = "(= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base| 4)) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9d03dd5_3c57a013_Treesizes_66_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~a~0#1.base", "ULTIMATE.start_main_~p~0#1.base", "#HeapAllocations"),
		};
		final String formulaAsString = "(and (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_main_~a~0#1.base| 4)) (+ |ULTIMATE.start_main_~a~0#1.base| 8)) (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_main_~a~0#1.base| 4)) |ULTIMATE.start_main_~p~0#1.base|) (<= (+ 16 |ULTIMATE.start_main_~a~0#1.base|) |#HeapAllocations|) (forall ((v_ArrVal_126 Int) (v_ArrVal_124 Int) (|v_ULTIMATE.start_main_~p~0#1.base_66| Int) (v_ArrVal_127 Int)) (or (= (select (store (store (store |#memory_$Pointer$.base| |ULTIMATE.start_main_~p~0#1.base| v_ArrVal_124) (+ 4 |ULTIMATE.start_main_~p~0#1.base|) v_ArrVal_126) |v_ULTIMATE.start_main_~p~0#1.base_66| v_ArrVal_127) (+ |ULTIMATE.start_main_~a~0#1.base| 4)) |v_ULTIMATE.start_main_~p~0#1.base_66|) (< v_ArrVal_126 |#HeapAllocations|) (= (select (store (store (store |#memory_$Pointer$.base| |ULTIMATE.start_main_~p~0#1.base| v_ArrVal_124) (+ 4 |ULTIMATE.start_main_~p~0#1.base|) v_ArrVal_126) |v_ULTIMATE.start_main_~p~0#1.base_66| v_ArrVal_127) (+ |ULTIMATE.start_main_~a~0#1.base| 4)) |ULTIMATE.start_main_~p~0#1.base|) (< |v_ULTIMATE.start_main_~p~0#1.base_66| v_ArrVal_126))))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_main_~a~0#1.base| 4)))) (and (= .cse0 (+ |ULTIMATE.start_main_~a~0#1.base| 8)) (= .cse0 |ULTIMATE.start_main_~p~0#1.base|) (<= (+ 16 |ULTIMATE.start_main_~a~0#1.base|) |#HeapAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9d74b571_b436d049_Treesizes_24_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_39| Int)) (<= (mod (+ (select |#memory_int| (+ |v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_39| 8)) 4294967295) 4294967296) 4294967294)) (<= (mod (+ (select |#memory_int| (+ |ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base| 8)) 4294967295) 4294967296) 4294967294))";
		final String expectedResultAsString = "(<= (mod (+ (select |#memory_int| (+ |ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base| 8)) 4294967295) 4294967296) 4294967294)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9e139e6b_197b5858_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_22| Int)) (<= 8684 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_22| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_21| Int)) (<= 8684 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_21| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9e46b063_44e1dfdc_Treesizes_17_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_byte_cursor_left_trim_pred_~source.base"),
		};
		final String formulaAsString = "(forall ((|v_aws_byte_cursor_left_trim_pred_~#trimmed~1.base_12| Int)) (or (< (mod (select |#memory_int| |v_aws_byte_cursor_left_trim_pred_~#trimmed~1.base_12|) 4294967296) 1) (not (= (select |#memory_int| |v_aws_byte_cursor_left_trim_pred_~#trimmed~1.base_12|) (select |#memory_int| aws_byte_cursor_left_trim_pred_~source.base)))))";
		final String expectedResultAsString = "(<= (mod (select |#memory_int| aws_byte_cursor_left_trim_pred_~source.base) 4294967296) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9e68c2e_ce2f40e_Treesizes_119_119() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~cur#1.base_21| Int)) (= (mod (select |#memory_int| |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~cur#1.base_21|) 4294967296) 0)) (or (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5| Int)) (and (= (mod (select |#memory_int| (+ (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 4294967296) (- 4294967288) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 256) 0) (<= 2147483648 (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 4294967296)))) (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5| Int)) (and (= (mod (select |#memory_int| (+ (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 4294967296) 8 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 256) 0) (<= (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 4294967296) 2147483647)))) (or (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_15| Int)) (and (<= (mod (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_15| 4)) 4294967296) 2147483647) (= (mod (select |#memory_int| (+ (mod (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_15| 4)) 4294967296) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_15| 8)) 256) 0))) (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_15| Int)) (and (<= 2147483648 (mod (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_15| 4)) 4294967296)) (= (mod (select |#memory_int| (+ (mod (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_15| 4)) 4294967296) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_15| (- 4294967288))) 256) 0)))))";
		final String expectedResultAsString = "(and (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~cur#1.base_BEFORE_CALL_3| Int)) (= (mod (select |#memory_int| |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~cur#1.base_BEFORE_CALL_3|) 4294967296) 0)) (or (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| Int)) (let ((.cse0 (mod (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| 4)) 4294967296))) (and (= (mod (select |#memory_int| (+ .cse0 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| (- 4294967288))) 256) 0) (<= 2147483648 .cse0)))) (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| Int)) (let ((.cse1 (mod (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| 4)) 4294967296))) (and (= (mod (select |#memory_int| (+ .cse1 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| 8)) 256) 0) (<= .cse1 2147483647))))) (or (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5| Int)) (let ((.cse2 (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 4294967296))) (and (= (mod (select |#memory_int| (+ .cse2 (- 4294967288) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 256) 0) (<= 2147483648 .cse2)))) (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5| Int)) (let ((.cse3 (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 4294967296))) (and (= (mod (select |#memory_int| (+ .cse3 8 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 256) 0) (<= .cse3 2147483647))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9ec308bb_8ea6d2b5_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_34| Int)) (and (= |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_34| (select |#memory_$Pointer$.base| (+ (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_34|) 4))) (<= (+ |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_34| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_34|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_31| Int)) (let ((.cse0 (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_31|))) (and (<= (+ |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_31| 8) .cse0) (= (select |#memory_$Pointer$.base| (+ .cse0 4)) |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_31|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9f3449f2_c3d60ac5_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_linked_list_back_~list.base"),
		};
		final String formulaAsString = "(and (<= (+ (select |#memory_$Pointer$.base| aws_linked_list_back_~list.base) 10) aws_linked_list_back_~list.base) (exists ((v_aws_linked_list_back_~list.base_BEFORE_CALL_26 Int)) (<= (+ (select |#memory_$Pointer$.base| v_aws_linked_list_back_~list.base_BEFORE_CALL_26) 10) v_aws_linked_list_back_~list.base_BEFORE_CALL_26)))";
		final String expectedResultAsString = "(<= (+ (select |#memory_$Pointer$.base| aws_linked_list_back_~list.base) 10) aws_linked_list_back_~list.base)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9fa0cbed_c9ab9e7e_Treesizes_45_11() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_2~0", "~var_1_9~0"),
		};
		final String formulaAsString = "(and (<= 1 (mod ~var_1_9~0 4294967296)) (or (= (mod ~var_1_2~0 256) 0) (forall ((v_y_97 Int) (v_z_97 Int)) (or (< 4294967295 v_z_97) (< v_z_97 0) (< 65535 (+ (* v_y_97 4294967296) (* v_z_97 4294967295))) (< (+ v_z_97 65535) (mod ~var_1_9~0 4294967296)) (< (+ (* v_y_97 4294967296) (* v_z_97 4294967295)) 0)))))";
		final String expectedResultAsString = "(and (<= 1 (mod ~var_1_9~0 4294967296)) (= (mod ~var_1_2~0 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a012cb99_de4accc1_Treesizes_21_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base", "ULTIMATE.start_property_#t~mem95#1"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| (+ |~#WrapperStruct00~0.base| 12)) (+ |ULTIMATE.start_property_#t~mem95#1| 10)) (= (select |#memory_int| (+ |~#WrapperStruct00~0.base| 12)) (+ (select |#memory_int| |~#WrapperStruct00~0.base|) 10)))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| |~#WrapperStruct00~0.base|))) (and (= (select |#memory_int| (+ |~#WrapperStruct00~0.base| 12)) (+ .cse0 10)) (= |ULTIMATE.start_property_#t~mem95#1| .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a0812d67_6629ff2e_Treesizes_50_50() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#unsigned_char_Array_0~0.base", "~#double_Array_0~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base", "~#signed_char_Array_0~0.base", "~#signed_long_int_Array_0~0.base"),
		};
		final String formulaAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base (+ |~#signed_char_Array_0~0.base| 1))) (not (= (+ 3 |~#signed_char_Array_0~0.base|) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)) (forall ((v_ArrVal_432 Int)) (<= (mod (select (store |#memory_int| |~#double_Array_0~0.base| v_ArrVal_432) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base) 256) 0)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base (+ |~#unsigned_char_Array_0~0.base| 1))) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base (+ 2 |~#unsigned_char_Array_0~0.base|))) (not (= |~#signed_long_int_Array_0~0.base| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base |~#unsigned_char_Array_0~0.base|)) (not (= (+ |~#signed_char_Array_0~0.base| 4) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= |~#double_Array_0~0.base| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base (+ |~#signed_char_Array_0~0.base| 1))) (not (= (+ 3 |~#signed_char_Array_0~0.base|) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base (+ |~#unsigned_char_Array_0~0.base| 1))) (<= (mod (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base) 256) 0) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base (+ 2 |~#unsigned_char_Array_0~0.base|))) (not (= |~#signed_long_int_Array_0~0.base| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base |~#unsigned_char_Array_0~0.base|)) (not (= (+ |~#signed_char_Array_0~0.base| 4) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a1310c8f_10153719_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_19| Int)) (= (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_19|)) 0))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_18| Int)) (= (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_18|)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a1a7fa1d_35ec9896_Treesizes_24_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_reset_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (<= (mod (+ 4294967295 (select |#memory_int| (+ |ULTIMATE.start_aws_byte_buf_reset_harness_~#buf~3#1.base| 8))) 4294967296) 4294967294) (exists ((|v_ULTIMATE.start_aws_byte_buf_reset_harness_~#buf~3#1.base_BEFORE_CALL_30| Int)) (<= (mod (+ (select |#memory_int| (+ |v_ULTIMATE.start_aws_byte_buf_reset_harness_~#buf~3#1.base_BEFORE_CALL_30| 8)) 4294967295) 4294967296) 4294967294)))";
		final String expectedResultAsString = "(<= (mod (+ 4294967295 (select |#memory_int| (+ |ULTIMATE.start_aws_byte_buf_reset_harness_~#buf~3#1.base| 8))) 4294967296) 4294967294)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a1f73990_ffbaba90_Treesizes_15_15() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_32~0", "~var_1_20~0"),
		};
		final String formulaAsString = "(and (= (mod (+ (* 4294967295 ~var_1_20~0) 4294967295) 4294967296) 0) (<= 1 (mod ~var_1_32~0 256)))";
		final String expectedResultAsString = "(and (<= 1 (mod ~var_1_32~0 256)) (<= (mod (+ (* 4294967295 ~var_1_20~0) 4294967295) 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a245384b_1c3266d_Treesizes_22_15() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#sum~0#1.base", "ULTIMATE.start_main_~a~0#1.base", "~N~0"),
		};
		final String formulaAsString = "(or (< 4 ~N~0) (forall ((|ULTIMATE.start_main_~i~0#1| Int) (v_ArrVal_188 Int)) (= 5 (select (store (store |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| (* |ULTIMATE.start_main_~i~0#1| 4)) 5) |ULTIMATE.start_main_~#sum~0#1.base| v_ArrVal_188) (+ |ULTIMATE.start_main_~a~0#1.base| 4)))))";
		final String expectedResultAsString = "(or (< 4 ~N~0) (forall ((v_ArrVal_188 Int)) (= (select (store |#memory_int| |ULTIMATE.start_main_~#sum~0#1.base| v_ArrVal_188) (+ |ULTIMATE.start_main_~a~0#1.base| 4)) 5)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a2a6c729_12f1beb_Treesizes_20_3() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(or (< |ULTIMATE.start_main_~n~0#1| (+ 2 (div |ULTIMATE.start_main_~n~0#1| 2))) (and (not (= (mod |ULTIMATE.start_main_~n~0#1| 2) 0)) (<= (+ |ULTIMATE.start_main_~n~0#1| 1) 0)))";
		final String expectedResultAsString = "(<= |ULTIMATE.start_main_~n~0#1| 2)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a33e933f_cd7f98f_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_harness_~#cursor~2#1.base_BEFORE_CALL_32| Int)) (<= 8825 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_string_eq_byte_cursor_harness_~#cursor~2#1.base_BEFORE_CALL_32| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_harness_~#cursor~2#1.base_BEFORE_CALL_27| Int)) (<= 8825 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_string_eq_byte_cursor_harness_~#cursor~2#1.base_BEFORE_CALL_27| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a378bc33_4351e268_Treesizes_57_47() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#unsigned_char_Array_0~0.base", "~last_1_unsigned_char_Array_0_1_~0", "~#signed_long_int_Array_0~0.base"),
		};
		final String formulaAsString = "(and (<= (+ (select |#memory_int| (+ |~#signed_long_int_Array_0~0.base| 4)) (mod (+ (select |#memory_int| |~#unsigned_char_Array_0~0.base|) (select |#memory_int| (+ |~#signed_long_int_Array_0~0.base| 8)) ~last_1_unsigned_char_Array_0_1_~0 (* (select |#memory_int| (+ |~#signed_long_int_Array_0~0.base| 4)) 255)) 256)) (+ (select |#memory_int| (+ |~#signed_long_int_Array_0~0.base| 8)) (mod ~last_1_unsigned_char_Array_0_1_~0 256) 255)) (<= (+ (select |#memory_int| (+ |~#signed_long_int_Array_0~0.base| 8)) (mod ~last_1_unsigned_char_Array_0_1_~0 256) (mod (select |#memory_int| |~#unsigned_char_Array_0~0.base|) 256)) (select |#memory_int| (+ |~#signed_long_int_Array_0~0.base| 4))))";
		final String expectedResultAsString = "(let ((.cse2 (select |#memory_int| (+ |~#signed_long_int_Array_0~0.base| 8))) (.cse3 (mod ~last_1_unsigned_char_Array_0_1_~0 256)) (.cse1 (select |#memory_int| |~#unsigned_char_Array_0~0.base|)) (.cse0 (select |#memory_int| (+ |~#signed_long_int_Array_0~0.base| 4)))) (and (<= (+ .cse0 (mod (+ (* .cse1 255) 255) 256)) (+ .cse2 .cse3 255)) (<= (+ .cse2 .cse3 (mod .cse1 256)) .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a3f9deb7_7e5ca63_Treesizes_16_9() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_Id_MCDC_89_~Id_MCDC_96~0#1"),
		};
		final String formulaAsString = "(and (not (= 41 (mod (+ 4294967295 |ULTIMATE.start_Id_MCDC_89_~Id_MCDC_96~0#1|) 4294967296))) (<= (mod (+ 4294967295 |ULTIMATE.start_Id_MCDC_89_~Id_MCDC_96~0#1|) 4294967296) 41))";
		final String expectedResultAsString = "(<= (mod (+ 41 (* 4294967295 |ULTIMATE.start_Id_MCDC_89_~Id_MCDC_96~0#1|)) 4294967296) 40)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a4588271_d4f6296b_Treesizes_191_186() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~last_1_var_1_17~0", "~var_1_10~0", "~var_1_4~0", "~last_1_var_1_11~0", "~var_1_16~0", "~var_1_5~0", "~var_1_14~0", "~last_1_var_1_13~0", "~last_1_var_1_12~0", "~var_1_13~0", "~var_1_8~0", "~var_1_9~0", "~var_1_19~0", "~var_1_18~0", "~var_1_6~0", "~last_1_var_1_18~0", "~last_1_var_1_1~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (or (and (or (not (= (mod ~var_1_8~0 256) 0)) (and (not (= (mod ~last_1_var_1_12~0 256) 0)) (not (= (mod ~var_1_9~0 256) 0))) (= (mod ~var_1_6~0 256) 0)) (or (and (or (= (mod ~last_1_var_1_12~0 256) 0) (= (mod ~var_1_9~0 256) 0)) (= (mod ~var_1_8~0 256) 0)) (= (mod ~var_1_6~0 256) 1))) (< 0 (+ ~last_1_var_1_1~0 1))) (= 0 (mod ~var_1_10~0 256)) (or (not (= (mod ~last_1_var_1_11~0 256) 0)) (not (= (mod ~last_1_var_1_12~0 256) 0)) (= (mod ~var_1_18~0 256) (mod ~var_1_16~0 256)) (and (<= (mod ~last_1_var_1_17~0 65536) (* ~var_1_4~0 ~last_1_var_1_1~0)) (not (= (* ~var_1_4~0 ~last_1_var_1_1~0) (mod ~last_1_var_1_17~0 65536))))) (= (mod ~var_1_19~0 256) (mod ~var_1_18~0 256)) (= (mod (+ (* (mod ~last_1_var_1_18~0 256) 65535) ~var_1_14~0) 65536) (mod ~var_1_13~0 65536)) (<= (+ (mod ~var_1_14~0 65536) (mod ~var_1_13~0 65536)) (+ (mod ~last_1_var_1_18~0 256) ~var_1_13~0 65535)) (or (and (= (mod ~last_1_var_1_12~0 256) 0) (<= (+ 5 (mod ~last_1_var_1_13~0 65536)) ~var_1_4~0) (<= (+ 5 (mod ~last_1_var_1_13~0 65536)) ~var_1_5~0) (= (+ ~var_1_1~0 128) 0)) (and (= (mod ~last_1_var_1_13~0 65536) ~var_1_1~0) (or (not (= (mod ~last_1_var_1_12~0 256) 0)) (< ~var_1_5~0 (+ 5 (mod ~last_1_var_1_13~0 65536))) (< ~var_1_4~0 (+ 5 (mod ~last_1_var_1_13~0 65536)))))) (<= (div ~var_1_19~0 256) (div ~var_1_18~0 256)))";
		final String expectedResultAsString = "(let ((.cse4 (= (mod ~last_1_var_1_12~0 256) 0))) (let ((.cse5 (mod ~var_1_18~0 256)) (.cse8 (mod ~last_1_var_1_18~0 256)) (.cse1 (not .cse4))) (and (or (let ((.cse2 (= (mod ~var_1_9~0 256) 0)) (.cse0 (= (mod ~var_1_8~0 256) 0)) (.cse3 (mod ~var_1_6~0 256))) (and (or (not .cse0) (and .cse1 (not .cse2)) (= .cse3 0)) (or (and (or .cse4 .cse2) .cse0) (= .cse3 1)))) (< 0 (+ ~last_1_var_1_1~0 1))) (= 0 (mod ~var_1_10~0 256)) (or (not (= (mod ~last_1_var_1_11~0 256) 0)) .cse1 (= .cse5 (mod ~var_1_16~0 256)) (let ((.cse7 (* ~var_1_4~0 ~last_1_var_1_1~0)) (.cse6 (mod ~last_1_var_1_17~0 65536))) (and (<= .cse6 .cse7) (not (= .cse7 .cse6))))) (<= (mod ~var_1_14~0 65536) (+ .cse8 ~var_1_13~0)) (= (mod ~var_1_19~0 256) .cse5) (= (mod (+ (* .cse8 65535) ~var_1_14~0) 65536) (mod ~var_1_13~0 65536)) (let ((.cse10 (mod ~last_1_var_1_13~0 65536))) (let ((.cse9 (+ 5 .cse10))) (or (and .cse4 (<= .cse9 ~var_1_4~0) (<= .cse9 ~var_1_5~0) (= (+ ~var_1_1~0 128) 0)) (and (= .cse10 ~var_1_1~0) (or .cse1 (< ~var_1_5~0 .cse9) (< ~var_1_4~0 .cse9)))))) (<= (div ~var_1_19~0 256) (div ~var_1_18~0 256)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a4ca051e_a65cf075_Treesizes_100_42() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "func_to_recursive_line_0_to_40_0_~a.base", "func_to_recursive_line_0_to_40_0_~y.base", "func_to_recursive_line_0_to_40_0_~x.base", "func_to_recursive_line_0_to_40_0_~b.base", "func_to_recursive_line_0_to_40_0_~z.base"),
		};
		final String formulaAsString = "(and (exists ((v_func_to_recursive_line_0_to_40_0_~y.base_BEFORE_CALL_1 Int) (v_func_to_recursive_line_0_to_40_0_~z.base_BEFORE_CALL_1 Int) (v_func_to_recursive_line_0_to_40_0_~x.base_BEFORE_CALL_1 Int) (v_func_to_recursive_line_0_to_40_0_~a.base_BEFORE_CALL_1 Int)) (and (<= (+ 8 v_func_to_recursive_line_0_to_40_0_~x.base_BEFORE_CALL_1) v_func_to_recursive_line_0_to_40_0_~y.base_BEFORE_CALL_1) (= (select |#memory_int| v_func_to_recursive_line_0_to_40_0_~z.base_BEFORE_CALL_1) 0) (<= (+ v_func_to_recursive_line_0_to_40_0_~y.base_BEFORE_CALL_1 8) v_func_to_recursive_line_0_to_40_0_~z.base_BEFORE_CALL_1) (= (select |#memory_int| (+ (- 4) v_func_to_recursive_line_0_to_40_0_~x.base_BEFORE_CALL_1)) (select |#memory_int| v_func_to_recursive_line_0_to_40_0_~y.base_BEFORE_CALL_1)) (= (select |#memory_int| v_func_to_recursive_line_0_to_40_0_~x.base_BEFORE_CALL_1) (select |#memory_int| v_func_to_recursive_line_0_to_40_0_~a.base_BEFORE_CALL_1)) (<= (+ 8 v_func_to_recursive_line_0_to_40_0_~a.base_BEFORE_CALL_1) v_func_to_recursive_line_0_to_40_0_~x.base_BEFORE_CALL_1))) (<= (+ 12 func_to_recursive_line_0_to_40_0_~b.base) func_to_recursive_line_0_to_40_0_~y.base) (= (select |#memory_int| func_to_recursive_line_0_to_40_0_~a.base) (select |#memory_int| (+ func_to_recursive_line_0_to_40_0_~b.base 4))) (exists ((|func_to_recursive_line_0_to_40_0_#t~mem5| Int)) (and (<= |func_to_recursive_line_0_to_40_0_#t~mem5| (select |#memory_int| func_to_recursive_line_0_to_40_0_~y.base)) (<= (* (select |#memory_int| func_to_recursive_line_0_to_40_0_~a.base) (select |#memory_int| func_to_recursive_line_0_to_40_0_~b.base)) (* |func_to_recursive_line_0_to_40_0_#t~mem5| (select |#memory_int| func_to_recursive_line_0_to_40_0_~x.base))))) (<= (+ func_to_recursive_line_0_to_40_0_~a.base 4) func_to_recursive_line_0_to_40_0_~b.base) (= (select |#memory_int| func_to_recursive_line_0_to_40_0_~y.base) (select |#memory_int| func_to_recursive_line_0_to_40_0_~b.base)) (= (select |#memory_int| func_to_recursive_line_0_to_40_0_~z.base) 0) (<= (+ 8 func_to_recursive_line_0_to_40_0_~y.base) func_to_recursive_line_0_to_40_0_~z.base) (= (+ func_to_recursive_line_0_to_40_0_~b.base 4) func_to_recursive_line_0_to_40_0_~x.base))";
		final String expectedResultAsString = "(let ((.cse0 (+ func_to_recursive_line_0_to_40_0_~b.base 4))) (and (<= (+ 12 func_to_recursive_line_0_to_40_0_~b.base) func_to_recursive_line_0_to_40_0_~y.base) (= (select |#memory_int| func_to_recursive_line_0_to_40_0_~a.base) (select |#memory_int| .cse0)) (<= (+ func_to_recursive_line_0_to_40_0_~a.base 4) func_to_recursive_line_0_to_40_0_~b.base) (= (select |#memory_int| func_to_recursive_line_0_to_40_0_~y.base) (select |#memory_int| func_to_recursive_line_0_to_40_0_~b.base)) (= (select |#memory_int| func_to_recursive_line_0_to_40_0_~z.base) 0) (<= (+ 8 func_to_recursive_line_0_to_40_0_~y.base) func_to_recursive_line_0_to_40_0_~z.base) (= .cse0 func_to_recursive_line_0_to_40_0_~x.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a52226b_b5189acd_Treesizes_27_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations", "ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (<= (+ |ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base| 16) |#StackAllocations|) (exists ((|v_ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base_BEFORE_CALL_75| Int)) (and (<= (+ 16 |v_ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base_BEFORE_CALL_75|) |#StackAllocations|) (<= 8681 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base_BEFORE_CALL_75| 4))))) (<= 8681 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base| 4))))";
		final String expectedResultAsString = "(and (<= (+ |ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base| 16) |#StackAllocations|) (<= 8681 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_eq_c_str_harness_~#buf~3#1.base| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a56345fd_3f03f65a_Treesizes_15_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations", "aws_byte_cursor_advance_nospec_~cursor#1.base"),
		};
		final String formulaAsString = "(and (<= (mod (* (select |#memory_int| |aws_byte_cursor_advance_nospec_~cursor#1.base|) 4294967295) 4294967296) 0) (<= (+ 29 |aws_byte_cursor_advance_nospec_~cursor#1.base|) |#StackAllocations|))";
		final String expectedResultAsString = "(and (<= (+ 29 |aws_byte_cursor_advance_nospec_~cursor#1.base|) |#StackAllocations|) (<= (mod (select |#memory_int| |aws_byte_cursor_advance_nospec_~cursor#1.base|) 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a5af6a8b_c7fed0a4_Treesizes_29_26() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_13~0", "~var_1_8~0", "~var_1_72~0"),
		};
		final String formulaAsString = "(and (= (mod ~var_1_13~0 256) 0) (or (= (mod ~var_1_72~0 256) 0) (< 0 ~var_1_8~0)) (or (and (= ~var_1_8~0 1) (not (= (mod ~var_1_72~0 256) 0))) (= ~var_1_8~0 0)))";
		final String expectedResultAsString = "(and (let ((.cse0 (= (mod ~var_1_72~0 256) 0))) (or (and .cse0 (= ~var_1_8~0 0)) (and (= ~var_1_8~0 1) (not .cse0)))) (= (mod ~var_1_13~0 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a5e965ed_3db376ad_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_~src#1.base_BEFORE_CALL_15| Int)) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_~src#1.base_BEFORE_CALL_15| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_36| Int)) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_36| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a64ae335_8379dd78_Treesizes_15_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_from_c_str_~c_str#1.base", "ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| |ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base|) 0) (exists ((|v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_1| Int)) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_1|) 0)) (= |ULTIMATE.start_aws_byte_buf_from_c_str_~c_str#1.base| 0))";
		final String expectedResultAsString = "(and (= (select |#memory_int| |ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base|) 0) (= |ULTIMATE.start_aws_byte_buf_from_c_str_~c_str#1.base| 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a6fcce4c_378f1630_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_8_Pointer~0.base", "~#var_1_14~0.base", "~#var_1_15~0.base", "~#var_1_16~0.base"),
		};
		final String formulaAsString = "(and (not (= ~var_1_8_Pointer~0.base |~#var_1_16~0.base|)) (forall ((v_ArrVal_626 Int)) (<= (mod (select (store |#memory_int| |~#var_1_14~0.base| v_ArrVal_626) ~var_1_8_Pointer~0.base) 256) 0)) (not (= ~var_1_8_Pointer~0.base |~#var_1_15~0.base|)))";
		final String expectedResultAsString = "(and (<= (mod (select |#memory_int| ~var_1_8_Pointer~0.base) 256) 0) (not (= ~var_1_8_Pointer~0.base |~#var_1_16~0.base|)) (not (= ~var_1_8_Pointer~0.base |~#var_1_15~0.base|)) (not (= |~#var_1_14~0.base| ~var_1_8_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a74fe8c4_69e72e9b_Treesizes_21_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_3| Int) (|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base_BEFORE_CALL_5| Int)) (and (= (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base_BEFORE_CALL_5|)) 0) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_3| 8) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base_BEFORE_CALL_5|) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_3| 4)) 0)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2| Int) (|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base_BEFORE_CALL_4| Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2| 8) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base_BEFORE_CALL_4|) (= (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~b#1.base_BEFORE_CALL_4|)) 0) (= 0 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2| 4)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a7ddbf61_b863cc6d_Treesizes_41_32() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_linked_list_is_valid_aws_linked_list_is_valid_deep_~temp~0#1.base", "aws_linked_list_is_valid_#in~list#1.base"),
		};
		final String formulaAsString = "(and (= |aws_linked_list_is_valid_#in~list#1.base| |aws_linked_list_is_valid_aws_linked_list_is_valid_deep_~temp~0#1.base|) (not (= (select |#memory_$Pointer$.base| (+ |aws_linked_list_is_valid_#in~list#1.base| 12)) 0)) (exists ((|v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_34| Int)) (and (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_34|) (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_34| 12))) (<= (+ (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_34| 12)) 26) |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_34|))) (exists ((|v_aws_linked_list_is_valid_aws_linked_list_is_valid_deep_~temp~0#1.base_BEFORE_CALL_1| Int)) (not (= (select |#memory_$Pointer$.base| (+ |v_aws_linked_list_is_valid_aws_linked_list_is_valid_deep_~temp~0#1.base_BEFORE_CALL_1| 12)) 0))))";
		final String expectedResultAsString = "(and (= |aws_linked_list_is_valid_#in~list#1.base| |aws_linked_list_is_valid_aws_linked_list_is_valid_deep_~temp~0#1.base|) (not (= (select |#memory_$Pointer$.base| (+ |aws_linked_list_is_valid_#in~list#1.base| 12)) 0)) (exists ((|v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_34| Int)) (let ((.cse0 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_34| 12)))) (and (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_34|) .cse0) (<= (+ .cse0 26) |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_34|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a84a6f35_b24ea5d1_Treesizes_23_23() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_3~0", "~var_1_73~0", "~var_1_9~0"),
		};
		final String formulaAsString = "(and (= (div ~var_1_9~0 256) (div ~var_1_3~0 256)) (<= ~var_1_3~0 ~var_1_9~0) (<= (mod ~var_1_9~0 256) (mod ~var_1_3~0 256)) (= (div ~var_1_73~0 4294967296) 0))";
		final String expectedResultAsString = "(let ((.cse0 (mod ~var_1_9~0 256))) (and (<= ~var_1_9~0 (+ .cse0 ~var_1_3~0)) (<= ~var_1_3~0 ~var_1_9~0) (<= .cse0 (mod ~var_1_3~0 256)) (= (div ~var_1_73~0 4294967296) 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a912ef8_e815a60e_Treesizes_27_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_satisfies_pred_harness_~#cur~3#1.base", "#StackAllocations"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_satisfies_pred_harness_~#cur~3#1.base_BEFORE_CALL_28| Int)) (and (<= 8690 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_satisfies_pred_harness_~#cur~3#1.base_BEFORE_CALL_28|))) (<= (+ 8 |v_ULTIMATE.start_aws_byte_cursor_satisfies_pred_harness_~#cur~3#1.base_BEFORE_CALL_28|) |#StackAllocations|))) (<= (+ |ULTIMATE.start_aws_byte_cursor_satisfies_pred_harness_~#cur~3#1.base| 8) |#StackAllocations|) (<= 8690 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_satisfies_pred_harness_~#cur~3#1.base| 4))))";
		final String expectedResultAsString = "(and (<= (+ |ULTIMATE.start_aws_byte_cursor_satisfies_pred_harness_~#cur~3#1.base| 8) |#StackAllocations|) (<= 8690 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_satisfies_pred_harness_~#cur~3#1.base| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a941209b_bc685662_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_18| Int)) (and (<= 8688 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_18|))) (<= (+ 2 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_18|))) |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_18|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_46| Int)) (let ((.cse0 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_46| 4)))) (and (<= (+ 2 .cse0) |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_46|) (<= 8688 .cse0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a9c9308f_1326d0b5_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_38| Int)) (and (<= (+ 16 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_38|) |#StackAllocations|) (<= 58 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_38|)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_35| Int)) (and (<= 58 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_35|))) (<= (+ 16 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_35|) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_aa2e80bd_a821cee6_Treesizes_31_27() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base", "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~a~0#1.base", "ULTIMATE.start_main_~p~0#1.base", "#HeapAllocations"),
		};
		final String formulaAsString = "(and (or (= (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 1) (= |ULTIMATE.start_main_~a~0#1.base| |ULTIMATE.start_main_~p~0#1.base|)) (<= (+ |ULTIMATE.start_main_~a~0#1.base| 8) (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_main_~a~0#1.base| 4))) (<= (+ 16 |ULTIMATE.start_main_~a~0#1.base|) |#HeapAllocations|) (<= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_main_~a~0#1.base| 4)) |ULTIMATE.start_main_~p~0#1.base|))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_main_~a~0#1.base| 4)))) (and (<= (+ |ULTIMATE.start_main_~a~0#1.base| 8) .cse0) (= (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 1) (<= (+ 16 |ULTIMATE.start_main_~a~0#1.base|) |#HeapAllocations|) (<= .cse0 |ULTIMATE.start_main_~p~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_aa9ab13b_97cdeafe_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0", "~last_1_var_1_24~0", "~var_1_8~0"),
		};
		final String formulaAsString = "(and (= (div ~var_1_1~0 65536) 0) (<= (mod ~var_1_8~0 4294967296) (+ ~last_1_var_1_24~0 4294967287)) (<= (+ 2147483575 ~var_1_1~0 ~last_1_var_1_24~0) (mod ~var_1_8~0 4294967296)) (<= 64 ~var_1_1~0))";
		final String expectedResultAsString = "(let ((.cse0 (mod ~var_1_8~0 4294967296))) (and (<= .cse0 (+ ~last_1_var_1_24~0 4294967287)) (<= (+ 2147483575 ~var_1_1~0 ~last_1_var_1_24~0) .cse0) (<= (div ~var_1_1~0 65536) 0) (<= 64 ~var_1_1~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ab1f0bb7_768414d0_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_59| Int)) (and (<= (+ 16 |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_59|) |#StackAllocations|) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_59| 4)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_57| Int)) (and (<= (+ 16 |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_57|) |#StackAllocations|) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_57| 4)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ab8551f7_4ba65f36_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_10| Int)) (<= 8688 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_10|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_33| Int)) (<= 8688 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_33| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_aba768fa_2f1b0685_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_back_~list#1.base_BEFORE_CALL_6| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_back_~list#1.base_BEFORE_CALL_6| 8)) 0))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_35| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_35| 8)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_abbb17e7_95d59d6_Treesizes_23_21() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~x$r_buff0_thd1~0", "~x$w_buff0_used~0", "~x$r_buff1_thd1~0", "~x$r_buff1_thd0~0", "~x$r_buff0_thd0~0"),
		};
		final String formulaAsString = "(and (<= 0 (div ~x$w_buff0_used~0 256)) (<= (mod ~x$w_buff0_used~0 256) 0) (= 0 ~x$r_buff0_thd1~0) (= ~x$r_buff1_thd0~0 0) (= 0 ~x$r_buff0_thd0~0) (= ~x$r_buff1_thd1~0 0))";
		final String expectedResultAsString = "(and (<= (mod ~x$w_buff0_used~0 256) 0) (= 0 ~x$r_buff0_thd1~0) (= ~x$r_buff1_thd0~0 0) (<= 0 ~x$w_buff0_used~0) (= 0 ~x$r_buff0_thd0~0) (= ~x$r_buff1_thd1~0 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ac140b0f_7402d6d6_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#to~0#1.base_BEFORE_CALL_18| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#to~0#1.base_BEFORE_CALL_18| 12)) 0))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#to~0#1.base_BEFORE_CALL_17| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#to~0#1.base_BEFORE_CALL_17| 12)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ac6b2b99_aa48481c_Treesizes_80_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~item~0#1.base", "#HeapAllocations", "ULTIMATE.start_main_~node~1#1.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~node~1#1.base|) 0) (forall ((|v_ULTIMATE.start_main_~node~1#1.base_21| Int) (v_ArrVal_353 Int) (v_ArrVal_352 Int) (v_ArrVal_350 Int)) (or (= (select (store (store (store (store (store (store |#memory_$Pointer$.base| |ULTIMATE.start_main_~item~0#1.base| |ULTIMATE.start_main_~node~1#1.base|) (+ |ULTIMATE.start_main_~item~0#1.base| 4) v_ArrVal_350) |v_ULTIMATE.start_main_~node~1#1.base_21| 0) (+ |v_ULTIMATE.start_main_~node~1#1.base_21| 4) v_ArrVal_352) (+ |#HeapAllocations| 8) v_ArrVal_353) (+ |#HeapAllocations| 12) |ULTIMATE.start_main_~item~0#1.base|) (select (store (store (store (store (store (store |#memory_$Pointer$.base| |ULTIMATE.start_main_~item~0#1.base| |ULTIMATE.start_main_~node~1#1.base|) (+ |ULTIMATE.start_main_~item~0#1.base| 4) v_ArrVal_350) |v_ULTIMATE.start_main_~node~1#1.base_21| 0) (+ |v_ULTIMATE.start_main_~node~1#1.base_21| 4) v_ArrVal_352) (+ |#HeapAllocations| 8) v_ArrVal_353) (+ |#HeapAllocations| 12) |ULTIMATE.start_main_~item~0#1.base|) |ULTIMATE.start_main_~item~0#1.base|)) 0) (< |v_ULTIMATE.start_main_~node~1#1.base_21| |#HeapAllocations|))) (= |ULTIMATE.start_main_~item~0#1.base| (+ 8 |ULTIMATE.start_main_~node~1#1.base|)) (= |#HeapAllocations| (+ 16 |ULTIMATE.start_main_~node~1#1.base|)))";
		final String expectedResultAsString = "(and (= (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~node~1#1.base|) 0) (= |ULTIMATE.start_main_~item~0#1.base| (+ 8 |ULTIMATE.start_main_~node~1#1.base|)) (= |#HeapAllocations| (+ 16 |ULTIMATE.start_main_~node~1#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ad0861a8_49c4bb72_Treesizes_12_11() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_32~0", "~var_1_14~0"),
		};
		final String formulaAsString = "(and (<= (mod ~var_1_14~0 65536) 0) (not (= (mod ~var_1_32~0 256) 0)))";
		final String expectedResultAsString = "(and (<= 1 (mod ~var_1_32~0 256)) (<= (mod ~var_1_14~0 65536) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_add5f20_92a1ba03_Treesizes_50_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_3_Pointer~0.base", "~var_1_13_Pointer~0.base", "~var_1_1_Pointer~0.base"),
		};
		final String formulaAsString = "(and (<= (+ (mod (select |#memory_int| ~var_1_1_Pointer~0.base) 4294967296) (mod (+ (select |#memory_int| ~var_1_3_Pointer~0.base) (* 4294967295 (select |#memory_int| ~var_1_1_Pointer~0.base))) 4294967296)) 4294967295) (not (= ~var_1_3_Pointer~0.base ~var_1_13_Pointer~0.base)) (not (= ~var_1_13_Pointer~0.base ~var_1_1_Pointer~0.base)) (<= (select |#memory_int| ~var_1_3_Pointer~0.base) (select |#memory_int| ~var_1_1_Pointer~0.base)) (<= (+ (mod (select |#memory_int| ~var_1_3_Pointer~0.base) 4294967296) (select |#memory_int| ~var_1_1_Pointer~0.base)) (+ 32766 (select |#memory_int| ~var_1_3_Pointer~0.base))))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| ~var_1_3_Pointer~0.base))) (and (not (= ~var_1_3_Pointer~0.base ~var_1_13_Pointer~0.base)) (not (= ~var_1_13_Pointer~0.base ~var_1_1_Pointer~0.base)) (<= (mod .cse0 4294967296) 32766) (= .cse0 (select |#memory_int| ~var_1_1_Pointer~0.base))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ae3c2ff2_c028497d_Treesizes_19_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_from_array_harness_~length~2#1", "ULTIMATE.start_aws_byte_cursor_from_array_harness_~#cur~3#1.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_from_array_harness_~#cur~3#1.base|) |ULTIMATE.start_aws_byte_cursor_from_array_harness_~length~2#1|) (exists ((|v_ULTIMATE.start_aws_byte_cursor_from_array_~#cur~2#1.base_BEFORE_CALL_5| Int)) (<= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_from_array_~#cur~2#1.base_BEFORE_CALL_5|) 4294967296) 0)) (<= (mod |ULTIMATE.start_aws_byte_cursor_from_array_harness_~length~2#1| 4294967296) 0))";
		final String expectedResultAsString = "(and (= (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_from_array_harness_~#cur~3#1.base|) |ULTIMATE.start_aws_byte_cursor_from_array_harness_~length~2#1|) (<= (mod |ULTIMATE.start_aws_byte_cursor_from_array_harness_~length~2#1| 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_aef53cfc_e566db5_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_from_whole_buffer_harness_~#buf~3#1.base_BEFORE_CALL_55| Int)) (and (<= 8696 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_write_from_whole_buffer_harness_~#buf~3#1.base_BEFORE_CALL_55| 4))) (<= (+ 32 |v_ULTIMATE.start_aws_byte_buf_write_from_whole_buffer_harness_~#buf~3#1.base_BEFORE_CALL_55|) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_from_whole_buffer_harness_~#buf~3#1.base_BEFORE_CALL_49| Int)) (and (<= 8696 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_write_from_whole_buffer_harness_~#buf~3#1.base_BEFORE_CALL_49| 4))) (<= (+ 32 |v_ULTIMATE.start_aws_byte_buf_write_from_whole_buffer_harness_~#buf~3#1.base_BEFORE_CALL_49|) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_af9f0d6_dc8fc898_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_78~0"),
		};
		final String formulaAsString = "(= (mod ~var_1_78~0 256) 0)";
		final String expectedResultAsString = "(<= (mod ~var_1_78~0 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b01d60ed_62863aa5_Treesizes_165_84() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| Int) (v_DerPreprocessor_4 Int) (v_DerPreprocessor_3 Int) (v_y_7 Int)) (and (= (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| 4)) (select (store (store (store |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| (* v_y_7 (- 4294967296)) 8 (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| 4))) v_DerPreprocessor_4) (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| 4) v_DerPreprocessor_3) (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| (* v_y_7 (- 4294967296)) (- 4294967288) (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| 4))) 0) (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| 4))) (= (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| (* v_y_7 (- 4294967296)) 8 (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| 4)))) 0) (<= 316 |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20|) (<= (* v_y_7 4294967296) (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| 4))) (<= (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| 4)) (+ (* v_y_7 4294967296) 15)))) (exists ((v_y_6 Int) (|v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26| Int) (v_DerPreprocessor_2 Int) (v_DerPreprocessor_1 Int)) (and (<= (* v_y_6 4294967296) (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26| 4))) (= (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26| 8 (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26| 4)) (* v_y_6 (- 4294967296)))) 0) (= (select (store (store (store |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26| 8 (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26| 4)) (* v_y_6 (- 4294967296))) v_DerPreprocessor_1) (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26| 4) v_DerPreprocessor_2) (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26| (- 4294967288) (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26| 4)) (* v_y_6 (- 4294967296))) 0) (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26| 4)) (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26| 4))) (<= (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26| 4)) (+ (* v_y_6 4294967296) 15)) (<= 316 |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_26|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| Int)) (and (<= 316 |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20|) (exists ((v_y_6 Int) (v_DerPreprocessor_2 Int) (v_DerPreprocessor_1 Int)) (let ((.cse3 (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| 4))) (let ((.cse4 (* v_y_6 (- 4294967296))) (.cse0 (select |#memory_int| .cse3))) (let ((.cse1 (* v_y_6 4294967296)) (.cse2 (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| 8 .cse4 .cse0))) (and (<= .cse0 (+ .cse1 15)) (<= .cse1 .cse0) (= (select (store (store (store |#memory_int| .cse2 v_DerPreprocessor_1) .cse3 v_DerPreprocessor_2) (+ |v_ULTIMATE.start_aws_string_eq_harness_~str_a~1#1.base_BEFORE_CALL_20| (- 4294967288) .cse4 .cse0) 0) .cse3) .cse0) (= (select |#memory_int| .cse2) 0))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b0ac38ee_856ea12c_Treesizes_299_234() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_12~0", "~var_1_1~0", "~var_1_4~0", "~var_1_5~0", "~var_1_3~0", "~var_1_13~0", "~var_1_8~0", "~var_1_9~0", "~var_1_18~0", "~var_1_6~0", "~var_1_7~0"),
		};
		final String formulaAsString = "(and (<= (+ ~var_1_4~0 17) 0) (or (and (<= (+ ~var_1_8~0 1) 0) (or (< (+ (div ~var_1_5~0 ~var_1_7~0) 5) 0) (and (or (< 0 (+ ~var_1_5~0 1)) (= (mod ~var_1_5~0 ~var_1_7~0) 0)) (= (+ (div ~var_1_5~0 ~var_1_7~0) 5) 0)))) (and (<= (+ ~var_1_8~0 1) ~var_1_7~0) (or (< (+ (div ~var_1_5~0 ~var_1_7~0) 5) 0) (and (= (+ (div ~var_1_5~0 ~var_1_7~0) 5) 0) (= (mod ~var_1_5~0 ~var_1_7~0) 0)))) (and (or (and (or (< 0 (+ ~var_1_5~0 1)) (= (mod ~var_1_5~0 ~var_1_8~0) 0)) (= (+ 5 (div ~var_1_5~0 ~var_1_8~0)) 0)) (< (+ 5 (div ~var_1_5~0 ~var_1_8~0)) 0)) (<= ~var_1_7~0 ~var_1_8~0))) (or (and (or (= (+ 5 ~var_1_13~0) 0) (and (or (= (mod (+ ~var_1_4~0 ~var_1_3~0) 256) ~var_1_13~0) (< (mod ~var_1_18~0 4294967296) (+ (mod (+ (* 4294967295 ~var_1_3~0) 4294967295) 4294967296) 1))) (or (< 0 (+ 5 ~var_1_4~0 ~var_1_3~0)) (< (mod ~var_1_18~0 4294967296) (+ (mod (+ (* 4294967295 ~var_1_3~0) 4294967295) 4294967296) 1))))) (or (not (= (+ 5 ~var_1_13~0) 0)) (< (+ ~var_1_4~0 ~var_1_3~0 4) 0) (< (mod ~var_1_18~0 4294967296) (+ (mod (+ (* 4294967295 ~var_1_3~0) 4294967295) 4294967296) 1)))) (< 127 (mod (+ ~var_1_4~0 ~var_1_3~0) 256))) (<= ~var_1_3~0 ~var_1_1~0) (or (< (mod (+ ~var_1_4~0 ~var_1_3~0) 256) 128) (and (or (not (= (+ 5 ~var_1_13~0) 0)) (= 251 (mod (+ ~var_1_4~0 ~var_1_3~0) 256)) (< (+ ~var_1_4~0 ~var_1_3~0 4) 0) (< (mod ~var_1_18~0 4294967296) (+ (mod (+ (* 4294967295 ~var_1_3~0) 4294967295) 4294967296) 1))) (or (= (+ 5 ~var_1_13~0) 0) (and (or (= (+ 256 ~var_1_13~0) (mod (+ ~var_1_4~0 ~var_1_3~0) 256)) (< (mod ~var_1_18~0 4294967296) (+ (mod (+ (* 4294967295 ~var_1_3~0) 4294967295) 4294967296) 1))) (or (< 0 (+ 5 ~var_1_4~0 ~var_1_3~0)) (< (mod ~var_1_18~0 4294967296) (+ (mod (+ (* 4294967295 ~var_1_3~0) 4294967295) 4294967296) 1))))))) (<= ~var_1_12~0 ~var_1_4~0) (= 32 ~var_1_6~0) (= (+ (div ~var_1_12~0 4294967296) 1) 0) (<= (mod ~var_1_4~0 4294967296) (mod ~var_1_12~0 4294967296)) (= ~var_1_4~0 ~var_1_9~0))";
		final String expectedResultAsString = "(and (<= (+ ~var_1_4~0 17) 0) (= ~var_1_4~0 ~var_1_12~0) (let ((.cse4 (+ ~var_1_4~0 ~var_1_3~0 4)) (.cse0 (= (+ 5 ~var_1_13~0) 0)) (.cse3 (+ 5 ~var_1_4~0 ~var_1_3~0)) (.cse1 (mod (+ ~var_1_4~0 ~var_1_3~0) 256))) (or (let ((.cse2 (< (mod ~var_1_18~0 4294967296) (+ (mod (+ (* 4294967295 ~var_1_3~0) 4294967295) 4294967296) 1)))) (and (or .cse0 (and (or (= .cse1 ~var_1_13~0) .cse2) (or (< 0 .cse3) .cse2))) (or (< .cse1 128) .cse2) (or (not .cse0) (< .cse4 0) .cse2))) (and (or (and (<= 0 .cse4) (= (+ 256 ~var_1_13~0) .cse1)) (and .cse0 (<= .cse3 0))) (<= 128 .cse1)))) (<= ~var_1_3~0 ~var_1_1~0) (= (+ (div ~var_1_4~0 4294967296) 1) 0) (= 32 ~var_1_6~0) (let ((.cse6 (+ (div ~var_1_5~0 ~var_1_7~0) 5))) (let ((.cse5 (+ ~var_1_8~0 1)) (.cse7 (= .cse6 0))) (or (and (<= .cse5 ~var_1_7~0) (or (< .cse6 0) (and .cse7 (= (mod ~var_1_5~0 ~var_1_7~0) 0)))) (and (<= .cse5 0) .cse7 (<= 0 ~var_1_5~0)) (and (let ((.cse8 (+ 5 (div ~var_1_5~0 ~var_1_8~0)))) (or (and (or (< 0 (+ ~var_1_5~0 1)) (= (mod ~var_1_5~0 ~var_1_8~0) 0)) (= .cse8 0)) (< .cse8 0))) (<= ~var_1_7~0 ~var_1_8~0))))) (= ~var_1_4~0 ~var_1_9~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b129a9f0_feabc673_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_39| Int)) (and (<= 8690 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_39| 4))) (<= (+ 8 |v_ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_39|) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_38| Int)) (and (<= (+ 8 |v_ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_38|) |#StackAllocations|) (<= 8690 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_38| 4)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b24dbe0_7e791a8d_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_back_~list#1.base_BEFORE_CALL_7| Int)) (and (<= 72 |v_ULTIMATE.start_aws_linked_list_back_~list#1.base_BEFORE_CALL_7|) (<= |v_ULTIMATE.start_aws_linked_list_back_~list#1.base_BEFORE_CALL_7| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_back_~list#1.base_BEFORE_CALL_7| 12)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_19| Int)) (and (<= 72 |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_19|) (<= |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_19| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_19| 12)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b25fcbaa_765577bb_Treesizes_28_28() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_8_Pointer~0.base", "~#var_1_13~0.base", "~#var_1_12~0.base", "~#var_1_14~0.base", "~#var_1_15~0.base", "~#var_1_16~0.base"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_624 Int)) (<= (mod (select (store |#memory_int| |~#var_1_12~0.base| v_ArrVal_624) ~var_1_8_Pointer~0.base) 256) 0)) (not (= ~var_1_8_Pointer~0.base |~#var_1_16~0.base|)) (not (= ~var_1_8_Pointer~0.base |~#var_1_13~0.base|)) (not (= ~var_1_8_Pointer~0.base |~#var_1_15~0.base|)) (not (= |~#var_1_14~0.base| ~var_1_8_Pointer~0.base)))";
		final String expectedResultAsString = "(and (<= (mod (select |#memory_int| ~var_1_8_Pointer~0.base) 256) 0) (not (= ~var_1_8_Pointer~0.base |~#var_1_16~0.base|)) (not (= ~var_1_8_Pointer~0.base |~#var_1_13~0.base|)) (not (= ~var_1_8_Pointer~0.base |~#var_1_15~0.base|)) (not (= |~#var_1_12~0.base| ~var_1_8_Pointer~0.base)) (not (= |~#var_1_14~0.base| ~var_1_8_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b28aae5a_3ce57b41_Treesizes_85_85() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(or (exists ((v_y_4 Int) (|v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_14| Int)) (and (<= (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_14|)) (+ (* v_y_4 4294967296) 4294967295)) (<= (+ (* v_y_4 4294967296) 2147483648) (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_14|))) (= (select |#memory_int| (+ (- 4294967288) (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_14|)) (* v_y_4 (- 4294967296)) |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_14|)) 0))) (exists ((|v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_14| Int)) (= (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_14|)) 0)) (exists ((|v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_14| Int) (v_y_1 Int)) (and (<= (* v_y_1 4294967296) (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_14|))) (<= (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_14|)) (+ 2147483647 (* v_y_1 4294967296))) (= (select |#memory_int| (+ (* v_y_1 (- 4294967296)) 8 (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_14|)) |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_14|)) 0))))";
		final String expectedResultAsString = "(or (exists ((v_y_4 Int) (|v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_11| Int)) (let ((.cse0 (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_11|))) (.cse1 (* v_y_4 4294967296))) (and (= (select |#memory_int| (+ .cse0 (- 4294967288) (* v_y_4 (- 4294967296)) |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_11|)) 0) (<= (+ .cse1 2147483648) .cse0) (<= .cse0 (+ .cse1 4294967295))))) (exists ((|v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_11| Int) (v_y_1 Int)) (let ((.cse3 (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_11|))) (.cse2 (* v_y_1 4294967296))) (and (<= .cse2 .cse3) (= (select |#memory_int| (+ (* v_y_1 (- 4294967296)) 8 .cse3 |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_11|)) 0) (<= .cse3 (+ 2147483647 .cse2))))) (exists ((|v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_11| Int)) (= (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_c_str_harness_~str~3#1.base_BEFORE_CALL_11|)) 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b2c015c6_4b86f5fb_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~z~0#1| Int)) (= (+ (* |ULTIMATE.start_main_~y~0#1| |ULTIMATE.start_main_~z~0#1| |ULTIMATE.start_main_~z~0#1|) (* |ULTIMATE.start_main_~x~0#1| |ULTIMATE.start_main_~z~0#1|)) (+ (* |ULTIMATE.start_main_~x~0#1| |ULTIMATE.start_main_~z~0#1| |ULTIMATE.start_main_~z~0#1|) |ULTIMATE.start_main_~z~0#1|)))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_main_~x~0#1| 1) (= |ULTIMATE.start_main_~y~0#1| 1))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b328f5b3_aefc4685_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_19| Int)) (<= (mod (+ 4294967295 (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_19| 8))) 4294967296) 4294967294))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_15| Int)) (<= (mod (+ 4294967295 (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_15| 8))) 4294967296) 4294967294))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b37b83f5_6eaf5397_Treesizes_50_50() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "old(#memory_$Pointer$.base)", "#memory_$Pointer$.base", "old(#memory_int)", "#memory_int"),
		};
		final String formulaAsString = "(and (forall ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_22| Int)) (or (not (= (select |old(#memory_$Pointer$.base)| (+ |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_22| 4)) 0)) (not (= 0 (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_22|) 4294967296))) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_22| 4)) 0))) (forall ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_22| Int)) (or (= (mod (select |old(#memory_int)| |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_22|) 4294967296) 0) (not (= 0 (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_22|) 4294967296))) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_22| 4)) 0))))";
		final String expectedResultAsString = "(and (forall ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_21| Int)) (let ((.cse0 (+ |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_21| 4))) (or (not (= (select |old(#memory_$Pointer$.base)| .cse0) 0)) (= (select |#memory_$Pointer$.base| .cse0) 0) (not (= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_21|) 4294967296) 0))))) (forall ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_21| Int)) (or (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_21| 4)) 0) (not (= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_21|) 4294967296) 0)) (= (mod (select |old(#memory_int)| |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#rhs~0#1.base_BEFORE_CALL_21|) 4294967296) 0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b3d60373_3736c112_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_remove_~node#1.base_BEFORE_CALL_4| Int)) (and (<= 70 (select |#memory_$Pointer$.base| (+ |v_aws_linked_list_remove_~node#1.base_BEFORE_CALL_4| 4))) (<= (+ (select |#memory_$Pointer$.base| (+ |v_aws_linked_list_remove_~node#1.base_BEFORE_CALL_4| 4)) 16) |v_aws_linked_list_remove_~node#1.base_BEFORE_CALL_4|)))";
		final String expectedResultAsString = "(exists ((|v_aws_linked_list_remove_~node#1.base_BEFORE_CALL_1| Int)) (let ((.cse0 (select |#memory_$Pointer$.base| (+ |v_aws_linked_list_remove_~node#1.base_BEFORE_CALL_1| 4)))) (and (<= (+ 16 .cse0) |v_aws_linked_list_remove_~node#1.base_BEFORE_CALL_1|) (<= 70 .cse0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b40b2e3f_85133f85_Treesizes_98_93() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0", "~var_1_4~0", "~var_1_5~0", "~last_1_var_1_10~0", "~last_1_var_1_13~0", "~var_1_13~0", "~var_1_8~0", "~var_1_9~0", "~var_1_7~0"),
		};
		final String formulaAsString = "(and (or (and (or (< (* ~var_1_1~0 ~var_1_1~0 ~var_1_13~0) (+ (* 256 (* (div ~var_1_13~0 256) ~var_1_1~0 ~var_1_1~0)) ~var_1_1~0)) (= (mod (+ ~var_1_8~0 ~var_1_7~0) 256) (mod ~var_1_5~0 256))) (or (< (+ (* 256 (* (div ~var_1_13~0 256) ~var_1_1~0 ~var_1_1~0)) ~var_1_1~0) (+ (* ~var_1_1~0 ~var_1_1~0 ~var_1_13~0) 1)) (= (mod ~var_1_7~0 256) (mod ~var_1_5~0 256)))) (and (= (mod (+ ~var_1_8~0 ~var_1_7~0) 256) (mod ~var_1_5~0 256)) (<= (+ (mod ~var_1_7~0 256) (mod ~var_1_8~0 256) (mod ~var_1_5~0 256)) (+ 255 ~var_1_5~0))) (and (not (= (+ ~var_1_1~0 1) 0)) (<= (+ 257 ~var_1_4~0) (+ (mod ~last_1_var_1_13~0 256) (mod ~last_1_var_1_10~0 256))))) (= ~var_1_9~0 1))";
		final String expectedResultAsString = "(and (= ~var_1_9~0 1) (let ((.cse4 (mod ~var_1_5~0 256))) (let ((.cse2 (= (mod (+ ~var_1_8~0 ~var_1_7~0) 256) .cse4)) (.cse3 (mod ~var_1_7~0 256))) (or (let ((.cse1 (+ (* 256 (* (div ~var_1_13~0 256) ~var_1_1~0 ~var_1_1~0)) ~var_1_1~0)) (.cse0 (* ~var_1_1~0 ~var_1_1~0 ~var_1_13~0))) (and (or (< .cse0 .cse1) .cse2) (or (< .cse1 (+ .cse0 1)) (= .cse3 .cse4)))) (and (not (= (+ ~var_1_1~0 1) 0)) (<= (+ 257 ~var_1_4~0) (+ (mod ~last_1_var_1_13~0 256) (mod ~last_1_var_1_10~0 256)))) (and .cse2 (<= (+ .cse3 (mod ~var_1_8~0 256)) ~var_1_5~0))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b4fb9914_8b7a09a3_Treesizes_21_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_write_be64_~#x#1.base", "ULTIMATE.start_aws_byte_buf_write_be64_~buf#1.base"),
		};
		final String formulaAsString = "(and (<= 8683 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_write_be64_~buf#1.base| 4))) (<= (+ |ULTIMATE.start_aws_byte_buf_write_be64_~buf#1.base| 37) |ULTIMATE.start_aws_byte_buf_write_be64_~#x#1.base|) (exists ((|v_ULTIMATE.start_aws_byte_buf_write_be64_~buf#1.base_BEFORE_CALL_5| Int)) (<= 8683 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_write_be64_~buf#1.base_BEFORE_CALL_5| 4)))))";
		final String expectedResultAsString = "(and (<= 8683 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_write_be64_~buf#1.base| 4))) (<= (+ |ULTIMATE.start_aws_byte_buf_write_be64_~buf#1.base| 37) |ULTIMATE.start_aws_byte_buf_write_be64_~#x#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b5b61370_104871eb_Treesizes_12_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_10_Pointer~0.base", "~var_1_4_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~var_1_10_Pointer~0.base ~var_1_4_Pointer~0.base)) (<= (mod (select |#memory_int| ~var_1_4_Pointer~0.base) 256) 0))";
		final String expectedResultAsString = "(forall ((v_ArrVal_261 Int)) (<= (mod (select (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_261) ~var_1_4_Pointer~0.base) 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b6181d9b_acecb39f_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~var_19_arg_0~0#1"),
		};
		final String formulaAsString = "(= (mod |ULTIMATE.start_main_~var_19_arg_0~0#1| 256) 0)";
		final String expectedResultAsString = "(<= (mod |ULTIMATE.start_main_~var_19_arg_0~0#1| 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b6849b68_5b986a8_Treesizes_182_119() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base", "ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base", "ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~cur#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~cur#1.base_BEFORE_CALL_3| Int)) (= (mod (select |#memory_int| |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~cur#1.base_BEFORE_CALL_3|) 4294967296) 0)) (or (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| Int)) (and (= (mod (select |#memory_int| (+ (mod (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| 4)) 4294967296) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| (- 4294967288))) 256) 0) (<= 2147483648 (mod (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| 4)) 4294967296)))) (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| Int)) (and (= (mod (select |#memory_int| (+ (mod (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| 4)) 4294967296) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| 8)) 256) 0) (<= (mod (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base_BEFORE_CALL_14| 4)) 4294967296) 2147483647)))) (= |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base| |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base|) (= (mod (select |#memory_int| |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~cur#1.base|) 4294967296) 0) (or (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5| Int)) (and (= (mod (select |#memory_int| (+ (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 4294967296) (- 4294967288) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 256) 0) (<= 2147483648 (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 4294967296)))) (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5| Int)) (and (= (mod (select |#memory_int| (+ (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 4294967296) 8 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 256) 0) (<= (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 4294967296) 2147483647)))) (or (and (= (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base| 8 (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base| 4)) 4294967296))) 256) 0) (<= (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base| 4)) 4294967296) 2147483647)) (and (= 0 (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base| (- 4294967288) (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base| 4)) 4294967296))) 256)) (<= 2147483648 (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base| 4)) 4294967296)))))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~str~3#1.base| |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base|) (= (mod (select |#memory_int| |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~cur#1.base|) 4294967296) 0) (or (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5| Int)) (let ((.cse0 (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 4294967296))) (and (= (mod (select |#memory_int| (+ .cse0 (- 4294967288) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 256) 0) (<= 2147483648 .cse0)))) (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5| Int)) (let ((.cse1 (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 4294967296))) (and (= (mod (select |#memory_int| (+ .cse1 8 |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base_BEFORE_CALL_5|)) 256) 0) (<= .cse1 2147483647))))) (let ((.cse2 (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base| 4)) 4294967296))) (or (and (= (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base| 8 .cse2)) 256) 0) (<= .cse2 2147483647)) (and (= 0 (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_~str#1.base| (- 4294967288) .cse2)) 256)) (<= 2147483648 .cse2)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b6e0ce88_304aab1a_Treesizes_230_225() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~last_1_var_1_17~0", "~var_1_11~0", "~var_1_10~0", "~var_1_4~0", "~last_1_var_1_11~0", "~var_1_16~0", "~var_1_5~0", "~var_1_14~0", "~last_1_var_1_13~0", "~last_1_var_1_12~0", "~var_1_13~0", "~var_1_8~0", "~var_1_19~0", "~var_1_9~0", "~var_1_18~0", "~var_1_6~0", "~last_1_var_1_18~0", "~last_1_var_1_1~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (or (and (or (not (= (mod ~var_1_8~0 256) 0)) (and (not (= (mod ~last_1_var_1_12~0 256) 0)) (not (= (mod ~var_1_9~0 256) 0))) (= (mod ~var_1_6~0 256) 0)) (or (and (or (= (mod ~last_1_var_1_12~0 256) 0) (= (mod ~var_1_9~0 256) 0)) (= (mod ~var_1_8~0 256) 0)) (= (mod ~var_1_6~0 256) 1))) (< 0 (+ ~last_1_var_1_1~0 1))) (= 0 (mod ~var_1_10~0 256)) (or (= (mod ~var_1_19~0 256) (mod ~var_1_18~0 256)) (and (= (mod ~last_1_var_1_12~0 256) 0) (= (mod ~last_1_var_1_11~0 256) 0) (or (< (* ~var_1_4~0 ~last_1_var_1_1~0) (mod ~last_1_var_1_17~0 65536)) (= (* ~var_1_4~0 ~last_1_var_1_1~0) (mod ~last_1_var_1_17~0 65536))))) (= ~var_1_11~0 0) (or (and (or (not (= (mod ~last_1_var_1_11~0 256) 0)) (< (mod ~last_1_var_1_17~0 65536) (+ (* ~var_1_4~0 ~last_1_var_1_1~0) 1)) (not (= (mod ~last_1_var_1_12~0 256) 0))) (or (not (= (mod ~last_1_var_1_11~0 256) 0)) (not (= (* ~var_1_4~0 ~last_1_var_1_1~0) (mod ~last_1_var_1_17~0 65536))) (not (= (mod ~last_1_var_1_12~0 256) 0)))) (= (mod ~var_1_18~0 256) (mod ~var_1_16~0 256))) (= (mod (+ (* (mod ~last_1_var_1_18~0 256) 65535) ~var_1_14~0) 65536) (mod ~var_1_13~0 65536)) (<= (+ (mod ~var_1_14~0 65536) (mod ~var_1_13~0 65536)) (+ (mod ~last_1_var_1_18~0 256) ~var_1_13~0 65535)) (or (and (= (mod ~last_1_var_1_12~0 256) 0) (<= (+ 5 (mod ~last_1_var_1_13~0 65536)) ~var_1_4~0) (<= (+ 5 (mod ~last_1_var_1_13~0 65536)) ~var_1_5~0) (= (+ ~var_1_1~0 128) 0)) (and (= (mod ~last_1_var_1_13~0 65536) ~var_1_1~0) (or (not (= (mod ~last_1_var_1_12~0 256) 0)) (< ~var_1_5~0 (+ 5 (mod ~last_1_var_1_13~0 65536))) (< ~var_1_4~0 (+ 5 (mod ~last_1_var_1_13~0 65536)))))))";
		final String expectedResultAsString = "(let ((.cse4 (= (mod ~last_1_var_1_12~0 256) 0)) (.cse8 (* ~var_1_4~0 ~last_1_var_1_1~0)) (.cse9 (mod ~last_1_var_1_17~0 65536))) (let ((.cse10 (= .cse8 .cse9)) (.cse7 (= (mod ~last_1_var_1_11~0 256) 0)) (.cse6 (mod ~var_1_18~0 256)) (.cse5 (mod ~last_1_var_1_18~0 256)) (.cse1 (not .cse4))) (and (or (let ((.cse2 (= (mod ~var_1_9~0 256) 0)) (.cse0 (= (mod ~var_1_8~0 256) 0)) (.cse3 (mod ~var_1_6~0 256))) (and (or (not .cse0) (and .cse1 (not .cse2)) (= .cse3 0)) (or (and (or .cse4 .cse2) .cse0) (= .cse3 1)))) (< 0 (+ ~last_1_var_1_1~0 1))) (= 0 (mod ~var_1_10~0 256)) (<= (mod ~var_1_14~0 65536) (+ .cse5 ~var_1_13~0)) (or (= (mod ~var_1_19~0 256) .cse6) (and .cse4 .cse7 (or (< .cse8 .cse9) .cse10))) (= ~var_1_11~0 0) (or (let ((.cse11 (not .cse7))) (and (or .cse11 (< .cse9 (+ .cse8 1)) .cse1) (or .cse11 (not .cse10) .cse1))) (= .cse6 (mod ~var_1_16~0 256))) (= (mod (+ (* .cse5 65535) ~var_1_14~0) 65536) (mod ~var_1_13~0 65536)) (let ((.cse13 (mod ~last_1_var_1_13~0 65536))) (let ((.cse12 (+ 5 .cse13))) (or (and .cse4 (<= .cse12 ~var_1_4~0) (<= .cse12 ~var_1_5~0) (= (+ ~var_1_1~0 128) 0)) (and (= .cse13 ~var_1_1~0) (or .cse1 (< ~var_1_5~0 .cse12) (< ~var_1_4~0 .cse12)))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b7abf19_18c7cf37_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_u8_~buf#1.base_BEFORE_CALL_16| Int)) (<= 8681 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_write_u8_~buf#1.base_BEFORE_CALL_16|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_u8_~buf#1.base_BEFORE_CALL_15| Int)) (<= 8681 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_write_u8_~buf#1.base_BEFORE_CALL_15|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b7ec7835_18b23deb_Treesizes_14_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~a~0#1.base", "ULTIMATE.start_main_~p~0#1.base"),
		};
		final String formulaAsString = "(and (not (= (+ |ULTIMATE.start_main_~a~0#1.base| 4) |ULTIMATE.start_main_~p~0#1.base|)) (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_main_~a~0#1.base| 4)) |ULTIMATE.start_main_~p~0#1.base|))";
		final String expectedResultAsString = "(forall ((v_ArrVal_81 Int)) (= (select (store |#memory_$Pointer$.base| |ULTIMATE.start_main_~p~0#1.base| v_ArrVal_81) (+ |ULTIMATE.start_main_~a~0#1.base| 4)) |ULTIMATE.start_main_~p~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b8a58a2_13c9e937_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_20 Int)) (<= 68 (select |#memory_$Pointer$.base| (+ v_aws_linked_list_front_~list.base_BEFORE_CALL_20 12))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_51| Int)) (<= 68 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_51| 12))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b8c7de3_94aa4557_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_harness_~#to~0#1.base_BEFORE_CALL_12| Int)) (and (<= 8679 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_append_harness_~#to~0#1.base_BEFORE_CALL_12| 4))) (<= (+ 16 |v_ULTIMATE.start_aws_byte_buf_append_harness_~#to~0#1.base_BEFORE_CALL_12|) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_harness_~#to~0#1.base_BEFORE_CALL_11| Int)) (and (<= (+ 16 |v_ULTIMATE.start_aws_byte_buf_append_harness_~#to~0#1.base_BEFORE_CALL_11|) |#StackAllocations|) (<= 8679 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_append_harness_~#to~0#1.base_BEFORE_CALL_11| 4)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b8f413b0_5b37a22_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_init_copy_~src#1.base"),
		};
		final String formulaAsString = "(and (<= 8682 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_init_copy_~src#1.base| 4))) (exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_50| Int)) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_50| 4)))))";
		final String expectedResultAsString = "(<= 8682 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_init_copy_~src#1.base| 4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b941625a_32b76a56_Treesizes_15_15() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1", "ULTIMATE.start_main_~z~0#1"),
		};
		final String formulaAsString = "(= (mod (+ (* |ULTIMATE.start_main_~x~0#1| |ULTIMATE.start_main_~z~0#1|) (* 18446744073709551615 |ULTIMATE.start_main_~y~0#1|) (* 18446744073709551615 |ULTIMATE.start_main_~x~0#1|) 1) 18446744073709551616) 0)";
		final String expectedResultAsString = "(<= (mod (+ (* |ULTIMATE.start_main_~x~0#1| |ULTIMATE.start_main_~z~0#1|) (* 18446744073709551615 |ULTIMATE.start_main_~y~0#1|) (* 18446744073709551615 |ULTIMATE.start_main_~x~0#1|) 1) 18446744073709551616) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b9d21d57_cde3e709_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base"),
		};
		final String formulaAsString = "(and (<= 8425 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base| 16))) (exists ((|v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_58| Int)) (<= 8425 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_58| 16)))))";
		final String expectedResultAsString = "(<= 8425 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base| 16)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ba659d23_dd5a25_Treesizes_277_268() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~last_1_var_1_17~0", "~var_1_11~0", "~var_1_10~0", "~var_1_4~0", "~last_1_var_1_11~0", "~var_1_16~0", "~var_1_5~0", "~last_1_var_1_13~0", "~var_1_14~0", "~last_1_var_1_12~0", "~var_1_13~0", "~var_1_8~0", "~var_1_19~0", "~var_1_9~0", "~var_1_18~0", "~var_1_6~0", "~last_1_var_1_18~0", "~last_1_var_1_1~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (or (and (or (and (= (mod ~last_1_var_1_12~0 256) 0) (<= (+ ~var_1_4~0 1) ~var_1_5~0) (<= (+ 5 (mod ~last_1_var_1_13~0 65536)) ~var_1_4~0)) (and (= (mod ~last_1_var_1_12~0 256) 0) (<= ~var_1_5~0 ~var_1_4~0) (<= (+ 5 (mod ~last_1_var_1_13~0 65536)) ~var_1_5~0))) (= (+ ~var_1_1~0 128) 0)) (and (= (mod ~last_1_var_1_13~0 65536) ~var_1_1~0) (or (not (= (mod ~last_1_var_1_12~0 256) 0)) (< ~var_1_5~0 (+ 5 (mod ~last_1_var_1_13~0 65536))) (< ~var_1_4~0 (+ 5 (mod ~last_1_var_1_13~0 65536)))))) (or (and (or (not (= (mod ~var_1_8~0 256) 0)) (and (not (= (mod ~last_1_var_1_12~0 256) 0)) (not (= (mod ~var_1_9~0 256) 0))) (= (mod ~var_1_6~0 256) 0)) (or (and (or (= (mod ~last_1_var_1_12~0 256) 0) (= (mod ~var_1_9~0 256) 0)) (= (mod ~var_1_8~0 256) 0)) (= (mod ~var_1_6~0 256) 1))) (< 0 (+ ~last_1_var_1_1~0 1))) (= 0 (mod ~var_1_10~0 256)) (<= (mod (+ (* (mod ~last_1_var_1_18~0 256) 65535) ~var_1_14~0) 65536) (mod ~var_1_13~0 65536)) (<= (+ (mod ~last_1_var_1_18~0 256) ~var_1_13~0) (mod ~var_1_14~0 65536)) (or (and (or (not (= (mod ~last_1_var_1_11~0 256) 0)) (< (mod ~last_1_var_1_17~0 65536) (+ (* ~var_1_4~0 ~last_1_var_1_1~0) 1)) (not (= (mod ~last_1_var_1_12~0 256) 0))) (= (mod ~var_1_19~0 256) (mod ~var_1_18~0 256)) (or (not (= (mod ~last_1_var_1_11~0 256) 0)) (not (= (* ~var_1_4~0 ~last_1_var_1_1~0) (mod ~last_1_var_1_17~0 65536))) (not (= (mod ~last_1_var_1_12~0 256) 0)))) (and (or (and (= (mod ~last_1_var_1_12~0 256) 0) (= (mod ~last_1_var_1_11~0 256) 0) (= (* ~var_1_4~0 ~last_1_var_1_1~0) (mod ~last_1_var_1_17~0 65536))) (and (= (mod ~last_1_var_1_12~0 256) 0) (= (mod ~last_1_var_1_11~0 256) 0) (<= (+ (* ~var_1_4~0 ~last_1_var_1_1~0) 1) (mod ~last_1_var_1_17~0 65536)))) (= (mod ~var_1_18~0 256) (mod ~var_1_16~0 256)))) (= ~var_1_11~0 0) (= (+ (div ~var_1_13~0 65536) (div ~var_1_14~0 65536) (mod ~last_1_var_1_18~0 256)) (div (+ (* (- 16776960) (div ~last_1_var_1_18~0 256)) (* ~last_1_var_1_18~0 65535) ~var_1_14~0) 65536)))";
		final String expectedResultAsString = "(let ((.cse0 (= (mod ~last_1_var_1_12~0 256) 0))) (let ((.cse3 (not .cse0)) (.cse14 (mod ~last_1_var_1_18~0 256))) (and (let ((.cse2 (mod ~last_1_var_1_13~0 65536))) (let ((.cse1 (+ 5 .cse2))) (or (and (or (and .cse0 (<= (+ ~var_1_4~0 1) ~var_1_5~0) (<= .cse1 ~var_1_4~0)) (and .cse0 (<= ~var_1_5~0 ~var_1_4~0) (<= .cse1 ~var_1_5~0))) (= (+ ~var_1_1~0 128) 0)) (and (= .cse2 ~var_1_1~0) (or .cse3 (< ~var_1_5~0 .cse1) (< ~var_1_4~0 .cse1)))))) (or (let ((.cse5 (= (mod ~var_1_9~0 256) 0)) (.cse4 (= (mod ~var_1_8~0 256) 0)) (.cse6 (mod ~var_1_6~0 256))) (and (or (not .cse4) (and .cse3 (not .cse5)) (= .cse6 0)) (or (and (or .cse0 .cse5) .cse4) (= .cse6 1)))) (< 0 (+ ~last_1_var_1_1~0 1))) (= 0 (mod ~var_1_10~0 256)) (let ((.cse13 (* ~var_1_4~0 ~last_1_var_1_1~0)) (.cse8 (mod ~last_1_var_1_17~0 65536))) (let ((.cse11 (= .cse13 .cse8)) (.cse12 (= (mod ~last_1_var_1_11~0 256) 0)) (.cse9 (+ .cse13 1)) (.cse10 (mod ~var_1_18~0 256))) (or (let ((.cse7 (not .cse12))) (and (or .cse7 (< .cse8 .cse9) .cse3) (= (mod ~var_1_19~0 256) .cse10) (or .cse7 (not .cse11) .cse3))) (and (or (and .cse0 .cse12 .cse11) (and .cse0 .cse12 (<= .cse9 .cse8))) (= .cse10 (mod ~var_1_16~0 256)))))) (= ~var_1_11~0 0) (= (mod (+ (* .cse14 65535) ~var_1_14~0) 65536) (mod ~var_1_13~0 65536)) (= (+ (div ~var_1_13~0 65536) (div ~var_1_14~0 65536) .cse14) (div (+ (* (- 16776960) (div ~last_1_var_1_18~0 256)) (* ~last_1_var_1_18~0 65535) ~var_1_14~0) 65536)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_baa6f541_d6ee8844_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_#t~ret740#1"),
		};
		final String formulaAsString = "(= (mod |ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_#t~ret740#1| 256) 0)";
		final String expectedResultAsString = "(<= (mod |ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_#t~ret740#1| 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_baacf5d8_a305ddca_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_4| Int)) (<= 8691 (select |#memory_$Pointer$.base| (+ 4 |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_4|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_23| Int)) (<= 8691 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_23|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_baebbe79_21c2de04_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_15| Int)) (<= 8688 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_15|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_41| Int)) (<= 8688 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_41| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bb260326_59e4c0fa_Treesizes_5_3() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~CELLCOUNT~0"),
		};
		final String formulaAsString = "(<= 1 (div ~CELLCOUNT~0 2))";
		final String expectedResultAsString = "(<= 2 ~CELLCOUNT~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bb6e8708_1b4cb3be_Treesizes_13_11() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~z~0#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~z~0#1| 1) (<= (mod (+ (* 4294967295 |ULTIMATE.start_main_~n~0#1|) 6) 4294967296) 0))";
		final String expectedResultAsString = "(and (<= (mod (+ 4294967290 |ULTIMATE.start_main_~n~0#1|) 4294967296) 0) (= |ULTIMATE.start_main_~z~0#1| 1))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bc03bbc7_8562bad3_Treesizes_10_7() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~x_2~0", "~x_1~0"),
		};
		final String formulaAsString = "(and (<= 0 ~x_2~0) (<= ~x_1~0 0) (= ~x_2~0 ~x_1~0))";
		final String expectedResultAsString = "(and (= ~x_2~0 0) (= ~x_1~0 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bc6145a2_d03b0cdf_Treesizes_91_41() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~x1~0", "~x2~0", "~n~0"),
		};
		final String formulaAsString = "(and (<= (+ 2147483649 (* 2 ~x2~0) (mod (+ ~x1~0 (* 4294967294 ~x2~0)) 4294967296)) (+ (mod ~x1~0 4294967296) (* 8589934592 (div ~x2~0 4294967296)) (* (mod ~x2~0 4294967296) 2) (mod (* 2147483647 ~x2~0) 2147483648))) (<= (mod ~n~0 4294967296) (mod ~x1~0 4294967296)) (= (mod ~x1~0 2) 0) (<= (+ (mod (* (div (* (- 1) ~x1~0) 2) 4294967295) 4294967296) 1) (mod ~n~0 4294967296)) (<= (+ (mod ~x1~0 4294967296) (mod (+ ~n~0 (* 4294967294 ~x2~0) 4294967293) 4294967296)) (+ (mod ~n~0 4294967296) 4294967293)) (= (mod ~x2~0 4294967296) (mod (* (div (* (- 1) ~x1~0) 2) 4294967295) 4294967296)))";
		final String expectedResultAsString = "(let ((.cse0 (mod ~n~0 4294967296)) (.cse1 (mod (* (div (* (- 1) ~x1~0) 2) 4294967295) 4294967296))) (and (<= .cse0 (mod ~x1~0 4294967296)) (= (mod ~x1~0 2) 0) (<= (+ .cse1 1) .cse0) (= (mod ~x2~0 4294967296) .cse1)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bcd200e0_337ecbd8_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_6| Int)) (and (<= 72 |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_6|) (<= |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_6| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_6| 12)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_7| Int)) (and (<= |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_7| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_7| 12))) (<= 72 |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_7|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bd0dc785_d0c53124_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base"),
		};
		final String formulaAsString = "(<= 68 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base| 12)))";
		final String expectedResultAsString = "(< 67 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base| 12)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bd5c923b_d1dd20cc_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_10| Int)) (<= 58 (select |#memory_$Pointer$.base| (+ |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_10| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_23| Int)) (<= 58 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_23|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bdaf5eaa_fa1b8e1e_Treesizes_109_109() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(and (or (= (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 12)) 256) (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 14)) 255) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255)) 256)) (< (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 14)) 255) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255)) 256) 128)) (or (< 127 (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 14)) 255) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255)) 256)) (= (select |#memory_int| (+ |~#WrapperStruct00~0.base| 12)) (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 14)) 255) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255)) 256))))";
		final String expectedResultAsString = "(let ((.cse1 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 12))) (.cse0 (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 14)) 255) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255)) 256))) (or (and (<= 128 .cse0) (= (+ .cse1 256) .cse0)) (and (<= .cse0 127) (= .cse1 .cse0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_be9ae938_9d6cf4ea_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base"),
		};
		final String formulaAsString = "(and (<= 52 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base| 4))) (exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~0#1.base_BEFORE_CALL_38| Int)) (<= 52 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~0#1.base_BEFORE_CALL_38| 4)))))";
		final String expectedResultAsString = "(<= 52 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base| 4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bf2a6f89_e0621ffd_Treesizes_15_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_20~0"),
		};
		final String formulaAsString = "(or (< (mod ~var_1_20~0 4294967296) 33) (< 2147483647 (mod (+ (* 4294967295 ~var_1_20~0) 4294967295) 4294967296)))";
		final String expectedResultAsString = "(<= (mod ~var_1_20~0 4294967296) 2147483647)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bf6e4492_fe699bba_Treesizes_65_47() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base"),
		};
		final String formulaAsString = "(and (exists ((v_DerPreprocessor_2 Int) (v_DerPreprocessor_1 Int)) (= (select (store (store (store |#memory_int| (+ (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base| 4)) 4294967296) |ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base| 8) v_DerPreprocessor_1) (+ |ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base| 4) v_DerPreprocessor_2) (+ (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base| 4)) 4294967296) |ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base| (- 4294967288)) 0) (+ |ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base| 4)) (select |#memory_int| (+ |ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base| 4)))) (= (select |#memory_int| (+ (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base| 4)) 4294967296) |ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base| 8)) 0) (<= (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base| 4)) 4294967296) 15))";
		final String expectedResultAsString = "(let ((.cse1 (select |#memory_int| (+ |ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base| 4)))) (let ((.cse0 (+ .cse1 4294967280))) (and (= (select |#memory_int| (+ (* (div .cse0 4294967296) (- 4294967296)) .cse1 |ULTIMATE.start_aws_string_compare_harness_#t~ret1359#1.base| 8)) 0) (<= 8589934575 (+ (mod (+ 4294967295 (* .cse1 4294967295)) 4294967296) (mod .cse0 4294967296))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bfb6c7e4_1dfc0915_Treesizes_9_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_reserve_relative_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(<= (mod (+ 4294967295 (select |#memory_int| |ULTIMATE.start_aws_byte_buf_reserve_relative_harness_~#buf~3#1.base|)) 4294967296) 4294967294)";
		final String expectedResultAsString = "(not (= (mod (select |#memory_int| |ULTIMATE.start_aws_byte_buf_reserve_relative_harness_~#buf~3#1.base|) 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c021664d_458ed1f4_Treesizes_87_60() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base", "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_from_c_str_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_2| Int)) (and (= (select |#memory_int| (+ |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_2| 8)) (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_2|)) (= (mod (select |#memory_int| (+ |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_2| 8)) 4294967296) 0) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_2| 12)) 0))) (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_from_c_str_harness_~#buf~3#1.base| 12)) 0) (exists ((|v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_10| Int)) (and (= (mod (select |#memory_int| (+ 8 |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_10|)) 4294967296) 0) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_10|) (select |#memory_int| |ULTIMATE.start_aws_byte_buf_from_c_str_harness_~#buf~3#1.base|)) (= (select |#memory_int| (+ 8 |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_10|)) (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_10|)) (= (select |#memory_$Pointer$.base| (+ 12 |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_10|)) 0))) (exists ((|v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_1| Int)) (and (= (select |#memory_int| (+ |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_1| 8)) (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_1|)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_1| 12)) 0))))";
		final String expectedResultAsString = "(and (= (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_from_c_str_harness_~#buf~3#1.base| 12)) 0) (exists ((|v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_10| Int)) (let ((.cse0 (select |#memory_int| (+ 8 |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_10|))) (.cse1 (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_10|))) (and (= (mod .cse0 4294967296) 0) (= .cse1 (select |#memory_int| |ULTIMATE.start_aws_byte_buf_from_c_str_harness_~#buf~3#1.base|)) (= .cse0 .cse1) (= (select |#memory_$Pointer$.base| (+ 12 |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_10|)) 0)))) (exists ((|v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_1| Int)) (and (= (select |#memory_int| (+ |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_1| 8)) (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_1|)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_1| 12)) 0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c06e90f1_874ce05d_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_byte_cursor_compare_lexical_~lhs#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_23| Int)) (<= 8691 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_23|)))) (<= 8691 (select |#memory_$Pointer$.base| (+ |aws_byte_cursor_compare_lexical_~lhs#1.base| 4))))";
		final String expectedResultAsString = "(<= 8691 (select |#memory_$Pointer$.base| (+ |aws_byte_cursor_compare_lexical_~lhs#1.base| 4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c0d061f0_bc974f22_Treesizes_13_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~a~0#1.base"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_8 Int)) (= (select (store |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| (* |ULTIMATE.start_main_~i~0#1| 4)) v_ArrVal_8) |ULTIMATE.start_main_~a~0#1.base|) 0))";
		final String expectedResultAsString = "(and (not (= |ULTIMATE.start_main_~i~0#1| 0)) (= (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c1660500_c13e16e7_Treesizes_39_38() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~sorted3~0", "~sorted1~0", "thread2Thread1of1ForFork0_~i~1", "~sorted2~0", "~A~0.base"),
		};
		final String formulaAsString = "(and (= ~sorted2~0 1) (= thread2Thread1of1ForFork0_~i~1 0) (= ~sorted3~0 1) (or (and (<= (+ (select |#memory_int| ~A~0.base) 1) (select |#memory_int| (+ ~A~0.base 4))) (= ~sorted1~0 1)) (and (<= (select |#memory_int| (+ ~A~0.base 4)) (select |#memory_int| ~A~0.base)) (= ~sorted1~0 0))))";
		final String expectedResultAsString = "(let ((.cse1 (select |#memory_int| ~A~0.base)) (.cse0 (select |#memory_int| (+ ~A~0.base 4)))) (and (or (< .cse0 (+ .cse1 1)) (= ~sorted1~0 1)) (or (< .cse1 .cse0) (= ~sorted1~0 0)) (= ~sorted2~0 1) (= thread2Thread1of1ForFork0_~i~1 0) (= ~sorted3~0 1)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c2222d88_75bebd4c_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_6_Pointer~0.base", "~var_1_13_Pointer~0.base", "~var_1_21_Pointer~0.base", "~var_1_22_Pointer~0.base"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_574 Int)) (<= (mod (select (store |#memory_int| ~var_1_13_Pointer~0.base v_ArrVal_574) ~var_1_6_Pointer~0.base) 256) 0)) (not (= ~var_1_6_Pointer~0.base ~var_1_21_Pointer~0.base)) (not (= ~var_1_22_Pointer~0.base ~var_1_6_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~var_1_13_Pointer~0.base ~var_1_6_Pointer~0.base)) (not (= ~var_1_6_Pointer~0.base ~var_1_21_Pointer~0.base)) (<= (mod (select |#memory_int| ~var_1_6_Pointer~0.base) 256) 0) (not (= ~var_1_22_Pointer~0.base ~var_1_6_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c2b21ec4_f38faf57_Treesizes_60_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getBoolSort, "ULTIMATE.start_step_#t~short7#1"),
			new FunDecl(SmtSortUtils::getIntSort, "~#BOOL_unsigned_char_Array_0~0.base", "~#signed_short_int_Array_0~0.base", "~#unsigned_short_int_Array_0~0.base", "~#float_Array_0~0.base", "~#signed_char_Array_0~0.base"),
		};
		final String formulaAsString = "(and (or |ULTIMATE.start_step_#t~short7#1| (forall ((v_ArrVal_783 Int) (v_ArrVal_782 Int) (v_ArrVal_781 Int) (v_ArrVal_780 Int)) (<= 1 (mod (select (store (store (store (store (store |#memory_int| |~#BOOL_unsigned_char_Array_0~0.base| 0) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_782) |~#float_Array_0~0.base| v_ArrVal_780) (+ |~#signed_short_int_Array_0~0.base| 4) v_ArrVal_781) (+ |~#signed_char_Array_0~0.base| 1) v_ArrVal_783) |~#BOOL_unsigned_char_Array_0~0.base|) 256)))) (or (not |ULTIMATE.start_step_#t~short7#1|) (forall ((v_ArrVal_783 Int) (v_ArrVal_782 Int) (v_ArrVal_781 Int) (v_ArrVal_780 Int)) (<= 1 (mod (select (store (store (store (store (store |#memory_int| |~#BOOL_unsigned_char_Array_0~0.base| 1) |~#unsigned_short_int_Array_0~0.base| v_ArrVal_782) |~#float_Array_0~0.base| v_ArrVal_780) (+ |~#signed_short_int_Array_0~0.base| 4) v_ArrVal_781) (+ |~#signed_char_Array_0~0.base| 1) v_ArrVal_783) |~#BOOL_unsigned_char_Array_0~0.base|) 256)))))";
		final String expectedResultAsString = "(and |ULTIMATE.start_step_#t~short7#1| (not (= |~#BOOL_unsigned_char_Array_0~0.base| (+ |~#signed_short_int_Array_0~0.base| 4))) (not (= |~#BOOL_unsigned_char_Array_0~0.base| |~#float_Array_0~0.base|)) (not (= |~#BOOL_unsigned_char_Array_0~0.base| (+ |~#signed_char_Array_0~0.base| 1))) (not (= |~#BOOL_unsigned_char_Array_0~0.base| |~#unsigned_short_int_Array_0~0.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c38f1fc0_cb0767e8_Treesizes_14_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_my_drv_disconnect_~#status~0#1.base", "ULTIMATE.start_main_~#data~1#1.base"),
		};
		final String formulaAsString = "(and (not (= (+ |ULTIMATE.start_main_~#data~1#1.base| 28) |ULTIMATE.start_my_drv_disconnect_~#status~0#1.base|)) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#data~1#1.base| 28)) 2))";
		final String expectedResultAsString = "(forall ((v_ArrVal_325 Int)) (= 2 (select (store |#memory_int| |ULTIMATE.start_my_drv_disconnect_~#status~0#1.base| v_ArrVal_325) (+ |ULTIMATE.start_main_~#data~1#1.base| 28))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c3e99edb_e03f7c34_Treesizes_15_3() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_step_~stepLocal_2~0#1"),
		};
		final String formulaAsString = "(exists ((v_z_12 Int)) (and (= |ULTIMATE.start_step_~stepLocal_2~0#1| 0) (<= 0 v_z_12) (not (= v_z_12 0)) (<= v_z_12 255)))";
		final String expectedResultAsString = "(= |ULTIMATE.start_step_~stepLocal_2~0#1| 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c4704616_77b190e3_Treesizes_30_30() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var0_Pointer~0.base", "~#unsigned_long_int_Array_0~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base", "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base", "~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base)) (forall ((v_ArrVal_614 Int)) (<= (mod (select (store |#memory_int| (+ |~#unsigned_long_int_Array_0~0.base| 4) v_ArrVal_614) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base) 256) 0)) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base ~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var0_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base)) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (<= (mod (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base) 256) 0) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ |~#unsigned_long_int_Array_0~0.base| 4))) (not (= ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base ~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var0_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c4d59c71_a45a0b77_Treesizes_65_65() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_12~0", "~var_1_10~0", "~var_1_4~0", "~var_1_5~0", "~var_1_14~0", "~var_1_13~0", "~var_1_3~0", "~var_1_9~0"),
		};
		final String formulaAsString = "(and (<= (+ ~var_1_4~0 (mod ~var_1_10~0 256)) ~var_1_9~0) (<= (mod ~var_1_9~0 256) (mod (+ ~var_1_4~0 ~var_1_10~0) 256)) (or (and (or (= (mod ~var_1_14~0 256) 0) (= (mod ~var_1_12~0 256) 0)) (= ~var_1_13~0 0)) (and (not (= (mod ~var_1_12~0 256) 0)) (not (= (mod ~var_1_14~0 256) 0)) (= ~var_1_13~0 1))) (= (div (+ ~var_1_4~0 ~var_1_10~0) 256) (+ (div ~var_1_10~0 256) (div ~var_1_9~0 256))) (= ~var_1_3~0 ~var_1_5~0))";
		final String expectedResultAsString = "(let ((.cse0 (+ ~var_1_4~0 ~var_1_10~0))) (and (<= (+ ~var_1_4~0 (mod ~var_1_10~0 256)) ~var_1_9~0) (<= (mod ~var_1_9~0 256) (mod .cse0 256)) (let ((.cse2 (= (mod ~var_1_12~0 256) 0)) (.cse1 (= (mod ~var_1_14~0 256) 0))) (or (and (or .cse1 .cse2) (= ~var_1_13~0 0)) (and (not .cse2) (not .cse1) (= ~var_1_13~0 1)))) (<= (+ (div ~var_1_10~0 256) (div ~var_1_9~0 256)) (div .cse0 256)) (= ~var_1_3~0 ~var_1_5~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c507220e_425a173f_Treesizes_38_29() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_12~0", "~var_1_13~0", "~var_1_8~0", "~var_1_9~0"),
		};
		final String formulaAsString = "(and (<= (+ (div ~var_1_9~0 4294967296) (mod ~var_1_8~0 256)) (div (+ (* (div ~var_1_8~0 256) (- 1099511627520)) (* 4294967295 ~var_1_8~0) 1211749435 ~var_1_13~0 ~var_1_12~0) 4294967296)) (= (mod ~var_1_9~0 4294967296) (mod (+ (* 4294967295 (mod ~var_1_8~0 256)) 1211749435 ~var_1_13~0 ~var_1_12~0) 4294967296)))";
		final String expectedResultAsString = "(let ((.cse1 (mod ~var_1_9~0 4294967296)) (.cse0 (mod ~var_1_8~0 256))) (and (<= (+ .cse0 ~var_1_9~0) (+ .cse1 1211749435 ~var_1_13~0 ~var_1_12~0)) (= .cse1 (mod (+ (* 4294967295 .cse0) 1211749435 ~var_1_13~0 ~var_1_12~0) 4294967296))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c5c74dbc_fe1a3d2d_Treesizes_341_338() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~last_1_var_1_25~0", "~var_1_23~0", "~var_1_22~0", "~var_1_21~0", "~var_1_10~0", "~var_1_20~0", "~var_1_16~0", "~var_1_4~0", "~var_1_26~0", "~var_1_5~0", "~var_1_25~0", "~var_1_24~0", "~var_1_8~0", "~var_1_19~0", "~var_1_9~0", "~var_1_18~0", "~var_1_17~0", "~var_1_7~0", "~last_1_var_1_16~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (<= (+ ~var_1_22~0 1) (mod ~var_1_7~0 65536)) (= (mod (+ (* 4294967295 (mod ~var_1_10~0 65536)) ~var_1_18~0 ~var_1_26~0) 4294967296) (mod ~var_1_25~0 4294967296)) (= ~var_1_4~0 ~var_1_1~0) (or (and (or (< 127 (mod (+ ~var_1_19~0 ~var_1_20~0 (* 255 ~var_1_21~0)) 256)) (< (+ ~var_1_4~0 ~var_1_18~0) ~var_1_17~0)) (or (= (mod (+ ~var_1_19~0 ~var_1_20~0 (* 255 ~var_1_21~0)) 256) (+ 256 ~var_1_16~0)) (< (+ ~var_1_4~0 ~var_1_18~0) ~var_1_17~0))) (and (<= (mod (+ ~var_1_19~0 ~var_1_20~0 (* 255 ~var_1_21~0)) 256) 127) (= (mod (+ ~var_1_19~0 ~var_1_20~0 (* 255 ~var_1_21~0)) 256) ~var_1_16~0))) (= ~var_1_23~0 1) (or (and (<= ~var_1_21~0 (+ ~var_1_18~0 ~var_1_20~0)) (or (and (<= (+ ~var_1_18~0 ~var_1_19~0 1) ~var_1_21~0) (or (and (<= (mod ~var_1_19~0 65536) 32767) (= ~var_1_22~0 (mod ~var_1_19~0 65536))) (and (<= 32768 (mod ~var_1_19~0 65536)) (= (mod ~var_1_19~0 65536) (+ 65536 ~var_1_22~0))))) (and (or (and (= (mod (+ (* ~var_1_18~0 65535) ~var_1_21~0) 65536) (+ 65536 ~var_1_22~0)) (<= 32768 (mod (+ (* ~var_1_18~0 65535) ~var_1_21~0) 65536))) (and (<= (mod (+ (* ~var_1_18~0 65535) ~var_1_21~0) 65536) 32767) (= (mod (+ (* ~var_1_18~0 65535) ~var_1_21~0) 65536) ~var_1_22~0))) (<= ~var_1_21~0 (+ ~var_1_18~0 ~var_1_19~0))))) (and (<= (+ ~var_1_18~0 ~var_1_20~0 1) ~var_1_21~0) (or (and (<= ~var_1_20~0 ~var_1_19~0) (or (and (= (mod ~var_1_20~0 65536) (+ 65536 ~var_1_22~0)) (<= 32768 (mod ~var_1_20~0 65536))) (and (= (mod ~var_1_20~0 65536) ~var_1_22~0) (<= (mod ~var_1_20~0 65536) 32767)))) (and (<= (+ ~var_1_19~0 1) ~var_1_20~0) (or (and (<= (mod ~var_1_19~0 65536) 32767) (= ~var_1_22~0 (mod ~var_1_19~0 65536))) (and (<= 32768 (mod ~var_1_19~0 65536)) (= (mod ~var_1_19~0 65536) (+ 65536 ~var_1_22~0)))))))) (or (and (or (= (mod ~last_1_var_1_16~0 4294967296) (mod ~last_1_var_1_25~0 4294967296)) (= (mod ~var_1_7~0 65536) (mod (+ (* ~var_1_10~0 65535) ~var_1_9~0) 65536))) (or (= (mod ~var_1_7~0 65536) (mod ~var_1_9~0 65536)) (not (= (mod ~last_1_var_1_16~0 4294967296) (mod ~last_1_var_1_25~0 4294967296))))) (< (mod ~var_1_10~0 65536) 9)) (or (not (= (mod ~var_1_8~0 256) 0)) (not (= (mod ~var_1_5~0 256) 0)) (not (= (mod ~var_1_24~0 256) 0))) (or (< 8 (mod ~var_1_10~0 65536)) (and (or (= (mod ~last_1_var_1_16~0 4294967296) (mod ~last_1_var_1_25~0 4294967296)) (= (mod ~var_1_7~0 65536) (mod (+ 65528 ~var_1_9~0) 65536))) (or (= (mod ~var_1_7~0 65536) (mod ~var_1_9~0 65536)) (not (= (mod ~last_1_var_1_16~0 4294967296) (mod ~last_1_var_1_25~0 4294967296)))))))";
		final String expectedResultAsString = "(let ((.cse0 (mod ~var_1_7~0 65536)) (.cse9 (= (mod ~last_1_var_1_16~0 4294967296) (mod ~last_1_var_1_25~0 4294967296)))) (let ((.cse1 (mod ~var_1_10~0 65536)) (.cse10 (or (= .cse0 (mod ~var_1_9~0 65536)) (not .cse9))) (.cse8 (< (+ ~var_1_4~0 ~var_1_18~0) ~var_1_17~0)) (.cse7 (mod (+ ~var_1_19~0 ~var_1_20~0 (* 255 ~var_1_21~0)) 256))) (and (<= (+ ~var_1_22~0 1) .cse0) (= (mod (+ (* 4294967295 .cse1) ~var_1_18~0 ~var_1_26~0) 4294967296) (mod ~var_1_25~0 4294967296)) (= ~var_1_4~0 ~var_1_1~0) (= ~var_1_23~0 1) (let ((.cse4 (+ 65536 ~var_1_22~0))) (let ((.cse2 (let ((.cse6 (mod ~var_1_19~0 65536))) (or (and (<= .cse6 32767) (= ~var_1_22~0 .cse6)) (and (<= 32768 .cse6) (= .cse6 .cse4)))))) (or (and (<= ~var_1_21~0 (+ ~var_1_18~0 ~var_1_20~0)) (or (and (<= (+ ~var_1_18~0 ~var_1_19~0 1) ~var_1_21~0) .cse2) (and (let ((.cse3 (mod (+ (* ~var_1_18~0 65535) ~var_1_21~0) 65536))) (or (and (= .cse3 .cse4) (<= 32768 .cse3)) (and (<= .cse3 32767) (= .cse3 ~var_1_22~0)))) (<= ~var_1_21~0 (+ ~var_1_18~0 ~var_1_19~0))))) (and (<= (+ ~var_1_18~0 ~var_1_20~0 1) ~var_1_21~0) (or (and (<= ~var_1_20~0 ~var_1_19~0) (let ((.cse5 (mod ~var_1_20~0 65536))) (or (and (= .cse5 .cse4) (<= 32768 .cse5)) (and (= .cse5 ~var_1_22~0) (<= .cse5 32767))))) (and (<= (+ ~var_1_19~0 1) ~var_1_20~0) .cse2)))))) (or (= .cse7 (+ 256 ~var_1_16~0)) (< .cse7 128) .cse8) (or (and (or .cse9 (= .cse0 (mod (+ (* ~var_1_10~0 65535) ~var_1_9~0) 65536))) .cse10) (< .cse1 9)) (or (not (= (mod ~var_1_8~0 256) 0)) (not (= (mod ~var_1_5~0 256) 0)) (not (= (mod ~var_1_24~0 256) 0))) (or (< 8 .cse1) (and (or .cse9 (= .cse0 (mod (+ 65528 ~var_1_9~0) 65536))) .cse10)) (or (< 127 .cse7) .cse8 (= .cse7 ~var_1_16~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c63b92ab_9ec8a129_Treesizes_10_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14| Int)) (<= (mod (* (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_left_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14|) 4294967295) 4294967296) 0))";
		final String expectedResultAsString = "(exists ((v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_11 Int)) (<= (mod (select |#memory_int| v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_11) 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c69e3bfd_e8c6d2a1_Treesizes_38_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(forall ((v_y_4 Int) (v_z_4 Int)) (or (< (+ (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) 65536) (* 65536 v_y_4) (* 65536 v_z_4)) 65536) (< 32767 (+ (* v_z_4 65535) (* 65536 v_y_4))) (< 65535 (+ v_z_4 (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) 65536)))))";
		final String expectedResultAsString = "(<= (mod (+ 32769 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2))) 65536) 32768)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c7721aa4_cb5663ea_Treesizes_38_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "func_to_recursive_line_26_to_34_0_~c.base", "func_to_recursive_line_26_to_34_0_~x.base", "func_to_recursive_line_26_to_34_0_~y.base"),
		};
		final String formulaAsString = "(and (= 2 (select |#memory_int| func_to_recursive_line_26_to_34_0_~y.base)) (exists ((v_func_to_recursive_line_26_to_34_0_~x.base_BEFORE_CALL_15 Int) (v_func_to_recursive_line_26_to_34_0_~y.base_BEFORE_CALL_16 Int)) (and (= 9 (select |#memory_int| v_func_to_recursive_line_26_to_34_0_~x.base_BEFORE_CALL_15)) (= (select |#memory_int| v_func_to_recursive_line_26_to_34_0_~y.base_BEFORE_CALL_16) 2) (<= (+ 8 v_func_to_recursive_line_26_to_34_0_~y.base_BEFORE_CALL_16) v_func_to_recursive_line_26_to_34_0_~x.base_BEFORE_CALL_15))) (<= (+ 8 func_to_recursive_line_26_to_34_0_~y.base) func_to_recursive_line_26_to_34_0_~x.base) (= 9 (select |#memory_int| func_to_recursive_line_26_to_34_0_~x.base)) (<= (+ 8 func_to_recursive_line_26_to_34_0_~x.base) func_to_recursive_line_26_to_34_0_~c.base))";
		final String expectedResultAsString = "(and (= 2 (select |#memory_int| func_to_recursive_line_26_to_34_0_~y.base)) (<= (+ 8 func_to_recursive_line_26_to_34_0_~y.base) func_to_recursive_line_26_to_34_0_~x.base) (= 9 (select |#memory_int| func_to_recursive_line_26_to_34_0_~x.base)) (<= (+ 8 func_to_recursive_line_26_to_34_0_~x.base) func_to_recursive_line_26_to_34_0_~c.base))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c7d3544e_e3618912_Treesizes_16_9() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~mask_SORT_2~0#1", "ULTIMATE.start_main_~var_9~0#1"),
		};
		final String formulaAsString = "(and (<= 0 (+ |ULTIMATE.start_main_~mask_SORT_2~0#1| 1)) (<= (+ (div |ULTIMATE.start_main_~mask_SORT_2~0#1| 4294967296) 1) 0) (= |ULTIMATE.start_main_~var_9~0#1| 1))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_main_~var_9~0#1| 1) (= (+ |ULTIMATE.start_main_~mask_SORT_2~0#1| 1) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c883c19f_ebd1538a_Treesizes_23_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#signed_short_int_Array_0~0.base", "~#unsigned_char_Array_0~0.base", "~#signed_char_Array_0~0.base"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_178 Int) (v_ArrVal_177 Int) (v_ArrVal_176 Int)) (<= 0 (+ (select (store (store (store |#memory_int| (+ |~#signed_char_Array_0~0.base| 4) v_ArrVal_176) |~#signed_short_int_Array_0~0.base| v_ArrVal_177) (+ 2 |~#unsigned_char_Array_0~0.base|) v_ArrVal_178) (+ 3 |~#signed_char_Array_0~0.base|)) 99)))";
		final String expectedResultAsString = "(forall ((v_ArrVal_178 Int) (v_ArrVal_177 Int)) (<= 0 (+ (select (store (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_177) (+ 2 |~#unsigned_char_Array_0~0.base|) v_ArrVal_178) (+ 3 |~#signed_char_Array_0~0.base|)) 99)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c8e7d7fd_644ce885_Treesizes_61_33() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#array~0#1.base", "~ARR_SIZE~0", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_7| Int)) (and (= (select |#memory_int| (+ |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_7| 12)) 0) (<= (select |#memory_int| (+ |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_7| 4)) 0) (= (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_7|) 0) (= (select |#memory_int| (+ |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_7| 8)) 0))) (<= |ULTIMATE.start_main_~sum~0#1| 0) (= (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) (<= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 4)) 0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 12)) 0) (= 2 ~ARR_SIZE~0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 8)) 0))";
		final String expectedResultAsString = "(and (<= |ULTIMATE.start_main_~sum~0#1| 0) (= (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) (<= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 4)) 0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 12)) 0) (= 2 ~ARR_SIZE~0) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array~0#1.base| 8)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c9c4a68b_f373ae36_Treesizes_9_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~0#1"),
		};
		final String formulaAsString = "(<= (mod (+ 4294967295 (* 4294967295 |ULTIMATE.start_main_~y~0#1|)) 4294967296) 4294967294)";
		final String expectedResultAsString = "(<= 1 (mod |ULTIMATE.start_main_~y~0#1| 4294967296))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_caaf7fa8_6b33f1f5_Treesizes_55_50() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_11~0", "~var_1_1~0", "~var_1_10~0", "~var_1_4~0", "~var_1_2~0", "~var_1_3~0", "~var_1_6~0"),
		};
		final String formulaAsString = "(and (= ~var_1_1~0 ~var_1_6~0) (<= (div (+ (* (div ~var_1_3~0 65536) (- 65536)) (* (div ~var_1_4~0 65536) (- 65536)) ~var_1_4~0 ~var_1_3~0 ~var_1_11~0) 4294967296) (div ~var_1_10~0 4294967296)) (<= 64 (mod ~var_1_4~0 65536)) (not (= (mod ~var_1_2~0 256) 0)) (= (mod ~var_1_10~0 4294967296) (mod (+ (* (div ~var_1_3~0 65536) 4294901760) (* (div ~var_1_4~0 65536) 4294901760) ~var_1_4~0 ~var_1_3~0 ~var_1_11~0) 4294967296)))";
		final String expectedResultAsString = "(let ((.cse1 (mod ~var_1_4~0 65536)) (.cse0 (mod ~var_1_10~0 4294967296))) (and (= ~var_1_1~0 ~var_1_6~0) (<= (+ .cse0 .cse1 ~var_1_11~0 (mod ~var_1_3~0 65536)) (+ 4294967295 ~var_1_10~0)) (<= 64 .cse1) (not (= (mod ~var_1_2~0 256) 0)) (= .cse0 (mod (+ (* (div ~var_1_3~0 65536) 4294901760) (* (div ~var_1_4~0 65536) 4294901760) ~var_1_4~0 ~var_1_3~0 ~var_1_11~0) 4294967296))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cb24df52_56e1bec0_Treesizes_65_37() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_string_eq_ignore_case_~b#1.base", "ULTIMATE.start_aws_string_eq_ignore_case_~a#1.base", "ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| 8 (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| 4)) 4294967296))) 0) (<= 328 |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base|) (<= (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| 4)) 4294967296) 15) (exists ((|v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_9| Int)) (and (= (select |#memory_int| (+ (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_9|)) 4294967296) 8 |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_9|)) 0) (<= 328 |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_9|) (<= (mod (select |#memory_int| (+ 4 |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_9|)) 4294967296) 15))) (= |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| |ULTIMATE.start_aws_string_eq_ignore_case_~a#1.base|) (or (= |ULTIMATE.start_aws_string_eq_ignore_case_~b#1.base| |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base|) (= |ULTIMATE.start_aws_string_eq_ignore_case_~b#1.base| 0)))";
		final String expectedResultAsString = "(let ((.cse0 (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| 4)) 4294967296))) (and (= (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| 8 .cse0)) 0) (<= 328 |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base|) (<= .cse0 15) (= |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| |ULTIMATE.start_aws_string_eq_ignore_case_~a#1.base|) (or (= |ULTIMATE.start_aws_string_eq_ignore_case_~b#1.base| |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base|) (= |ULTIMATE.start_aws_string_eq_ignore_case_~b#1.base| 0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cc0fb789_7d524e2a_Treesizes_27_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_read_~cur#1.base", "#StackAllocations"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_11| Int)) (and (<= (+ 21 |v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_11|) |#StackAllocations|) (<= 50 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_11| 4))))) (<= (+ |ULTIMATE.start_aws_byte_cursor_read_~cur#1.base| 21) |#StackAllocations|) (<= 50 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_read_~cur#1.base| 4))))";
		final String expectedResultAsString = "(and (<= (+ |ULTIMATE.start_aws_byte_cursor_read_~cur#1.base| 21) |#StackAllocations|) (<= 50 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_read_~cur#1.base| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cca63ce5_ff26b18b_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_25| Int)) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_25| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_24| Int)) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_24| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cd707909_1fc0253f_Treesizes_117_117() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(and (or (= (select |#memory_int| (+ |~#WrapperStruct00~0.base| 12)) (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 14)) 255) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 255)) 256)) (< 127 (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 14)) 255) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 255)) 256))) (or (< (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 14)) 255) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 255)) 256) 128) (= (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 12)) 256) (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 14)) 255) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 255)) 256))))";
		final String expectedResultAsString = "(let ((.cse1 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 12))) (.cse0 (mod (+ (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 14)) 255) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 16)) 255) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 13)) 255)) 256))) (or (and (<= 128 .cse0) (= (+ .cse1 256) .cse0)) (and (= .cse1 .cse0) (<= .cse0 127))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cdfa213c_7560da6_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_buf_secure_zero_~buf#1.base_BEFORE_CALL_16| Int)) (and (<= (+ (select |#memory_$Pointer$.base| (+ |v_aws_byte_buf_secure_zero_~buf#1.base_BEFORE_CALL_16| 4)) 2) |v_aws_byte_buf_secure_zero_~buf#1.base_BEFORE_CALL_16|) (<= 8684 (select |#memory_$Pointer$.base| (+ |v_aws_byte_buf_secure_zero_~buf#1.base_BEFORE_CALL_16| 4)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_45| Int)) (let ((.cse0 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_45| 4)))) (and (<= (+ 2 .cse0) |v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_45|) (<= 8684 .cse0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ce265537_5644776f_Treesizes_21_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_eq_harness_~#lhs~0#1.base", "ULTIMATE.start_aws_byte_buf_eq_harness_~#rhs~0#1.base"),
		};
		final String formulaAsString = "(and (<= (+ |ULTIMATE.start_aws_byte_buf_eq_harness_~#lhs~0#1.base| 16) |ULTIMATE.start_aws_byte_buf_eq_harness_~#rhs~0#1.base|) (<= 8675 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_eq_harness_~#lhs~0#1.base| 4))) (exists ((|v_ULTIMATE.start_aws_byte_buf_eq_harness_~#lhs~0#1.base_BEFORE_CALL_35| Int)) (<= 8675 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_eq_harness_~#lhs~0#1.base_BEFORE_CALL_35| 4)))))";
		final String expectedResultAsString = "(and (<= (+ |ULTIMATE.start_aws_byte_buf_eq_harness_~#lhs~0#1.base| 16) |ULTIMATE.start_aws_byte_buf_eq_harness_~#rhs~0#1.base|) (<= 8675 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_eq_harness_~#lhs~0#1.base| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ce65196c_8bb787d9_Treesizes_134_14() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~b~0#1", "ULTIMATE.start_main_~B~0#1"),
		};
		final String formulaAsString = "(and (<= |ULTIMATE.start_main_~B~0#1| 1) (exists ((v_y_4 Int) (v_y_5 Int) (v_y_8 Int) (v_z_6 Int) (v_z_8 Int)) (and (<= (+ (* 2 |ULTIMATE.start_main_~b~0#1|) v_z_6) (+ (* 2 v_z_8) (* v_y_8 4294967296) 4294967295)) (<= 0 v_z_8) (<= 0 (+ (* v_y_8 2147483648) v_z_8)) (<= (+ (* 4294967295 v_z_6) (* |ULTIMATE.start_main_~b~0#1| 8589934590) (* v_y_5 4294967296)) (+ (* v_z_8 8589934590) (* 18446744069414584320 v_y_8) 1)) (<= 0 v_z_6) (<= (+ (* v_z_8 8589934590) (* 18446744069414584320 v_y_8)) (+ (* 4294967295 v_z_6) (* |ULTIMATE.start_main_~b~0#1| 8589934590) (* v_y_5 4294967296))) (<= v_z_8 2147483647) (<= v_z_6 1) (<= (+ (* 2 v_z_8) (* v_y_8 4294967296)) (+ (* 2 |ULTIMATE.start_main_~b~0#1|) v_z_6)) (<= (+ (* 4294967295 v_z_6) (* |ULTIMATE.start_main_~b~0#1| 8589934590) (* v_y_5 4294967296) 1) (+ (* v_z_8 8589934591) (* 8589934592 v_y_4) (* v_y_8 2147483648))) (<= (+ (* 8589934592 v_y_4) (* v_y_8 4294967296) (* 8589934592 v_z_8)) (+ (* 4294967295 v_z_6) (* |ULTIMATE.start_main_~b~0#1| 8589934590) |ULTIMATE.start_main_~B~0#1| (* v_y_5 4294967296) 1)))))";
		final String expectedResultAsString = "(and (<= |ULTIMATE.start_main_~B~0#1| 1) (<= 1 |ULTIMATE.start_main_~b~0#1|) (<= (* 2 |ULTIMATE.start_main_~b~0#1|) (+ |ULTIMATE.start_main_~B~0#1| 1)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ceeb65f4_d839ea73_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_31| Int)) (<= 8684 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_31| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_30| Int)) (<= 8684 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_30| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cfaa3744_dc831126_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_linked_list_node_next_is_valid_#in~node.base", "aws_linked_list_node_next_is_valid_~node.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_53| Int)) (<= (+ |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_53| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_53|))) (= aws_linked_list_node_next_is_valid_~node.base |aws_linked_list_node_next_is_valid_#in~node.base|))";
		final String expectedResultAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_51| Int)) (<= (+ |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_51| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_51|))) (= aws_linked_list_node_next_is_valid_~node.base |aws_linked_list_node_next_is_valid_#in~node.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cff7938f_7152a8c_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_6_Pointer~0.base", "~var_1_10_Pointer~0.base", "~var_1_4_Pointer~0.base"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_178 Int)) (<= (mod (+ (select (store |#memory_int| ~var_1_6_Pointer~0.base v_ArrVal_178) ~var_1_4_Pointer~0.base) 65535) 65536) 65534)) (not (= ~var_1_10_Pointer~0.base ~var_1_4_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~var_1_10_Pointer~0.base ~var_1_4_Pointer~0.base)) (<= (mod (+ (select |#memory_int| ~var_1_4_Pointer~0.base) 65535) 65536) 65534) (not (= ~var_1_6_Pointer~0.base ~var_1_4_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d0461ab1_18f8b3c4_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_prev_~node#1.base_BEFORE_CALL_35| Int)) (and (= (select |#memory_$Pointer$.base| (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_linked_list_prev_~node#1.base_BEFORE_CALL_35|))) |v_ULTIMATE.start_aws_linked_list_prev_~node#1.base_BEFORE_CALL_35|) (<= (+ 8 |v_ULTIMATE.start_aws_linked_list_prev_~node#1.base_BEFORE_CALL_35|) (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_linked_list_prev_~node#1.base_BEFORE_CALL_35|)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_prev_~node#1.base_BEFORE_CALL_34| Int)) (let ((.cse0 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_linked_list_prev_~node#1.base_BEFORE_CALL_34|)))) (and (<= (+ 8 |v_ULTIMATE.start_aws_linked_list_prev_~node#1.base_BEFORE_CALL_34|) .cse0) (= (select |#memory_$Pointer$.base| .cse0) |v_ULTIMATE.start_aws_linked_list_prev_~node#1.base_BEFORE_CALL_34|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d0670ef2_b53d02c8_Treesizes_33_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "func_to_recursive_line_29_to_40_0_~a.base", "func_to_recursive_line_29_to_40_0_~s.base"),
		};
		final String formulaAsString = "(and (<= (+ func_to_recursive_line_29_to_40_0_~a.base 8) func_to_recursive_line_29_to_40_0_~s.base) (= (select |#memory_int| func_to_recursive_line_29_to_40_0_~s.base) 4) (= (select |#memory_int| func_to_recursive_line_29_to_40_0_~a.base) 1) (exists ((v_func_to_recursive_line_29_to_40_0_~s.base_BEFORE_CALL_14 Int) (v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_11 Int)) (and (<= (+ v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_11 8) v_func_to_recursive_line_29_to_40_0_~s.base_BEFORE_CALL_14) (= (select |#memory_int| v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_11) 1) (= (select |#memory_int| v_func_to_recursive_line_29_to_40_0_~s.base_BEFORE_CALL_14) 4))))";
		final String expectedResultAsString = "(and (<= (+ func_to_recursive_line_29_to_40_0_~a.base 8) func_to_recursive_line_29_to_40_0_~s.base) (= (select |#memory_int| func_to_recursive_line_29_to_40_0_~s.base) 4) (= (select |#memory_int| func_to_recursive_line_29_to_40_0_~a.base) 1))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d0ed9826_2b078d83_Treesizes_37_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_ensure_byte_buf_has_allocated_buffer_member_~buf#1.base", "#StackHeapBarrier", "#InitialAllocations", "ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (<= (+ |#StackHeapBarrier| 1) |ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base|) (<= (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base| 8)) 4294967296) 16) (exists ((|v_ULTIMATE.start_ensure_byte_buf_has_allocated_buffer_member_~buf#1.base_BEFORE_CALL_3| Int)) (and (<= (mod (select |#memory_int| (+ |v_ULTIMATE.start_ensure_byte_buf_has_allocated_buffer_member_~buf#1.base_BEFORE_CALL_3| 8)) 4294967296) 16) (<= (+ |#StackHeapBarrier| 1) |v_ULTIMATE.start_ensure_byte_buf_has_allocated_buffer_member_~buf#1.base_BEFORE_CALL_3|))) (<= 8821 |#InitialAllocations|) (= |ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base| |ULTIMATE.start_ensure_byte_buf_has_allocated_buffer_member_~buf#1.base|))";
		final String expectedResultAsString = "(and (<= (+ |#StackHeapBarrier| 1) |ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base|) (<= (mod (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base| 8)) 4294967296) 16) (<= 8821 |#InitialAllocations|) (= |ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base| |ULTIMATE.start_ensure_byte_buf_has_allocated_buffer_member_~buf#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d1d22063_d51962f2_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_38| Int)) (and (<= 8691 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_38| 4))) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_38| 8) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_37| Int)) (and (<= 8691 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_37| 4))) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_37| 8) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d2ee483_b29063ff_Treesizes_42_42() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "~SIZE~0", "ULTIMATE.start_main_~#a~0#1.base", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(or (= (+ (select |#memory_int| (+ |ULTIMATE.start_main_~#a~0#1.base| (* 2 |ULTIMATE.start_main_~i~0#1|))) |ULTIMATE.start_main_~sum~0#1|) (+ (select |#memory_int| (+ (- 2) |ULTIMATE.start_main_~#a~0#1.base| (* ~SIZE~0 2))) (select |#memory_int| (+ 2 |ULTIMATE.start_main_~#a~0#1.base|)) (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) (select |#memory_int| (+ (- 4) |ULTIMATE.start_main_~#a~0#1.base| (* ~SIZE~0 2))))) (not (= ~SIZE~0 (+ |ULTIMATE.start_main_~i~0#1| 1))))";
		final String expectedResultAsString = "(or (let ((.cse0 (* 2 |ULTIMATE.start_main_~i~0#1|))) (= (+ (select |#memory_int| (+ (- 2) |ULTIMATE.start_main_~#a~0#1.base| (* ~SIZE~0 2))) (select |#memory_int| (+ (- 2) |ULTIMATE.start_main_~#a~0#1.base| .cse0)) (select |#memory_int| (+ 2 |ULTIMATE.start_main_~#a~0#1.base|)) (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|)) (+ (select |#memory_int| (+ |ULTIMATE.start_main_~#a~0#1.base| .cse0)) |ULTIMATE.start_main_~sum~0#1|))) (not (= ~SIZE~0 (+ |ULTIMATE.start_main_~i~0#1| 1))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d393d414_a0f49cf_Treesizes_23_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_pop_back_~list#1.base"),
		};
		final String formulaAsString = "(and (<= |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base| (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base| 12))) (<= 72 |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|) (exists ((|v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_11| Int)) (and (<= |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_11| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_11| 12))) (<= 72 |v_ULTIMATE.start_aws_linked_list_pop_back_harness_~#list~0#1.base_BEFORE_CALL_11|))))";
		final String expectedResultAsString = "(and (<= |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base| (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base| 12))) (<= 72 |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d40044bd_784809da_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_buf_write_~buf.base_BEFORE_CALL_9 Int)) (<= (mod (+ (* (select |#memory_int| (+ 8 v_aws_byte_buf_write_~buf.base_BEFORE_CALL_9)) 4294967295) 4294967295) 4294967296) 4294967294))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base_BEFORE_CALL_42| Int)) (<= (mod (+ (* (select |#memory_int| (+ 8 |v_ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base_BEFORE_CALL_42|)) 4294967295) 4294967295) 4294967296) 4294967294))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d4375fc9_8d7f8de9_Treesizes_295_282() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_23~0", "~var_1_12~0", "~var_1_22~0", "~var_1_11~0", "~var_1_21~0", "~var_1_10~0", "~var_1_20~0", "~var_1_4~0", "~var_1_5~0", "~var_1_14~0", "~last_1_var_1_13~0", "~var_1_13~0", "~var_1_8~0", "~var_1_9~0", "~var_1_6~0", "~var_1_1~0", "~last_1_var_1_9~0", "~last_1_var_1_20~0", "~last_1_var_1_6~0"),
		};
		final String formulaAsString = "(and (or (and (or (not (= (mod ~var_1_6~0 65536) 100)) (< ~var_1_8~0 100)) (<= (+ ~var_1_8~0 1) (mod ~var_1_6~0 65536))) (= ~var_1_14~0 ~var_1_13~0)) (= (mod ~var_1_4~0 256) 0) (<= ~var_1_9~0 100) (or (< (+ (* ~last_1_var_1_13~0 ~last_1_var_1_20~0) (* ~last_1_var_1_13~0 ~last_1_var_1_13~0)) (+ ~last_1_var_1_13~0 1)) (= (mod ~var_1_6~0 65536) 256) (= (mod ~var_1_5~0 256) 0)) (= 100 (mod ~var_1_9~0 65536)) (or (and (or (and (or (and (= (+ 65536 ~var_1_20~0) (mod ~var_1_23~0 65536)) (<= (+ ~var_1_23~0 ~var_1_22~0) ~var_1_21~0)) (and (<= (+ ~var_1_21~0 1) (+ ~var_1_23~0 ~var_1_22~0)) (= ~var_1_20~0 (mod (+ ~var_1_21~0 (* ~var_1_22~0 65535)) 65536)))) (<= (mod (+ ~var_1_21~0 (* ~var_1_22~0 65535)) 65536) 32767)) (and (or (and (<= (+ ~var_1_21~0 1) (+ ~var_1_23~0 ~var_1_22~0)) (= (+ 65536 ~var_1_20~0) (mod (+ ~var_1_21~0 (* ~var_1_22~0 65535)) 65536))) (and (= (+ 65536 ~var_1_20~0) (mod ~var_1_23~0 65536)) (<= (+ ~var_1_23~0 ~var_1_22~0) ~var_1_21~0))) (<= 32768 (mod (+ ~var_1_21~0 (* ~var_1_22~0 65535)) 65536)))) (<= 32768 (mod ~var_1_23~0 65536))) (= 16 ~var_1_14~0) (and (<= (mod ~var_1_23~0 65536) 32767) (or (and (or (and (= (mod ~var_1_23~0 65536) ~var_1_20~0) (<= (+ ~var_1_23~0 ~var_1_22~0) ~var_1_21~0)) (and (<= (+ ~var_1_21~0 1) (+ ~var_1_23~0 ~var_1_22~0)) (= ~var_1_20~0 (mod (+ ~var_1_21~0 (* ~var_1_22~0 65535)) 65536)))) (<= (mod (+ ~var_1_21~0 (* ~var_1_22~0 65535)) 65536) 32767)) (and (or (and (<= (+ ~var_1_21~0 1) (+ ~var_1_23~0 ~var_1_22~0)) (= (+ 65536 ~var_1_20~0) (mod (+ ~var_1_21~0 (* ~var_1_22~0 65535)) 65536))) (and (= (mod ~var_1_23~0 65536) ~var_1_20~0) (<= (+ ~var_1_23~0 ~var_1_22~0) ~var_1_21~0))) (<= 32768 (mod (+ ~var_1_21~0 (* ~var_1_22~0 65535)) 65536)))))) (<= (+ (mod ~var_1_11~0 65536) 1) (mod ~var_1_6~0 65536)) (= (mod ~var_1_1~0 256) 0) (or (< (mod ~last_1_var_1_9~0 65536) (+ (mod ~last_1_var_1_6~0 65536) 1)) (= (mod ~var_1_5~0 256) 0)) (<= 0 (div ~var_1_6~0 65536)) (or (< (mod ~last_1_var_1_13~0 4294967296) (+ 1 (mod (+ (* 4294967295 ~last_1_var_1_13~0) ~var_1_12~0) 4294967296))) (= (mod ~var_1_10~0 65536) (mod ~var_1_11~0 65536))))";
		final String expectedResultAsString = "(let ((.cse1 (= (mod ~var_1_5~0 256) 0)) (.cse0 (mod ~var_1_6~0 65536)) (.cse14 (mod ~var_1_11~0 65536))) (and (= (mod ~var_1_4~0 256) 0) (<= ~var_1_9~0 100) (or (< (+ (* ~last_1_var_1_13~0 ~last_1_var_1_20~0) (* ~last_1_var_1_13~0 ~last_1_var_1_13~0)) (+ ~last_1_var_1_13~0 1)) (= .cse0 256) .cse1) (= 100 (mod ~var_1_9~0 65536)) (let ((.cse11 (+ ~var_1_23~0 ~var_1_22~0))) (let ((.cse7 (+ 65536 ~var_1_20~0)) (.cse13 (<= (+ ~var_1_21~0 1) .cse11)) (.cse12 (mod (+ ~var_1_21~0 (* ~var_1_22~0 65535)) 65536))) (let ((.cse3 (and .cse13 (= ~var_1_20~0 .cse12))) (.cse4 (<= .cse12 32767)) (.cse5 (and .cse13 (= .cse7 .cse12))) (.cse6 (<= 32768 .cse12)) (.cse8 (mod ~var_1_23~0 65536)) (.cse9 (<= .cse11 ~var_1_21~0))) (or (and (let ((.cse2 (and (= .cse7 .cse8) .cse9))) (or (and (or .cse2 .cse3) .cse4) (and (or .cse5 .cse2) .cse6))) (<= 32768 .cse8)) (= 16 ~var_1_14~0) (and (<= .cse8 32767) (let ((.cse10 (and (= .cse8 ~var_1_20~0) .cse9))) (or (and (or .cse10 .cse3) .cse4) (and (or .cse5 .cse10) .cse6)))))))) (<= (+ .cse14 1) .cse0) (= (mod ~var_1_1~0 256) 0) (or (< (mod ~last_1_var_1_9~0 65536) (+ (mod ~last_1_var_1_6~0 65536) 1)) .cse1) (or (= ~var_1_14~0 ~var_1_13~0) (< ~var_1_8~0 .cse0)) (<= 0 (div ~var_1_6~0 65536)) (or (< (mod ~last_1_var_1_13~0 4294967296) (+ 1 (mod (+ (* 4294967295 ~last_1_var_1_13~0) ~var_1_12~0) 4294967296))) (= (mod ~var_1_10~0 65536) .cse14))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d4df821b_c5b9589a_Treesizes_11_9() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~var_63_arg_1~0#1"),
		};
		final String formulaAsString = "(and (<= (mod |ULTIMATE.start_main_~var_63_arg_1~0#1| 256) 0) (<= 0 (div |ULTIMATE.start_main_~var_63_arg_1~0#1| 256)))";
		final String expectedResultAsString = "(and (<= (mod |ULTIMATE.start_main_~var_63_arg_1~0#1| 256) 0) (<= 0 |ULTIMATE.start_main_~var_63_arg_1~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d543d41e_1b9b9e37_Treesizes_64_64() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#signed_short_int_Array_0~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base", "~#unsigned_short_int_Array_0~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base", "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base", "~#float_Array_0~0.base", "~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base", "~#signed_char_Array_0~0.base", "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var2_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ 2 |~#unsigned_short_int_Array_0~0.base|))) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base)) (forall ((v_ArrVal_718 Int)) (<= (mod (+ 255 (select (store |#memory_int| (+ |~#float_Array_0~0.base| 12) v_ArrVal_718) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) 256) 254)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base |~#signed_char_Array_0~0.base|)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ |~#signed_short_int_Array_0~0.base| 2))) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ |~#signed_short_int_Array_0~0.base| 6))) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var2_Pointer~0.base)) (not (= |~#signed_short_int_Array_0~0.base| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= (+ 2 |~#signed_char_Array_0~0.base|) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base)) (not (= ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ 2 |~#unsigned_short_int_Array_0~0.base|))) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base |~#signed_char_Array_0~0.base|)) (<= (mod (+ (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base) 255) 256) 254) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ |~#signed_short_int_Array_0~0.base| 2))) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ |~#signed_short_int_Array_0~0.base| 6))) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var2_Pointer~0.base)) (not (= |~#signed_short_int_Array_0~0.base| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= (+ 2 |~#signed_char_Array_0~0.base|) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base)) (not (= ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)) (not (= (+ |~#float_Array_0~0.base| 12) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d5cfe8_1e76030a_Treesizes_19_18() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~CCCELVOL2~0#1", "ULTIMATE.start_main_~MINVAL~0#1", "~CELLCOUNT~0"),
		};
		final String formulaAsString = "(and (or (< 2 (div ~CELLCOUNT~0 4)) (and (= 2 |ULTIMATE.start_main_~MINVAL~0#1|) (= |ULTIMATE.start_main_~CCCELVOL2~0#1| 3))) (<= 2 (div ~CELLCOUNT~0 4)))";
		final String expectedResultAsString = "(let ((.cse0 (div ~CELLCOUNT~0 4))) (or (< 2 .cse0) (and (= 2 |ULTIMATE.start_main_~MINVAL~0#1|) (= |ULTIMATE.start_main_~CCCELVOL2~0#1| 3) (= .cse0 2))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d63089a_35149026_Treesizes_18_3() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0", "~var_1_5~0"),
		};
		final String formulaAsString = "(and (<= ~var_1_5~0 ~var_1_1~0) (<= (mod ~var_1_1~0 4294967296) (mod ~var_1_5~0 4294967296)) (<= ~var_1_1~0 (+ (mod ~var_1_1~0 4294967296) ~var_1_5~0)))";
		final String expectedResultAsString = "(= ~var_1_1~0 ~var_1_5~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d6a12968_bc78f834_Treesizes_7_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_property_#t~mem114#1"),
		};
		final String formulaAsString = "(<= (mod (+ |ULTIMATE.start_property_#t~mem114#1| 65535) 65536) 65534)";
		final String expectedResultAsString = "(<= 1 (mod |ULTIMATE.start_property_#t~mem114#1| 65536))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d7abb6b0_4b19f9aa_Treesizes_95_47() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| (+ (select |#memory_int| (+ 4 |ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base|)) (* (div (+ (select |#memory_int| (+ 4 |ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base|)) 4294967280) 4294967296) (- 4294967296)) 8 |ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base|)) 0) (exists ((|v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_1| Int)) (and (<= 8589934575 (+ (mod (+ (* 4294967295 (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_1| 4))) 4294967295) 4294967296) (mod (+ (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_1| 4)) 4294967280) 4294967296))) (= (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_1| (* (div (+ (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_1| 4)) 4294967280) 4294967296) (- 4294967296)) 8 (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_1| 4)))) 0))) (<= 8589934575 (+ (mod (+ (select |#memory_int| (+ 4 |ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base|)) 4294967280) 4294967296) (mod (+ 4294967295 (* (select |#memory_int| (+ 4 |ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base|)) 4294967295)) 4294967296))))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (+ 4 |ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base|)))) (let ((.cse1 (+ .cse0 4294967280))) (and (= (select |#memory_int| (+ .cse0 (* (div .cse1 4294967296) (- 4294967296)) 8 |ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base|)) 0) (<= 8589934575 (+ (mod .cse1 4294967296) (mod (+ 4294967295 (* .cse0 4294967295)) 4294967296))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d8550fdc_cb0767e8_Treesizes_14_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_my_drv_disconnect_~#status~0#1.base", "ULTIMATE.start_main_~#data~1#1.base"),
		};
		final String formulaAsString = "(and (not (= (+ |ULTIMATE.start_main_~#data~1#1.base| 28) |ULTIMATE.start_my_drv_disconnect_~#status~0#1.base|)) (= (select |#memory_int| (+ |ULTIMATE.start_main_~#data~1#1.base| 28)) 2))";
		final String expectedResultAsString = "(forall ((v_ArrVal_908 Int)) (= 2 (select (store |#memory_int| |ULTIMATE.start_my_drv_disconnect_~#status~0#1.base| v_ArrVal_908) (+ |ULTIMATE.start_main_~#data~1#1.base| 28))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d8cd467c_9fac0918_Treesizes_55_45() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_5_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base", "~WrapperStruct00_var_1_6_Pointer~0.base", "~WrapperStruct00_var_1_7_Pointer~0.base"),
		};
		final String formulaAsString = "(and (<= (+ (mod (select |#memory_int| ~WrapperStruct00_var_1_4_Pointer~0.base) 256) (mod (+ 255 (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base) (* 255 (select |#memory_int| ~WrapperStruct00_var_1_5_Pointer~0.base))) 256)) 253) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_6_Pointer~0.base)) (<= (mod (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base) 256) (mod (+ 255 (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base) (* 255 (select |#memory_int| ~WrapperStruct00_var_1_5_Pointer~0.base))) 256)) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_4_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_6_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_5_Pointer~0.base)))";
		final String expectedResultAsString = "(and (let ((.cse1 (select |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base)) (.cse0 (select |#memory_int| ~WrapperStruct00_var_1_4_Pointer~0.base))) (<= (+ 2 (mod .cse0 256) (mod .cse1 256)) (mod (+ .cse1 (* 255 (select |#memory_int| ~WrapperStruct00_var_1_5_Pointer~0.base)) 1 .cse0) 256))) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_6_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_4_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_6_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_5_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d97d5a37_283c087c_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_63| Int)) (<= 8425 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_63| 16))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_58| Int)) (<= 8425 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_58| 16))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d9d2d1ff_3f2f48c1_Treesizes_18_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "#Ultimate.C_memset_#value", "#Ultimate.C_memset_#ptr.base"),
		};
		final String formulaAsString = "(or (forall ((|#Ultimate.C_memset_#t~loopctr684| Int)) (= (mod (select (store |#memory_int| (+ |#Ultimate.C_memset_#t~loopctr684| |#Ultimate.C_memset_#ptr.base|) 0) |#Ultimate.C_memset_#ptr.base|) 256) 0)) (not (= |#Ultimate.C_memset_#value| 0)))";
		final String expectedResultAsString = "(or (= (mod (select |#memory_int| |#Ultimate.C_memset_#ptr.base|) 256) 0) (not (= |#Ultimate.C_memset_#value| 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_daaa07ab_1468f55c_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_property_#t~mem135#1"),
		};
		final String formulaAsString = "(= (mod |ULTIMATE.start_property_#t~mem135#1| 256) 0)";
		final String expectedResultAsString = "(<= (mod |ULTIMATE.start_property_#t~mem135#1| 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_db560ec2_7d06d30c_Treesizes_10_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_from_array_~#cur~2#1.base_BEFORE_CALL_8| Int)) (<= (mod (* (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_from_array_~#cur~2#1.base_BEFORE_CALL_8|) 4294967295) 4294967296) 0))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_from_array_harness_~#cur~3#1.base_BEFORE_CALL_12| Int)) (<= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_from_array_harness_~#cur~3#1.base_BEFORE_CALL_12|) 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dbc10e24_9cf9a761_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_be32_~cur#1.base_BEFORE_CALL_15| Int)) (<= 8685 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_be32_~cur#1.base_BEFORE_CALL_15| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_51| Int)) (<= 8685 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_51| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dc68cc51_b733b875_Treesizes_39_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base"),
		};
		final String formulaAsString = "(<= (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 1)) (mod (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) (* (select |#memory_int| (+ |~#WrapperStruct00~0.base| 1)) 255) 127) 256) (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) 256)) (+ 382 (mod (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) 256)))";
		final String expectedResultAsString = "(<= (let ((.cse0 (select |#memory_int| (+ |~#WrapperStruct00~0.base| 1)))) (+ .cse0 (mod (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 2)) (* .cse0 255) 127) 256))) 382)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dce297b5_81968098_Treesizes_30_30() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_2_Pointer~0.base", "~var_1_1_Pointer~0.base", "~var_1_7_Pointer~0.base", "~#var_1_9~0.base", "~#var_1_14~0.base", "~#var_1_15~0.base", "~#var_1_16~0.base"),
		};
		final String formulaAsString = "(and (not (= ~var_1_2_Pointer~0.base |~#var_1_15~0.base|)) (not (= |~#var_1_14~0.base| ~var_1_2_Pointer~0.base)) (not (= ~var_1_2_Pointer~0.base ~var_1_7_Pointer~0.base)) (forall ((v_ArrVal_157 Int)) (<= 0 (select (store |#memory_int| |~#var_1_9~0.base| v_ArrVal_157) ~var_1_2_Pointer~0.base))) (not (= ~var_1_2_Pointer~0.base ~var_1_1_Pointer~0.base)) (not (= ~var_1_2_Pointer~0.base |~#var_1_16~0.base|)))";
		final String expectedResultAsString = "(and (not (= ~var_1_2_Pointer~0.base |~#var_1_15~0.base|)) (not (= |~#var_1_14~0.base| ~var_1_2_Pointer~0.base)) (not (= ~var_1_2_Pointer~0.base ~var_1_7_Pointer~0.base)) (<= 0 (select |#memory_int| ~var_1_2_Pointer~0.base)) (not (= ~var_1_2_Pointer~0.base ~var_1_1_Pointer~0.base)) (not (= ~var_1_2_Pointer~0.base |~#var_1_16~0.base|)) (not (= ~var_1_2_Pointer~0.base |~#var_1_9~0.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dd392dbb_97034d8b_Treesizes_34_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~pd2~0#1.base", "ULTIMATE.start_main_~pa~0#1.base"),
		};
		final String formulaAsString = "(and (= (+ (select |#memory_int| (+ (* (div (+ (* (- 1) |ULTIMATE.start_main_~pa~0#1.base|) |ULTIMATE.start_main_~pd2~0#1.base|) 4) (- 4)) |ULTIMATE.start_main_~pd2~0#1.base|)) 2 (div (+ (* (- 1) |ULTIMATE.start_main_~pa~0#1.base|) |ULTIMATE.start_main_~pd2~0#1.base|) 4)) 0) (= (mod (+ (* 3 |ULTIMATE.start_main_~pa~0#1.base|) |ULTIMATE.start_main_~pd2~0#1.base|) 4) 0))";
		final String expectedResultAsString = "(= |ULTIMATE.start_main_~pa~0#1.base| (+ 8 |ULTIMATE.start_main_~pd2~0#1.base| (* (select |#memory_int| |ULTIMATE.start_main_~pa~0#1.base|) 4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dde39be0_9b1e2239_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_linked_list_rbegin_~list#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_46| Int)) (<= 69 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_46| 12)))) (<= 69 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_rbegin_~list#1.base| 12))))";
		final String expectedResultAsString = "(<= 69 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_linked_list_rbegin_~list#1.base| 12)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_de66022d_de0c2fc7_Treesizes_104_97() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0", "~var_1_10~0", "~var_1_3~0", "~last_1_var_1_8~0"),
		};
		final String formulaAsString = "(and (or (= 256 ~last_1_var_1_8~0) (= 25 ~last_1_var_1_8~0) (and (or (not (= ~var_1_1~0 ~last_1_var_1_8~0)) (< (mod (+ (* (div ~var_1_3~0 65536) 4294901760) ~var_1_3~0 ~var_1_10~0) 4294967296) (+ (mod ~var_1_1~0 4294967296) 1))) (not (= ~last_1_var_1_8~0 (+ ~var_1_10~0 (mod ~var_1_3~0 65536)))))) (or (and (= ~var_1_1~0 25) (<= (mod ~last_1_var_1_8~0 4294967296) 24)) (and (= ~var_1_1~0 ~last_1_var_1_8~0) (<= 25 (mod ~last_1_var_1_8~0 4294967296)))) (or (< (mod ~var_1_1~0 4294967296) (mod (+ (* (div ~var_1_3~0 65536) 4294901760) ~var_1_3~0 ~var_1_10~0) 4294967296)) (and (<= 0 (div ~var_1_1~0 4294967296)) (= (div ~last_1_var_1_8~0 4294967296) 0) (or (< (div ~var_1_10~0 4294967296) (div (+ (* (div ~var_1_3~0 65536) (- 65536)) ~var_1_3~0 ~var_1_10~0) 4294967296)) (< ~last_1_var_1_8~0 257)) (<= 25 ~last_1_var_1_8~0))))";
		final String expectedResultAsString = "(let ((.cse3 (div ~var_1_3~0 65536))) (let ((.cse2 (mod ~var_1_1~0 4294967296)) (.cse1 (mod (+ (* .cse3 4294901760) ~var_1_3~0 ~var_1_10~0) 4294967296)) (.cse0 (= ~var_1_1~0 ~last_1_var_1_8~0))) (and (or (= 256 ~last_1_var_1_8~0) (= 25 ~last_1_var_1_8~0) (and (or (not .cse0) (< .cse1 (+ .cse2 1))) (not (= ~last_1_var_1_8~0 (+ ~var_1_10~0 (mod ~var_1_3~0 65536)))))) (or (< .cse2 .cse1) (and (= (div ~last_1_var_1_8~0 4294967296) 0) (or (< (div ~var_1_10~0 4294967296) (div (+ (* .cse3 (- 65536)) ~var_1_3~0 ~var_1_10~0) 4294967296)) (< ~last_1_var_1_8~0 257)) .cse0)) (or (and (= ~var_1_1~0 25) (<= (mod ~last_1_var_1_8~0 4294967296) 24)) (and (<= 25 ~last_1_var_1_8~0) .cse0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dec24eda_9e9f4858_Treesizes_55_28() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#y~0#1.base", "ULTIMATE.start_main_~#x~0#1.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| |ULTIMATE.start_main_~#y~0#1.base|) 1) (exists ((|ULTIMATE.start_main_~#c~0#1.base| Int) (|v_ULTIMATE.start_main_~#y~0#1.base_BEFORE_CALL_9| Int) (|v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_8| Int)) (and (<= (+ |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_8| 8) |ULTIMATE.start_main_~#c~0#1.base|) (<= (+ |v_ULTIMATE.start_main_~#y~0#1.base_BEFORE_CALL_9| 8) |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_8|) (= (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_8|) 1) (= (select |#memory_int| |ULTIMATE.start_main_~#c~0#1.base|) 1) (= (select |#memory_int| |v_ULTIMATE.start_main_~#y~0#1.base_BEFORE_CALL_9|) 1))) (<= (+ |ULTIMATE.start_main_~#y~0#1.base| 8) |ULTIMATE.start_main_~#x~0#1.base|) (= (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|) 1) (exists ((|v_ULTIMATE.start_main_~#c~0#1.base_12| Int)) (and (= (select |#memory_int| |v_ULTIMATE.start_main_~#c~0#1.base_12|) 1) (<= (+ |ULTIMATE.start_main_~#x~0#1.base| 8) |v_ULTIMATE.start_main_~#c~0#1.base_12|))))";
		final String expectedResultAsString = "(and (= (select |#memory_int| |ULTIMATE.start_main_~#y~0#1.base|) 1) (exists ((|ULTIMATE.start_main_~#c~0#1.base| Int)) (and (<= (+ |ULTIMATE.start_main_~#x~0#1.base| 8) |ULTIMATE.start_main_~#c~0#1.base|) (= (select |#memory_int| |ULTIMATE.start_main_~#c~0#1.base|) 1))) (<= (+ |ULTIMATE.start_main_~#y~0#1.base| 8) |ULTIMATE.start_main_~#x~0#1.base|) (= (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|) 1))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_df6d4af6_779b86d0_Treesizes_11_7() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~f1_6~0", "~f2_3~0", "~f2_7~0", "~f1_2~0"),
		};
		final String formulaAsString = "(and (= (+ ~f1_2~0 ~f2_7~0) (+ ~f1_6~0 ~f2_3~0)) (= ~f1_2~0 ~f1_6~0))";
		final String expectedResultAsString = "(and (= ~f2_7~0 ~f2_3~0) (= ~f1_2~0 ~f1_6~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dff9e58c_acd42319_Treesizes_8_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var1_Pointer~0.base"),
		};
		final String formulaAsString = "(not (= (mod (select |#memory_int| ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var1_Pointer~0.base) 65536) 0))";
		final String expectedResultAsString = "(<= 1 (mod (select |#memory_int| ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var1_Pointer~0.base) 65536))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e00867db_ac8b9aef_Treesizes_37_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#volArray~0#1.base", "ULTIMATE.start_main_~MINVAL~0#1"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_59 Int) (v_ArrVal_60 Int)) (or (< v_ArrVal_60 (select |#memory_int| (+ |ULTIMATE.start_main_~#volArray~0#1.base| (* |ULTIMATE.start_main_~i~0#1| 12) (- 8)))) (< |ULTIMATE.start_main_~MINVAL~0#1| (+ (select (store (store |#memory_int| (+ |ULTIMATE.start_main_~#volArray~0#1.base| (* |ULTIMATE.start_main_~i~0#1| 12) (- 8)) v_ArrVal_60) (+ |ULTIMATE.start_main_~#volArray~0#1.base| (- 12) (* |ULTIMATE.start_main_~i~0#1| 12)) v_ArrVal_59) (+ |ULTIMATE.start_main_~#volArray~0#1.base| 4)) 1))))";
		final String expectedResultAsString = "(<= |ULTIMATE.start_main_~MINVAL~0#1| (select |#memory_int| (+ |ULTIMATE.start_main_~#volArray~0#1.base| 4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e05dc24c_6efaae6_Treesizes_63_58() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0", "~var_1_20~0", "~var_1_4~0", "~var_1_5~0", "~var_1_6~0"),
		};
		final String formulaAsString = "(and (<= (+ (mod ~var_1_1~0 256) (mod ~var_1_6~0 256) (mod ~var_1_5~0 256)) (+ 255 ~var_1_1~0)) (<= (+ (mod ~var_1_20~0 4294967296) (* (div (+ (* (div ~var_1_20~0 4294967296) (- 4294967296)) ~var_1_20~0) (+ ~var_1_4~0 (* (div ~var_1_4~0 4294967296) (- 4294967296))) 4294967296) 4294967296) 1) (div (+ (* (div ~var_1_20~0 4294967296) (- 4294967296)) ~var_1_20~0) (+ ~var_1_4~0 (* (div ~var_1_4~0 4294967296) (- 4294967296))))) (= (mod ~var_1_1~0 256) (mod (+ ~var_1_6~0 ~var_1_5~0) 256)))";
		final String expectedResultAsString = "(and (let ((.cse0 (+ (* (div ~var_1_20~0 4294967296) (- 4294967296)) ~var_1_20~0)) (.cse1 (+ ~var_1_4~0 (* (div ~var_1_4~0 4294967296) (- 4294967296))))) (<= (+ (mod ~var_1_20~0 4294967296) (* (div .cse0 .cse1 4294967296) 4294967296) 1) (div .cse0 .cse1))) (<= (+ (mod ~var_1_6~0 256) (mod ~var_1_5~0 256)) ~var_1_1~0) (= (mod ~var_1_1~0 256) (mod (+ ~var_1_6~0 ~var_1_5~0) 256)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e10ac87c_f338d756_Treesizes_6_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_36~0"),
		};
		final String formulaAsString = "(not (= (mod ~var_1_36~0 256) 0))";
		final String expectedResultAsString = "(<= 1 (mod ~var_1_36~0 256))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e1764c6d_18957371_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_36| Int)) (<= 8699 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_36| 4)))) (<= 8699 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_harness_~#buf~3#1.base| 4))))";
		final String expectedResultAsString = "(<= 8699 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_harness_~#buf~3#1.base| 4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e1c6064e_dab1c8d7_Treesizes_17_17() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_20~0", "~var_1_7~0"),
		};
		final String formulaAsString = "(and (<= (div ~var_1_20~0 4294967296) (div ~var_1_7~0 4294967296)) (<= (+ ~var_1_7~0 (mod ~var_1_20~0 4294967296)) (+ 4294967295 ~var_1_20~0)))";
		final String expectedResultAsString = "(let ((.cse0 (+ ~var_1_7~0 (mod ~var_1_20~0 4294967296)))) (and (<= .cse0 (+ 4294967295 ~var_1_20~0)) (<= ~var_1_20~0 .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e21df5f0_605597c8_Treesizes_36_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "~SIZE~0", "ULTIMATE.start_main_~#a~0#1.base", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(and (or (and (<= 1 |ULTIMATE.start_main_~i~0#1|) (or (= (+ (select |#memory_int| (+ |ULTIMATE.start_main_~#a~0#1.base| 4)) (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|)) (+ (select |#memory_int| (+ 2 |ULTIMATE.start_main_~#a~0#1.base| (* 2 |ULTIMATE.start_main_~i~0#1|))) |ULTIMATE.start_main_~sum~0#1|)) (< 1 |ULTIMATE.start_main_~i~0#1|))) (< 3 ~SIZE~0)) (<= 3 ~SIZE~0))";
		final String expectedResultAsString = "(and (or (and (<= 1 |ULTIMATE.start_main_~i~0#1|) (or (< 1 |ULTIMATE.start_main_~i~0#1|) (= (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) |ULTIMATE.start_main_~sum~0#1|))) (< 3 ~SIZE~0)) (<= 3 ~SIZE~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e2515d4d_a0c0aaa2_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_47| Int)) (and (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_47| 4))) (<= (+ 16 |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_47|) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_46| Int)) (and (<= (+ 16 |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_46|) |#StackAllocations|) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_46| 4)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e2debcd2_cea8d2a8_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_~b#1.base_BEFORE_CALL_15| Int)) (<= 8687 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_~b#1.base_BEFORE_CALL_15| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_~b#1.base_BEFORE_CALL_13| Int)) (<= 8687 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_~b#1.base_BEFORE_CALL_13| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e2fa9d21_57a399f5_Treesizes_63_57() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~a~0#1.base", "~SIZE~0", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(and (or (= 1 (select |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| (* |ULTIMATE.start_main_~i~0#1| 4)))) (< (+ |ULTIMATE.start_main_~i~0#1| 1) ~SIZE~0)) (or (= (select |#memory_int| (+ (* ~SIZE~0 4) (- 4) |ULTIMATE.start_main_~a~0#1.base|)) 1) (< 4 ~SIZE~0)) (or (and (= 1 (select |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| 12))) (= (+ (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (select |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| 4)) (select |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| 8))) |ULTIMATE.start_main_~sum~0#1|)) (< (+ |ULTIMATE.start_main_~i~0#1| 1) ~SIZE~0)) (<= 4 ~SIZE~0))";
		final String expectedResultAsString = "(and (or (= (select |#memory_int| (+ (* ~SIZE~0 4) (- 4) |ULTIMATE.start_main_~a~0#1.base|)) 1) (< 4 ~SIZE~0)) (<= 4 ~SIZE~0) (or (and (= 1 (select |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| 12))) (= (+ (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (select |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| 4)) (select |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| 8))) |ULTIMATE.start_main_~sum~0#1|) (= 1 (select |#memory_int| (+ |ULTIMATE.start_main_~a~0#1.base| (* |ULTIMATE.start_main_~i~0#1| 4))))) (< (+ |ULTIMATE.start_main_~i~0#1| 1) ~SIZE~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e31b747c_cab9e92c_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#buf~3#1.base_BEFORE_CALL_61| Int)) (and (<= 8696 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#buf~3#1.base_BEFORE_CALL_61|))) (<= (+ 24 |v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#buf~3#1.base_BEFORE_CALL_61|) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#buf~3#1.base_BEFORE_CALL_59| Int)) (and (<= (+ 24 |v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#buf~3#1.base_BEFORE_CALL_59|) |#StackAllocations|) (<= 8696 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_harness_~#buf~3#1.base_BEFORE_CALL_59|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e37fea47_a97ff317_Treesizes_35_32() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_16_Pointer~0.base", "~var_1_11_Pointer~0.base", "~#var_1_18~0.base", "~#var_1_17~0.base"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_341 Int)) (or (< (mod (+ 254 (select (store |#memory_int| |~#var_1_17~0.base| v_ArrVal_341) ~var_1_11_Pointer~0.base)) 256) 254) (< (mod (+ 255 (select (store |#memory_int| |~#var_1_17~0.base| v_ArrVal_341) ~var_1_11_Pointer~0.base)) 256) 1))) (not (= ~var_1_11_Pointer~0.base |~#var_1_18~0.base|)) (not (= ~var_1_11_Pointer~0.base ~var_1_16_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~var_1_11_Pointer~0.base |~#var_1_18~0.base|)) (let ((.cse0 (select |#memory_int| ~var_1_11_Pointer~0.base))) (or (< (mod (+ .cse0 255) 256) 1) (< (mod (+ .cse0 254) 256) 254))) (not (= ~var_1_11_Pointer~0.base ~var_1_16_Pointer~0.base)) (not (= |~#var_1_17~0.base| ~var_1_11_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e3990694_ef4a01ff_Treesizes_21_15() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_step_~stepLocal_2~0#1", "~var_1_20~0"),
		};
		final String formulaAsString = "(and (<= 1 (mod ~var_1_20~0 65536)) (exists ((v_z_33 Int)) (and (<= 0 v_z_33) (<= 0 |ULTIMATE.start_step_~stepLocal_2~0#1|) (<= v_z_33 255) (not (= v_z_33 0)))))";
		final String expectedResultAsString = "(forall ((~var_1_12~0 Int)) (or (< ~var_1_12~0 (+ |ULTIMATE.start_step_~stepLocal_2~0#1| 1)) (not (= (* (mod ~var_1_20~0 65536) ~var_1_12~0) 0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e4686f4f_2fd80c33_Treesizes_13_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_mkdup_~a#1.base_BEFORE_CALL_7| Int)) (= (select |#memory_int| |v_ULTIMATE.start_mkdup_~a#1.base_BEFORE_CALL_7|) 0)) (exists ((|v_ULTIMATE.start_mkdup_~a#1.base_BEFORE_CALL_9| Int)) (= (select |#memory_int| |v_ULTIMATE.start_mkdup_~a#1.base_BEFORE_CALL_9|) 0)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_mkdup_~a#1.base_BEFORE_CALL_7| Int)) (= (select |#memory_int| |v_ULTIMATE.start_mkdup_~a#1.base_BEFORE_CALL_7|) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e4ea4866_5209e999_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "#StackAllocations"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_array_list_ensure_capacity_harness_~#list~0#1.base_BEFORE_CALL_18| Int)) (and (= (select |#memory_$Pointer$.base| (+ 16 |v_ULTIMATE.start_aws_array_list_ensure_capacity_harness_~#list~0#1.base_BEFORE_CALL_18|)) 0) (<= (+ 20 |v_ULTIMATE.start_aws_array_list_ensure_capacity_harness_~#list~0#1.base_BEFORE_CALL_18|) |#StackAllocations|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_array_list_ensure_capacity_harness_~#list~0#1.base_BEFORE_CALL_17| Int)) (and (= (select |#memory_$Pointer$.base| (+ 16 |v_ULTIMATE.start_aws_array_list_ensure_capacity_harness_~#list~0#1.base_BEFORE_CALL_17|)) 0) (<= (+ 20 |v_ULTIMATE.start_aws_array_list_ensure_capacity_harness_~#list~0#1.base_BEFORE_CALL_17|) |#StackAllocations|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e58e94b9_1bccf12d_Treesizes_16_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base", "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_140 Int)) (<= (mod (select (store |#memory_int| ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base v_ArrVal_140) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base) 256) 0)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (<= (mod (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base) 256) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e601de0d_2085f7ea_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_eq_ignore_case_harness_~#lhs~0#1.base"),
		};
		final String formulaAsString = "(and (<= 8687 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_eq_ignore_case_harness_~#lhs~0#1.base| 4))) (exists ((|v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_22| Int)) (<= 8687 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_harness_~#lhs~0#1.base_BEFORE_CALL_22| 4)))))";
		final String expectedResultAsString = "(<= 8687 (select |#memory_$Pointer$.base| (+ |ULTIMATE.start_aws_byte_buf_eq_ignore_case_harness_~#lhs~0#1.base| 4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e7175afa_c4921429_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_38| Int)) (and (<= (+ |v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_38| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_38|)) (<= 68 |v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_38|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_37| Int)) (and (<= 68 |v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_37|) (<= (+ |v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_37| 8) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_back_harness_~#list~0#1.base_BEFORE_CALL_37|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e75b3d22_cde60b8a_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_2| Int)) (= (select |#memory_$Pointer$.base| (+ 8 |v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_2|)) 0))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_3| Int)) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_3| 8)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e810dc4f_d62bfa97_Treesizes_63_24() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1", "ULTIMATE.start_main_~a~0#1", "ULTIMATE.start_main_~z~0#1", "ULTIMATE.start_main_~az~0#1"),
		};
		final String formulaAsString = "(and (<= |ULTIMATE.start_main_~z~0#1| 20) (or (not (= (mod (+ (* |ULTIMATE.start_main_~x~0#1| |ULTIMATE.start_main_~z~0#1|) |ULTIMATE.start_main_~a~0#1| (* 18446744073709551615 |ULTIMATE.start_main_~az~0#1| |ULTIMATE.start_main_~y~0#1|) (* 18446744073709551615 |ULTIMATE.start_main_~x~0#1|)) 18446744073709551616) 0)) (= (mod (+ (* |ULTIMATE.start_main_~x~0#1| |ULTIMATE.start_main_~z~0#1| |ULTIMATE.start_main_~z~0#1|) (* 18446744073709551615 |ULTIMATE.start_main_~x~0#1| |ULTIMATE.start_main_~z~0#1|) (* |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_main_~z~0#1|) (* 18446744073709551615 |ULTIMATE.start_main_~az~0#1| |ULTIMATE.start_main_~y~0#1| |ULTIMATE.start_main_~z~0#1|)) 18446744073709551616) 0)) (= |ULTIMATE.start_main_~y~0#1| 1) (<= |ULTIMATE.start_main_~a~0#1| 20) (<= 0 |ULTIMATE.start_main_~a~0#1|) (= |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_main_~x~0#1|) (= |ULTIMATE.start_main_~az~0#1| (* |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_main_~z~0#1|)) (<= 0 |ULTIMATE.start_main_~z~0#1|))";
		final String expectedResultAsString = "(and (<= |ULTIMATE.start_main_~z~0#1| 20) (= |ULTIMATE.start_main_~y~0#1| 1) (<= |ULTIMATE.start_main_~a~0#1| 20) (<= 0 |ULTIMATE.start_main_~a~0#1|) (= |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_main_~x~0#1|) (= |ULTIMATE.start_main_~az~0#1| (* |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_main_~z~0#1|)) (<= 0 |ULTIMATE.start_main_~z~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e88f364b_6e5bb1b1_Treesizes_81_44() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_string_eq_ignore_case_~b#1.base", "ULTIMATE.start_aws_string_eq_ignore_case_~a#1.base", "ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_b~1#1.base", "ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base"),
		};
		final String formulaAsString = "(and (exists ((v_y_12 Int)) (and (<= (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| 4)) (+ (* v_y_12 4294967296) 15)) (= (select |#memory_int| (+ (* v_y_12 (- 4294967296)) (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| 4)) |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| 8)) 0) (<= (* v_y_12 4294967296) (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| 4))))) (= |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| |ULTIMATE.start_aws_string_eq_ignore_case_~a#1.base|) (exists ((|v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_21| Int) (v_y_10 Int)) (and (<= (* v_y_10 4294967296) (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_21| 4))) (= (select |#memory_int| (+ (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_21| 4)) |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_21| 8 (* v_y_10 (- 4294967296)))) 0) (<= (select |#memory_int| (+ |v_ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base_BEFORE_CALL_21| 4)) (+ (* v_y_10 4294967296) 15)))) (= |ULTIMATE.start_aws_string_eq_ignore_case_~b#1.base| |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_b~1#1.base|))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| |ULTIMATE.start_aws_string_eq_ignore_case_~a#1.base|) (exists ((v_y_10 Int)) (let ((.cse1 (* v_y_10 4294967296)) (.cse0 (select |#memory_int| (+ |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| 4)))) (and (<= .cse0 (+ .cse1 15)) (= (select |#memory_int| (+ .cse0 |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_a~1#1.base| 8 (* v_y_10 (- 4294967296)))) 0) (<= .cse1 .cse0)))) (= |ULTIMATE.start_aws_string_eq_ignore_case_~b#1.base| |ULTIMATE.start_aws_string_eq_ignore_case_harness_~str_b~1#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e96a0844_3978fbcd_Treesizes_32_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_array_list_copy_harness_~#to~0#1.base", "#StackAllocations", "ULTIMATE.start_aws_array_list_copy_harness_~#from~0#1.base"),
		};
		final String formulaAsString = "(and (<= (+ |ULTIMATE.start_aws_array_list_copy_harness_~#from~0#1.base| 20) |ULTIMATE.start_aws_array_list_copy_harness_~#to~0#1.base|) (= (select |#memory_$Pointer$.base| (+ 16 |ULTIMATE.start_aws_array_list_copy_harness_~#from~0#1.base|)) 0) (<= (+ 44 |ULTIMATE.start_aws_array_list_copy_harness_~#from~0#1.base|) |#StackAllocations|) (exists ((|v_ULTIMATE.start_aws_array_list_copy_harness_~#from~0#1.base_BEFORE_CALL_21| Int)) (and (= (select |#memory_$Pointer$.base| (+ 16 |v_ULTIMATE.start_aws_array_list_copy_harness_~#from~0#1.base_BEFORE_CALL_21|)) 0) (<= (+ 44 |v_ULTIMATE.start_aws_array_list_copy_harness_~#from~0#1.base_BEFORE_CALL_21|) |#StackAllocations|))))";
		final String expectedResultAsString = "(and (<= (+ |ULTIMATE.start_aws_array_list_copy_harness_~#from~0#1.base| 20) |ULTIMATE.start_aws_array_list_copy_harness_~#to~0#1.base|) (= (select |#memory_$Pointer$.base| (+ 16 |ULTIMATE.start_aws_array_list_copy_harness_~#from~0#1.base|)) 0) (<= (+ 44 |ULTIMATE.start_aws_array_list_copy_harness_~#from~0#1.base|) |#StackAllocations|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e9e14c31_100d72a_Treesizes_80_75() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_1~0", "~var_1_5~0", "~var_1_13~0", "~var_1_8~0", "~var_1_9~0", "~var_1_7~0"),
		};
		final String formulaAsString = "(and (or (and (or (< (* ~var_1_1~0 ~var_1_1~0 ~var_1_13~0) (+ (* 256 (* (div ~var_1_13~0 256) ~var_1_1~0 ~var_1_1~0)) ~var_1_1~0)) (= (mod (+ ~var_1_8~0 ~var_1_7~0) 256) (mod ~var_1_5~0 256))) (or (< (+ (* 256 (* (div ~var_1_13~0 256) ~var_1_1~0 ~var_1_1~0)) ~var_1_1~0) (+ (* ~var_1_1~0 ~var_1_1~0 ~var_1_13~0) 1)) (= (mod ~var_1_7~0 256) (mod ~var_1_5~0 256)))) (and (= (mod (+ ~var_1_8~0 ~var_1_7~0) 256) (mod ~var_1_5~0 256)) (<= (+ (mod ~var_1_7~0 256) (mod ~var_1_8~0 256) (mod ~var_1_5~0 256)) (+ 255 ~var_1_5~0)))) (= ~var_1_9~0 1))";
		final String expectedResultAsString = "(and (= ~var_1_9~0 1) (let ((.cse4 (mod ~var_1_5~0 256))) (let ((.cse2 (= (mod (+ ~var_1_8~0 ~var_1_7~0) 256) .cse4)) (.cse3 (mod ~var_1_7~0 256))) (or (let ((.cse1 (+ (* 256 (* (div ~var_1_13~0 256) ~var_1_1~0 ~var_1_1~0)) ~var_1_1~0)) (.cse0 (* ~var_1_1~0 ~var_1_1~0 ~var_1_13~0))) (and (or (< .cse0 .cse1) .cse2) (or (< .cse1 (+ .cse0 1)) (= .cse3 .cse4)))) (and .cse2 (<= (+ .cse3 (mod ~var_1_8~0 256)) ~var_1_5~0))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ea5fef76_8405358b_Treesizes_7_3() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~len~0#1"),
		};
		final String formulaAsString = "(or (< |ULTIMATE.start_main_~len~0#1| 2) (= |ULTIMATE.start_main_~len~0#1| 2))";
		final String expectedResultAsString = "(<= |ULTIMATE.start_main_~len~0#1| 2)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_eaab1dc_d1b89502_Treesizes_17_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_26 Int) (v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_33 Int)) (and (not (= v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_33 v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_26)) (= (select |#memory_int| v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_33) (+ (* 2 (select |#memory_int| v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_26)) 1))))";
		final String expectedResultAsString = "(exists ((v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_25 Int) (v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_32 Int)) (and (not (= v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_32 v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_25)) (= (+ (* (select |#memory_int| v_func_to_recursive_line_29_to_40_0_~a.base_BEFORE_CALL_25) 2) 1) (select |#memory_int| v_func_to_recursive_line_29_to_40_0_~t.base_BEFORE_CALL_32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_eaf6503a_4038dcb9_Treesizes_5_3() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~0#1"),
		};
		final String formulaAsString = "(<= (div |ULTIMATE.start_main_~y~0#1| 2) 4)";
		final String expectedResultAsString = "(<= |ULTIMATE.start_main_~y~0#1| 9)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_eb9d4775_8b590c22_Treesizes_62_58() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~WrapperStruct00_var_1_1_Pointer~0.base", "~#WrapperStruct00~0.base", "~WrapperStruct00_var_1_5_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base", "~WrapperStruct00_var_1_12_Pointer~0.base", "~WrapperStruct00_var_1_2_Pointer~0.base", "~WrapperStruct00_var_1_7_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~WrapperStruct00_var_1_5_Pointer~0.base ~WrapperStruct00_var_1_2_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_4_Pointer~0.base ~WrapperStruct00_var_1_12_Pointer~0.base)) (<= (+ (mod (select |#memory_int| ~WrapperStruct00_var_1_4_Pointer~0.base) 65536) (mod (+ (* 65535 (select |#memory_int| ~WrapperStruct00_var_1_4_Pointer~0.base)) (select |#memory_int| ~WrapperStruct00_var_1_2_Pointer~0.base)) 65536)) 65535) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_2_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_4_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (= ~WrapperStruct00_var_1_4_Pointer~0.base (+ |~#WrapperStruct00~0.base| 6)) (not (= ~WrapperStruct00_var_1_2_Pointer~0.base ~WrapperStruct00_var_1_12_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_4_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_5_Pointer~0.base ~WrapperStruct00_var_1_4_Pointer~0.base)) (= ~WrapperStruct00_var_1_2_Pointer~0.base (+ |~#WrapperStruct00~0.base| 2)) (not (= ~WrapperStruct00_var_1_2_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)))";
		final String expectedResultAsString = "(let ((.cse0 (+ |~#WrapperStruct00~0.base| 6)) (.cse1 (+ |~#WrapperStruct00~0.base| 2))) (and (<= (mod (select |#memory_int| .cse0) 65536) (mod (select |#memory_int| .cse1) 65536)) (not (= ~WrapperStruct00_var_1_5_Pointer~0.base ~WrapperStruct00_var_1_2_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_4_Pointer~0.base ~WrapperStruct00_var_1_12_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_2_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_4_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base)) (= ~WrapperStruct00_var_1_4_Pointer~0.base .cse0) (not (= ~WrapperStruct00_var_1_2_Pointer~0.base ~WrapperStruct00_var_1_12_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_7_Pointer~0.base ~WrapperStruct00_var_1_4_Pointer~0.base)) (not (= ~WrapperStruct00_var_1_5_Pointer~0.base ~WrapperStruct00_var_1_4_Pointer~0.base)) (= ~WrapperStruct00_var_1_2_Pointer~0.base .cse1) (not (= ~WrapperStruct00_var_1_2_Pointer~0.base ~WrapperStruct00_var_1_1_Pointer~0.base))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ec2815ce_2a87fc75_Treesizes_128_102() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#array2~0#1.base", "ULTIMATE.start_main_~sum~0#1", "ULTIMATE.start_main_~#array1~0#1.base"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~sum~0#1| 0) (= (select |#memory_int| (+ 8 |ULTIMATE.start_main_~#array2~0#1.base|)) 0) (or (and (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array2~0#1.base| 4)) 0) (= (select |#memory_int| (+ 4 |ULTIMATE.start_main_~#array1~0#1.base|)) 0) (= 2 (select |#memory_int| (+ 8 |ULTIMATE.start_main_~#array1~0#1.base|))) (= (+ (select |#memory_int| |ULTIMATE.start_main_~#array2~0#1.base|) 2) 0)) (and (or (and (= (select |#memory_int| (+ |ULTIMATE.start_main_~#array2~0#1.base| 4)) 0) (= (select |#memory_int| (+ 4 |ULTIMATE.start_main_~#array1~0#1.base|)) 0) (= (select |#memory_int| |ULTIMATE.start_main_~#array2~0#1.base|) 0) (exists ((v_z_16 Int) (v_y_16 Int)) (and (<= (+ (* v_z_16 4294967295) (* v_y_16 4294967296)) 2) (<= 0 (+ (* v_z_16 4294967295) (* v_y_16 4294967296))) (<= 0 v_z_16) (<= v_z_16 4294967293)))) (and (= (select |#memory_int| (+ 4 |ULTIMATE.start_main_~#array1~0#1.base|)) 1) (= (select |#memory_int| |ULTIMATE.start_main_~#array2~0#1.base|) 0) (= (+ (select |#memory_int| (+ |ULTIMATE.start_main_~#array2~0#1.base| 4)) 1) 0))) (= (select |#memory_int| (+ 8 |ULTIMATE.start_main_~#array1~0#1.base|)) 0))) (= (+ 12 |ULTIMATE.start_main_~#array1~0#1.base|) |ULTIMATE.start_main_~#array2~0#1.base|) (= (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) 0))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_main_~sum~0#1| 0) (= (select |#memory_int| (+ 8 |ULTIMATE.start_main_~#array2~0#1.base|)) 0) (= (+ 12 |ULTIMATE.start_main_~#array1~0#1.base|) |ULTIMATE.start_main_~#array2~0#1.base|) (let ((.cse4 (select |#memory_int| (+ 4 |ULTIMATE.start_main_~#array1~0#1.base|))) (.cse6 (select |#memory_int| (+ |ULTIMATE.start_main_~#array2~0#1.base| 4)))) (let ((.cse0 (= .cse6 0)) (.cse1 (= .cse4 0)) (.cse3 (select |#memory_int| |ULTIMATE.start_main_~#array2~0#1.base|)) (.cse2 (select |#memory_int| (+ 8 |ULTIMATE.start_main_~#array1~0#1.base|)))) (or (and .cse0 .cse1 (= 2 .cse2) (= (+ .cse3 2) 0)) (and (let ((.cse5 (= .cse3 0))) (or (and (= .cse4 1) .cse5 (= (+ .cse6 1) 0)) (and .cse0 .cse1 .cse5))) (= .cse2 0))))) (= (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ecbc8032_c52fe499_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~#var_1_20~0.base", "~#var_1_19~0.base", "~var_1_17_Pointer~0.base", "~var_1_21_Pointer~0.base", "~var_1_22_Pointer~0.base", "~var_1_23_Pointer~0.base", "~var_1_19_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~var_1_23_Pointer~0.base ~var_1_17_Pointer~0.base)) (not (= |~#var_1_20~0.base| ~var_1_19_Pointer~0.base)) (not (= ~var_1_22_Pointer~0.base ~var_1_17_Pointer~0.base)) (not (= ~var_1_17_Pointer~0.base ~var_1_21_Pointer~0.base)) (= |~#var_1_19~0.base| ~var_1_19_Pointer~0.base))";
		final String expectedResultAsString = "(and (not (= ~var_1_23_Pointer~0.base ~var_1_17_Pointer~0.base)) (not (= ~var_1_22_Pointer~0.base ~var_1_17_Pointer~0.base)) (not (= ~var_1_17_Pointer~0.base ~var_1_21_Pointer~0.base)) (not (= |~#var_1_20~0.base| |~#var_1_19~0.base|)) (= |~#var_1_19~0.base| ~var_1_19_Pointer~0.base))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ed32da2a_b410c1e1_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_from_whole_buffer_~buf#1.base_BEFORE_CALL_3| Int)) (<= 8696 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_write_from_whole_buffer_~buf#1.base_BEFORE_CALL_3| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_from_whole_buffer_~buf#1.base_BEFORE_CALL_1| Int)) (<= 8696 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_write_from_whole_buffer_~buf#1.base_BEFORE_CALL_1| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ed5bac87_4934773b_Treesizes_21_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_4| Int) (|v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_6| Int)) (and (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_6| 4)) 0) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_4| 8) |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_6|) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_4| 4)) 0)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2| Int) (|v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| Int)) (and (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| 4)) 0) (<= (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2| 8) |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4|) (= (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2| 4)) 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_edfded36_e81d67a3_Treesizes_11_11() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_array_eq_ignore_case_harness_~rhs_len~0#1", "ULTIMATE.start_aws_array_eq_ignore_case_harness_~lhs_len~0#1"),
		};
		final String formulaAsString = "(and (= (mod |ULTIMATE.start_aws_array_eq_ignore_case_harness_~lhs_len~0#1| 4294967296) 0) (= (mod |ULTIMATE.start_aws_array_eq_ignore_case_harness_~rhs_len~0#1| 4294967296) 0))";
		final String expectedResultAsString = "(and (<= (mod |ULTIMATE.start_aws_array_eq_ignore_case_harness_~rhs_len~0#1| 4294967296) 0) (<= (mod |ULTIMATE.start_aws_array_eq_ignore_case_harness_~lhs_len~0#1| 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ee881a46_fa7a291_Treesizes_30_28() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_12~0", "~var_1_3~0", "~var_1_13~0", "~var_1_9~0"),
		};
		final String formulaAsString = "(and (<= (+ (mod ~var_1_3~0 4294967296) (mod (+ (* 4294967295 ~var_1_3~0) ~var_1_9~0) 4294967296)) 4294967295) (<= (+ (mod ~var_1_13~0 256) ~var_1_12~0) (+ 255 ~var_1_13~0)) (= (mod ~var_1_13~0 256) (mod ~var_1_12~0 256)))";
		final String expectedResultAsString = "(and (<= (+ (mod ~var_1_3~0 4294967296) (mod (+ (* 4294967295 ~var_1_3~0) ~var_1_9~0) 4294967296)) 4294967295) (= (mod ~var_1_13~0 256) (mod ~var_1_12~0 256)) (<= (div ~var_1_12~0 256) (div ~var_1_13~0 256)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ef28a397_bda2f8ff_Treesizes_304_56() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "sum_#in~x.base", "sum_#res"),
		};
		final String formulaAsString = "(and (or (< (mod (+ (* (select |#memory_int| (+ |sum_#in~x.base| 24)) 4294967295) (* (select |#memory_int| (+ |sum_#in~x.base| 28)) 4294967295) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 12))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 32))) 4294967295 (* 4294967295 (select |#memory_int| |sum_#in~x.base|)) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 4))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 16))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 8))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 20))) (* (select |#memory_int| (+ |sum_#in~x.base| 36)) 4294967295)) 4294967296) 2147483648) (= 4294967295 (+ |sum_#res| (mod (+ (* (select |#memory_int| (+ |sum_#in~x.base| 24)) 4294967295) (* (select |#memory_int| (+ |sum_#in~x.base| 28)) 4294967295) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 12))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 32))) 4294967295 (* 4294967295 (select |#memory_int| |sum_#in~x.base|)) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 4))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 16))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 8))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 20))) (* (select |#memory_int| (+ |sum_#in~x.base| 36)) 4294967295)) 4294967296)))) (or (= (+ |sum_#res| (mod (+ (* (select |#memory_int| (+ |sum_#in~x.base| 24)) 4294967295) (* (select |#memory_int| (+ |sum_#in~x.base| 28)) 4294967295) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 12))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 32))) 4294967295 (* 4294967295 (select |#memory_int| |sum_#in~x.base|)) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 4))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 16))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 8))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 20))) (* (select |#memory_int| (+ |sum_#in~x.base| 36)) 4294967295)) 4294967296) 1) 0) (< (mod (+ 2147483647 (* (select |#memory_int| (+ |sum_#in~x.base| 24)) 4294967295) (* (select |#memory_int| (+ |sum_#in~x.base| 28)) 4294967295) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 12))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 32))) (* 4294967295 (select |#memory_int| |sum_#in~x.base|)) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 4))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 16))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 8))) (* 4294967295 (select |#memory_int| (+ |sum_#in~x.base| 20))) (* (select |#memory_int| (+ |sum_#in~x.base| 36)) 4294967295)) 4294967296) 2147483648)))";
		final String expectedResultAsString = "(= (mod (+ (select |#memory_int| (+ |sum_#in~x.base| 28)) (select |#memory_int| (+ |sum_#in~x.base| 36)) (select |#memory_int| (+ |sum_#in~x.base| 24)) (select |#memory_int| (+ |sum_#in~x.base| 32)) (select |#memory_int| |sum_#in~x.base|) (select |#memory_int| (+ |sum_#in~x.base| 20)) (select |#memory_int| (+ |sum_#in~x.base| 16)) (select |#memory_int| (+ |sum_#in~x.base| 12)) 2147483648 (select |#memory_int| (+ |sum_#in~x.base| 4)) (select |#memory_int| (+ |sum_#in~x.base| 8))) 4294967296) (+ |sum_#res| 2147483648))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f005f462_3c751a60_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_22| Int)) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_22| 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_21| Int)) (<= 8682 (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_byte_buf_init_copy_harness_~#src~0#1.base_BEFORE_CALL_21| 4))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f02065c_873b0c82_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_buf_write_~buf.base_BEFORE_CALL_14 Int)) (<= (mod (+ 4294967295 (* 4294967295 (select |#memory_int| (+ 8 v_aws_byte_buf_write_~buf.base_BEFORE_CALL_14)))) 4294967296) 4294967294))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_write_be16_~buf#1.base_BEFORE_CALL_18| Int)) (<= (mod (+ (* (select |#memory_int| (+ |v_ULTIMATE.start_aws_byte_buf_write_be16_~buf#1.base_BEFORE_CALL_18| 8)) 4294967295) 4294967295) 4294967296) 4294967294))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f08d1955_bfc5d5b7_Treesizes_32_30() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_11~0", "~var_1_10~0", "~var_1_8~0", "~var_1_7~0", "~var_1_17~0"),
		};
		final String formulaAsString = "(and (<= 0 (div ~var_1_7~0 4294967296)) (<= (+ ~var_1_11~0 1 (mod ~var_1_10~0 256)) 0) (<= ~var_1_17~0 (+ 511 ~var_1_11~0)) (<= (+ 192 ~var_1_7~0 ~var_1_11~0) (mod ~var_1_8~0 256)) (<= 0 (div ~var_1_17~0 256)))";
		final String expectedResultAsString = "(and (<= 0 (div ~var_1_7~0 4294967296)) (<= (+ ~var_1_11~0 1 (mod ~var_1_10~0 256)) 0) (<= ~var_1_17~0 (+ 511 ~var_1_11~0)) (<= (+ 192 ~var_1_7~0 ~var_1_11~0) (mod ~var_1_8~0 256)) (<= 0 ~var_1_17~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f0fcd548_7cfaf043_Treesizes_56_44() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~last_1_var_1_25~0", "~var_1_32~0", "~var_1_25~0", "~var_1_18~0"),
		};
		final String formulaAsString = "(and (<= (div ~last_1_var_1_25~0 4294967296) 0) (<= (+ 52 (mod ~last_1_var_1_25~0 4294967296)) (+ ~last_1_var_1_25~0 ~var_1_32~0)) (or (and (<= 0 (div ~var_1_25~0 4294967296)) (or (= (+ 103 ~var_1_18~0) (+ ~var_1_32~0 (* (div ~last_1_var_1_25~0 4294967296) 8589934592))) (< (+ 103 ~var_1_18~0) (+ ~var_1_32~0 (* (div ~last_1_var_1_25~0 4294967296) 8589934592)))) (= ~var_1_18~0 ~var_1_25~0)) (= 2 ~var_1_25~0)) (<= (div ~var_1_32~0 65536) 0))";
		final String expectedResultAsString = "(let ((.cse0 (div ~last_1_var_1_25~0 4294967296))) (and (or (= 2 ~var_1_25~0) (and (<= (+ 103 ~var_1_18~0) (+ ~var_1_32~0 (* .cse0 8589934592))) (<= 0 (div ~var_1_25~0 4294967296)) (= ~var_1_18~0 ~var_1_25~0))) (<= .cse0 0) (<= (+ 52 (mod ~last_1_var_1_25~0 4294967296)) (+ ~last_1_var_1_25~0 ~var_1_32~0)) (<= (div ~var_1_32~0 65536) 0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f182e80_dcb58996_Treesizes_24_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#volArray~0#1.base", "ULTIMATE.start_main_~MINVAL~0#1"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_124 Int) (v_ArrVal_123 Int)) (<= |ULTIMATE.start_main_~MINVAL~0#1| (select (store (store |#memory_int| (+ (* |ULTIMATE.start_main_~i~0#1| 8) |ULTIMATE.start_main_~#volArray~0#1.base| (- 4)) v_ArrVal_123) (+ (* |ULTIMATE.start_main_~i~0#1| 8) |ULTIMATE.start_main_~#volArray~0#1.base| (- 8)) v_ArrVal_124) (+ 16 |ULTIMATE.start_main_~#volArray~0#1.base|))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_124 Int)) (<= |ULTIMATE.start_main_~MINVAL~0#1| (select (store |#memory_int| (+ (* |ULTIMATE.start_main_~i~0#1| 8) |ULTIMATE.start_main_~#volArray~0#1.base| (- 8)) v_ArrVal_124) (+ 16 |ULTIMATE.start_main_~#volArray~0#1.base|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f28f7703_92366508_Treesizes_10_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_57| Int)) (and (<= 69 (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_57|)) (<= 79 |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_57|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_56| Int)) (and (<= 79 |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_56|) (<= 69 (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_56|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f2dc8f52_7174cb32_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_4_Pointer~0.base"),
		};
		final String formulaAsString = "(= (mod (select |#memory_int| ~var_1_4_Pointer~0.base) 256) 0)";
		final String expectedResultAsString = "(<= (mod (select |#memory_int| ~var_1_4_Pointer~0.base) 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f362e70_e2f4cc5c_Treesizes_183_36() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "memset_impl_#in~c", "memset_impl_#in~s.base", "memset_impl_~sp~0.base", "memset_impl_~c"),
		};
		final String formulaAsString = "(and (or (and (exists ((v_DerPreprocessor_15 Int) (v_z_22 Int)) (and (= (select |#memory_int| (+ memset_impl_~sp~0.base v_z_22)) (mod memset_impl_~c 256)) (<= v_z_22 2147483647) (= (select (store (store |#memory_int| (+ memset_impl_~sp~0.base v_z_22) v_DerPreprocessor_15) (+ memset_impl_~sp~0.base v_z_22 (- 4294967296)) (select |#memory_int| (+ memset_impl_~sp~0.base v_z_22))) memset_impl_~sp~0.base) (mod memset_impl_~c 256)) (<= 0 v_z_22))) (<= (mod memset_impl_~c 256) 127)) (and (exists ((v_DerPreprocessor_15 Int) (v_z_22 Int)) (and (<= v_z_22 2147483647) (= (+ (select (store (store |#memory_int| (+ memset_impl_~sp~0.base v_z_22) v_DerPreprocessor_15) (+ memset_impl_~sp~0.base v_z_22 (- 4294967296)) (select |#memory_int| (+ memset_impl_~sp~0.base v_z_22))) memset_impl_~sp~0.base) 256) (mod memset_impl_~c 256)) (<= 0 v_z_22) (= (+ 256 (select |#memory_int| (+ memset_impl_~sp~0.base v_z_22))) (mod memset_impl_~c 256)))) (<= 128 (mod memset_impl_~c 256))) (and (or (and (<= (mod memset_impl_~c 256) 127) (= (select |#memory_int| memset_impl_~sp~0.base) (mod memset_impl_~c 256))) (and (= (mod memset_impl_~c 256) (+ (select |#memory_int| memset_impl_~sp~0.base) 256)) (<= 128 (mod memset_impl_~c 256)))) (or (and (exists ((v_z_22 Int)) (and (= (mod memset_impl_~c 256) (+ 256 (select |#memory_int| (+ memset_impl_~sp~0.base v_z_22 (- 4294967296))))) (<= 2147483648 v_z_22) (<= v_z_22 4294967295))) (<= 128 (mod memset_impl_~c 256))) (and (exists ((v_z_22 Int)) (and (= (mod memset_impl_~c 256) (select |#memory_int| (+ memset_impl_~sp~0.base v_z_22 (- 4294967296)))) (<= 2147483648 v_z_22) (<= v_z_22 4294967295))) (<= (mod memset_impl_~c 256) 127))))) (= memset_impl_~sp~0.base |memset_impl_#in~s.base|) (= |memset_impl_#in~c| memset_impl_~c))";
		final String expectedResultAsString = "(and (= memset_impl_~sp~0.base |memset_impl_#in~s.base|) (= |memset_impl_#in~c| memset_impl_~c) (let ((.cse1 (select |#memory_int| memset_impl_~sp~0.base)) (.cse0 (mod memset_impl_~c 256))) (or (and (<= .cse0 127) (= .cse1 .cse0)) (and (= .cse0 (+ .cse1 256)) (<= 128 .cse0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f3e72d5d_f6234e8e_Treesizes_13_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "aws_byte_buf_write_~buf.base"),
		};
		final String formulaAsString = "(<= (mod (+ (* 4294967295 (select |#memory_int| (+ 8 aws_byte_buf_write_~buf.base))) 4294967295) 4294967296) 4294967294)";
		final String expectedResultAsString = "(<= 1 (mod (select |#memory_int| (+ 8 aws_byte_buf_write_~buf.base)) 4294967296))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f4ab9dc4_22bd5b47_Treesizes_52_47() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "~SIZE~0", "ULTIMATE.start_main_~#a~0#1.base", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(or (and (<= |ULTIMATE.start_main_~i~0#1| ~SIZE~0) (not (= ~SIZE~0 |ULTIMATE.start_main_~i~0#1|))) (= (+ (select |#memory_int| (+ (- 2) |ULTIMATE.start_main_~#a~0#1.base| (* ~SIZE~0 2))) (select |#memory_int| (+ 2 |ULTIMATE.start_main_~#a~0#1.base|)) (select |#memory_int| (+ |ULTIMATE.start_main_~#a~0#1.base| (* ~SIZE~0 2) (- 8))) (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) (select |#memory_int| (+ (- 4) |ULTIMATE.start_main_~#a~0#1.base| (* ~SIZE~0 2))) (select |#memory_int| (+ (- 6) |ULTIMATE.start_main_~#a~0#1.base| (* ~SIZE~0 2)))) |ULTIMATE.start_main_~sum~0#1|))";
		final String expectedResultAsString = "(or (< |ULTIMATE.start_main_~i~0#1| ~SIZE~0) (= (let ((.cse0 (* ~SIZE~0 2))) (+ (select |#memory_int| (+ (- 2) |ULTIMATE.start_main_~#a~0#1.base| .cse0)) (select |#memory_int| (+ 2 |ULTIMATE.start_main_~#a~0#1.base|)) (select |#memory_int| (+ |ULTIMATE.start_main_~#a~0#1.base| .cse0 (- 8))) (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) (select |#memory_int| (+ (- 4) |ULTIMATE.start_main_~#a~0#1.base| .cse0)) (select |#memory_int| (+ (- 6) |ULTIMATE.start_main_~#a~0#1.base| .cse0)))) |ULTIMATE.start_main_~sum~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f5259fcf_e2c591d_Treesizes_7_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~b~0"),
		};
		final String formulaAsString = "(<= (mod (+ ~b~0 1) 4294967296) 0)";
		final String expectedResultAsString = "(<= 4294967295 (mod ~b~0 4294967296))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f54d75e3_a61cb0d7_Treesizes_52_52() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var0_Pointer~0.base", "~#unsigned_long_int_Array_0~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base", "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base", "~#signed_long_int_Array_0~0.base", "~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base)) (forall ((v_ArrVal_610 Int)) (<= (mod (select (store |#memory_int| |~#signed_long_int_Array_0~0.base| v_ArrVal_610) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base) 256) 0)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ |~#signed_long_int_Array_0~0.base| 4))) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ |~#signed_long_int_Array_0~0.base| 8))) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ |~#unsigned_long_int_Array_0~0.base| 4))) (not (= ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base ~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var0_Pointer~0.base)) (not (= (+ |~#signed_long_int_Array_0~0.base| 16) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ |~#signed_long_int_Array_0~0.base| 4))) (not (= ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ |~#signed_long_int_Array_0~0.base| 8))) (<= (mod (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base) 256) 0) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base (+ |~#unsigned_long_int_Array_0~0.base| 4))) (not (= |~#signed_long_int_Array_0~0.base| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)) (not (= ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base ~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var0_Pointer~0.base)) (not (= (+ |~#signed_long_int_Array_0~0.base| 16) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f653f037_5a813c18_Treesizes_10_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~a~0#1.base", "ULTIMATE.start_main_~p~0#1.base"),
		};
		final String formulaAsString = "(and (not (= |ULTIMATE.start_main_~a~0#1.base| |ULTIMATE.start_main_~p~0#1.base|)) (= (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 2))";
		final String expectedResultAsString = "(forall ((v_ArrVal_24 Int)) (= (select (store |#memory_int| |ULTIMATE.start_main_~p~0#1.base| v_ArrVal_24) |ULTIMATE.start_main_~a~0#1.base|) 2))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f6dfac03_637489a8_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_buf_append_~from.base_BEFORE_CALL_3 Int)) (<= (mod (select |#memory_int| v_aws_byte_buf_append_~from.base_BEFORE_CALL_3) 4294967296) 0))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_harness_~#from~0#1.base_BEFORE_CALL_9| Int)) (<= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_append_harness_~#from~0#1.base_BEFORE_CALL_9|) 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f76b9dab_ae607361_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_12 Int)) (and (<= v_aws_linked_list_front_~list.base_BEFORE_CALL_12 (select |#memory_$Pointer$.base| (+ v_aws_linked_list_front_~list.base_BEFORE_CALL_12 12))) (<= 69 v_aws_linked_list_front_~list.base_BEFORE_CALL_12)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_18| Int)) (and (<= 69 |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_18|) (<= |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_18| (select |#memory_$Pointer$.base| (+ |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_18| 12)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f7a0a4a9_4fa01f89_Treesizes_11_9() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "node_create_~temp~0#1.base", "old(#HeapAllocations)", "#HeapAllocations"),
		};
		final String formulaAsString = "(and (= |#HeapAllocations| (+ |node_create_~temp~0#1.base| 8)) (= |#HeapAllocations| (+ 8 |old(#HeapAllocations)|)))";
		final String expectedResultAsString = "(and (= |#HeapAllocations| (+ 8 |old(#HeapAllocations)|)) (= |node_create_~temp~0#1.base| |old(#HeapAllocations)|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f8420c56_4380c554_Treesizes_27_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base", "#StackAllocations"),
		};
		final String formulaAsString = "(and (<= (+ 8 |ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base|) |#StackAllocations|) (exists ((|v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_25| Int)) (and (<= (+ |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_25| 8) |#StackAllocations|) (<= (mod (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base_BEFORE_CALL_25|) 4294967296) 0))) (<= (mod (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base|) 4294967296) 0))";
		final String expectedResultAsString = "(and (<= (+ 8 |ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base|) |#StackAllocations|) (<= (mod (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_read_common_harness_~#cur~3#1.base|) 4294967296) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f8b8b595_99e3aa27_Treesizes_135_75() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#WrapperStruct00~0.base", "ULTIMATE.start_property_#t~mem105#1"),
		};
		final String formulaAsString = "(and (or (and (<= 32768 (mod (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5))) 65536)) (= (mod (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5))) 65536) (+ 65536 |ULTIMATE.start_property_#t~mem105#1|))) (and (= (mod (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5))) 65536) |ULTIMATE.start_property_#t~mem105#1|) (<= (mod (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5))) 65536) 32767))) (or (and (= (mod (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5))) 65536) (+ 65536 (select |#memory_int| |~#WrapperStruct00~0.base|))) (<= 32768 (mod (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5))) 65536))) (and (<= (mod (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5))) 65536) 32767) (= (mod (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5))) 65536) (select |#memory_int| |~#WrapperStruct00~0.base|)))))";
		final String expectedResultAsString = "(let ((.cse1 (select |#memory_int| |~#WrapperStruct00~0.base|))) (and (let ((.cse0 (mod (+ (select |#memory_int| (+ |~#WrapperStruct00~0.base| 3)) (select |#memory_int| (+ |~#WrapperStruct00~0.base| 5))) 65536))) (or (and (= .cse0 (+ 65536 .cse1)) (<= 32768 .cse0)) (and (<= .cse0 32767) (= .cse0 .cse1)))) (= |ULTIMATE.start_property_#t~mem105#1| .cse1)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f954a6e6_6c25e574_Treesizes_7_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ldv_snd_register_oss_device_ldv_dispatch_register_2_2_#t~ret69#1.base"),
		};
		final String formulaAsString = "(<= (mod (+ |ldv_snd_register_oss_device_ldv_dispatch_register_2_2_#t~ret69#1.base| 4294967295) 4294967296) 4294967294)";
		final String expectedResultAsString = "(<= 1 (mod |ldv_snd_register_oss_device_ldv_dispatch_register_2_2_#t~ret69#1.base| 4294967296))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f9ad6f0d_6dde5ce8_Treesizes_19_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#a~0#1.base"),
		};
		final String formulaAsString = "(and (<= 7 (select |#memory_int| (+ 20 |ULTIMATE.start_main_~#a~0#1.base|))) (exists ((|v_ULTIMATE.start_main_~#a~0#1.base_BEFORE_CALL_9| Int)) (<= 7 (select |#memory_int| (+ |v_ULTIMATE.start_main_~#a~0#1.base_BEFORE_CALL_9| 20)))) (= 6 |ULTIMATE.start_main_~i~0#1|))";
		final String expectedResultAsString = "(and (<= 7 (select |#memory_int| (+ 20 |ULTIMATE.start_main_~#a~0#1.base|))) (= 6 |ULTIMATE.start_main_~i~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f9f34d56_f156c4d9_Treesizes_30_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_sll_circular_create_~last~0#1.base", "ULTIMATE.start_sll_circular_create_~head~0#1.base"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~#s~0#1.base| Int) (v_ArrVal_118 Int)) (or (not (= (select (store |#memory_$Pointer$.base| |ULTIMATE.start_sll_circular_create_~last~0#1.base| v_ArrVal_118) |ULTIMATE.start_main_~#s~0#1.base|) (select (store |#memory_$Pointer$.base| |ULTIMATE.start_sll_circular_create_~last~0#1.base| v_ArrVal_118) (select (store |#memory_$Pointer$.base| |ULTIMATE.start_sll_circular_create_~last~0#1.base| v_ArrVal_118) |ULTIMATE.start_main_~#s~0#1.base|)))) (not (= (select (store |#memory_$Pointer$.base| |ULTIMATE.start_sll_circular_create_~last~0#1.base| v_ArrVal_118) |ULTIMATE.start_main_~#s~0#1.base|) |ULTIMATE.start_sll_circular_create_~head~0#1.base|))))";
		final String expectedResultAsString = "(and (not (= |ULTIMATE.start_sll_circular_create_~head~0#1.base| (select |#memory_$Pointer$.base| |ULTIMATE.start_sll_circular_create_~head~0#1.base|))) (not (= |ULTIMATE.start_sll_circular_create_~head~0#1.base| |ULTIMATE.start_sll_circular_create_~last~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fa4333b8_b603843a_Treesizes_16_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~bcki~0#1.base"),
		};
		final String formulaAsString = "(and (not (= (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~bcki~0#1.base|) (+ 4 |ULTIMATE.start_main_~bcki~0#1.base|))) (= (select |#memory_$Pointer$.base| (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~bcki~0#1.base|)) 0))";
		final String expectedResultAsString = "(forall ((v_ArrVal_534 Int)) (= (select (store |#memory_$Pointer$.base| (+ 4 |ULTIMATE.start_main_~bcki~0#1.base|) v_ArrVal_534) (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~bcki~0#1.base|)) 0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fb178916_5b4be729_Treesizes_32_32() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#var_1_11~0.base", "~#var_1_13~0.base", "~#var_1_12~0.base", "~#var_1_14~0.base", "~var_1_9_Pointer~0.base", "~#var_1_15~0.base", "~#var_1_16~0.base"),
		};
		final String formulaAsString = "(and (not (= ~var_1_9_Pointer~0.base |~#var_1_16~0.base|)) (not (= ~var_1_9_Pointer~0.base |~#var_1_15~0.base|)) (not (= ~var_1_9_Pointer~0.base |~#var_1_13~0.base|)) (not (= |~#var_1_14~0.base| ~var_1_9_Pointer~0.base)) (forall ((v_ArrVal_428 Int)) (<= (mod (select (store |#memory_int| |~#var_1_11~0.base| v_ArrVal_428) ~var_1_9_Pointer~0.base) 256) 0)) (not (= |~#var_1_12~0.base| ~var_1_9_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~var_1_9_Pointer~0.base |~#var_1_16~0.base|)) (not (= ~var_1_9_Pointer~0.base |~#var_1_11~0.base|)) (not (= ~var_1_9_Pointer~0.base |~#var_1_15~0.base|)) (not (= ~var_1_9_Pointer~0.base |~#var_1_13~0.base|)) (not (= |~#var_1_14~0.base| ~var_1_9_Pointer~0.base)) (<= (mod (select |#memory_int| ~var_1_9_Pointer~0.base) 256) 0) (not (= |~#var_1_12~0.base| ~var_1_9_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fb965c36_e99601b6_Treesizes_18_16() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~var_112_arg_0~0#1", "ULTIMATE.start_main_~var_112_arg_1~0#1", "ULTIMATE.start_main_~var_115~0#1"),
		};
		final String formulaAsString = "(and (<= 0 (div |ULTIMATE.start_main_~var_112_arg_1~0#1| 256)) (<= (+ |ULTIMATE.start_main_~var_112_arg_1~0#1| (mod (+ |ULTIMATE.start_main_~var_112_arg_0~0#1| 1) 256)) 1) (= |ULTIMATE.start_main_~var_115~0#1| 1))";
		final String expectedResultAsString = "(and (<= 0 |ULTIMATE.start_main_~var_112_arg_1~0#1|) (<= (+ |ULTIMATE.start_main_~var_112_arg_1~0#1| (mod (+ |ULTIMATE.start_main_~var_112_arg_0~0#1| 1) 256)) 1) (= |ULTIMATE.start_main_~var_115~0#1| 1))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fc33c37f_2a16189c_Treesizes_9_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base"),
		};
		final String formulaAsString = "(<= (mod (+ (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base) 255) 256) 254)";
		final String expectedResultAsString = "(<= 1 (mod (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base) 256))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fcf2d75c_2644eed9_Treesizes_52_31() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "addflt_#in~a", "addflt_#in~b", "addflt_#res"),
		};
		final String formulaAsString = "(and (<= 4294967295 (+ (mod (+ (* 4294967295 |addflt_#in~b|) 4294967295) 4294967296) (mod |addflt_#res| 4294967296))) (or (< (mod |addflt_#in~a| 4294967296) (mod |addflt_#in~b| 4294967296)) (forall ((v_z_28 Int) (v_y_28 Int)) (or (< (+ (* v_z_28 4294967296) (* v_y_28 4294967296) (mod |addflt_#res| 4294967296)) 4294967296) (< 4294967295 (+ v_z_28 (mod |addflt_#res| 4294967296))) (< 4294967295 (+ (* v_y_28 4294967296) (* v_z_28 4294967295)))))))";
		final String expectedResultAsString = "(and (<= 4294967295 (+ (mod (+ (* 4294967295 |addflt_#in~b|) 4294967295) 4294967296) (mod |addflt_#res| 4294967296))) (or (< (mod (+ 4294967295 (* 4294967295 |addflt_#res|)) 4294967296) 1) (< (mod |addflt_#in~a| 4294967296) (mod |addflt_#in~b| 4294967296))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fd445d4e_69a92421_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~WrapperStruct00_var_1_10_Pointer~0.base", "~WrapperStruct00_var_1_12_Pointer~0.base", "~WrapperStruct00_var_1_13_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~WrapperStruct00_var_1_10_Pointer~0.base ~WrapperStruct00_var_1_13_Pointer~0.base)) (= (mod (select |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base) 256) 0))";
		final String expectedResultAsString = "(and (<= (mod (select |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base) 256) 0) (not (= ~WrapperStruct00_var_1_10_Pointer~0.base ~WrapperStruct00_var_1_13_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fdae5f8c_f3d60bd3_Treesizes_34_34() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "~#var_1_21~0.base", "~var_1_16_Pointer~0.base", "~var_1_13_Pointer~0.base", "~var_1_18_Pointer~0.base", "~#var_1_19~0.base", "~var_1_22_Pointer~0.base", "~var_1_20_Pointer~0.base", "~var_1_10_Pointer~0.base"),
		};
		final String formulaAsString = "(and (not (= ~var_1_13_Pointer~0.base ~var_1_18_Pointer~0.base)) (not (= |~#var_1_21~0.base| ~var_1_16_Pointer~0.base)) (not (= ~var_1_13_Pointer~0.base ~var_1_22_Pointer~0.base)) (not (= ~var_1_13_Pointer~0.base ~var_1_10_Pointer~0.base)) (forall ((v_ArrVal_419 Int)) (<= (mod (+ 255 (select (store |#memory_int| |~#var_1_19~0.base| v_ArrVal_419) ~var_1_16_Pointer~0.base)) 256) 254)) (not (= ~var_1_13_Pointer~0.base ~var_1_20_Pointer~0.base)))";
		final String expectedResultAsString = "(and (not (= ~var_1_13_Pointer~0.base ~var_1_18_Pointer~0.base)) (not (= |~#var_1_21~0.base| ~var_1_16_Pointer~0.base)) (not (= ~var_1_13_Pointer~0.base ~var_1_22_Pointer~0.base)) (not (= ~var_1_13_Pointer~0.base ~var_1_10_Pointer~0.base)) (<= (mod (+ (select |#memory_int| ~var_1_16_Pointer~0.base) 255) 256) 254) (not (= ~var_1_13_Pointer~0.base ~var_1_20_Pointer~0.base)) (not (= |~#var_1_19~0.base| ~var_1_16_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fe167cc0_640e574f_Treesizes_5_5() {
		final FunDecl[] funDecls = {
			new FunDecl(SmtSortUtils::getIntSort, "~var_1_30~0"),
		};
		final String formulaAsString = "(<= (mod ~var_1_30~0 256) 0)";
		final String expectedResultAsString = "(= (mod ~var_1_30~0 256) 0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fed6274f_338fd764_Treesizes_28_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_int"),
			new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base_BEFORE_CALL_42| Int)) (<= (mod (+ (* (select |#memory_int| (+ 8 |v_ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base_BEFORE_CALL_42|)) 4294967295) 4294967295) 4294967296) 4294967294)) (<= (mod (+ (* 4294967295 (select |#memory_int| (+ |ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base| 8))) 4294967295) 4294967296) 4294967294))";
		final String expectedResultAsString = "(<= (mod (+ (* 4294967295 (select |#memory_int| (+ |ULTIMATE.start_aws_byte_buf_write_harness_~#buf~3#1.base| 8))) 4294967295) 4294967296) 4294967294)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ff3d55be_6d7aeb8_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_13 Int)) (<= 8690 (select |#memory_$Pointer$.base| (+ v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_13 4))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_satisfies_pred_harness_~#cur~3#1.base_BEFORE_CALL_19| Int)) (<= 8690 (select |#memory_$Pointer$.base| (+ 4 |v_ULTIMATE.start_aws_byte_cursor_satisfies_pred_harness_~#cur~3#1.base_BEFORE_CALL_19|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ff99eb7c_907cdc2c_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_44| Int)) (<= 66 (select |#memory_$Pointer$.base| (+ 12 |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_44|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_43| Int)) (<= 66 (select |#memory_$Pointer$.base| (+ 12 |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_43|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}




	// @formatter:on
}
