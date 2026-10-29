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
public class SimplificationOpportunities20260930Bitvector {

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
				SimplificationOpportunities20260930Bitvector.class.getSimpleName());
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
	public void SimplificationOpportunity_107c32bd_e96d9493_Treesizes_64_62() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#StackHeapBarrier", "ULTIMATE.start_sll_circular_create_~head~0#1.base", "ULTIMATE.start_sll_circular_create_~last~0#1.base", "ULTIMATE.start_main_~#s~0#1.base", "#HeapAllocations"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (= (bvadd (_ bv16 32) (select |#memory_$Pointer$.base| |ULTIMATE.start_sll_circular_create_~head~0#1.base|)) |#HeapAllocations|) (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9| (_ BitVec 32))) (and (bvult (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9|) (_ bv2147483647 32)) (bvugt (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9|) |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9| |#StackHeapBarrier|))) (= (bvadd (_ bv16 32) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |#HeapAllocations|) (bvugt |ULTIMATE.start_main_~#s~0#1.base| |#StackHeapBarrier|) (= |#HeapAllocations| (bvadd (_ bv8 32) |ULTIMATE.start_sll_circular_create_~head~0#1.base|)) (bvugt (bvadd (_ bv4 32) |ULTIMATE.start_main_~#s~0#1.base|) |#StackHeapBarrier|) (bvult (bvadd (_ bv4 32) |ULTIMATE.start_main_~#s~0#1.base|) (_ bv2147483647 32)) (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_10| (_ BitVec 32))) (and (bvugt (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_10|) |#StackHeapBarrier|) (bvult (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_10|) (_ bv2147483647 32)) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_10| |#StackHeapBarrier|))) (bvult |#HeapAllocations| |#StackHeapBarrier|))";
		final String expectedResultAsString = "(let ((.cse1 (bvadd (_ bv4 32) |ULTIMATE.start_main_~#s~0#1.base|))) (and (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9|))) (and (bvult .cse0 (_ bv2147483647 32)) (bvugt .cse0 |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9| |#StackHeapBarrier|)))) (= (bvadd (_ bv16 32) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |#HeapAllocations|) (bvugt |ULTIMATE.start_main_~#s~0#1.base| |#StackHeapBarrier|) (= (select |#memory_$Pointer$.base| |ULTIMATE.start_sll_circular_create_~head~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) (= |#HeapAllocations| (bvadd (_ bv8 32) |ULTIMATE.start_sll_circular_create_~head~0#1.base|)) (bvugt .cse1 |#StackHeapBarrier|) (bvult .cse1 (_ bv2147483647 32)) (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_10| (_ BitVec 32))) (let ((.cse2 (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_10|))) (and (bvugt .cse2 |#StackHeapBarrier|) (bvult .cse2 (_ bv2147483647 32)) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_10| |#StackHeapBarrier|)))) (bvult |#HeapAllocations| |#StackHeapBarrier|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_113117b9_462abc07_Treesizes_71_71() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~state_20~0#1", "ULTIMATE.start_main_~mask_SORT_1~0#1", "ULTIMATE.start_main_~state_56~0#1"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 8) |ULTIMATE.start_main_~state_56~0#1|)) (forall ((|v_ULTIMATE.start_main_~var_79_arg_0~0#1_16| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_41_arg_1~0#1_14| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_37_arg_1~0#1_14| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_23_arg_1~0#1_14| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_26_arg_1~0#1_14| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvor ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |ULTIMATE.start_main_~state_20~0#1|) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_23_arg_1~0#1_14|)))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_26_arg_1~0#1_14|)))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_37_arg_1~0#1_14|))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_41_arg_1~0#1_14|))))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_79_arg_0~0#1_16|)))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|)))))) (or (forall ((|v_ULTIMATE.start_main_~var_79_arg_0~0#1_16| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_75_arg_1~0#1_14| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_75_arg_1~0#1_14|)))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_79_arg_0~0#1_16|)))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|))))) (= (_ bv0 8) |ULTIMATE.start_main_~state_56~0#1|)))";
		final String expectedResultAsString = "(let ((.cse0 ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|)) (.cse1 (= (_ bv0 8) |ULTIMATE.start_main_~state_56~0#1|))) (and (or (forall ((|v_ULTIMATE.start_main_~var_41_arg_1~0#1_11| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_37_arg_1~0#1_11| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_23_arg_1~0#1_11| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_26_arg_1~0#1_11| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_79_arg_0~0#1_13| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_79_arg_0~0#1_13|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvor ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_37_arg_1~0#1_11|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_26_arg_1~0#1_11|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |ULTIMATE.start_main_~state_20~0#1|) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_23_arg_1~0#1_11|))))))))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_41_arg_1~0#1_11|)))))))))))) .cse0)))) (not .cse1)) (or (forall ((|v_ULTIMATE.start_main_~var_75_arg_1~0#1_11| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_79_arg_0~0#1_13| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_75_arg_1~0#1_11|)))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_79_arg_0~0#1_13|)))) .cse0)))) .cse1)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_11f6da93_9fcc30bb_Treesizes_34_34() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#signed_char_Array_0~0.base", "~#signed_long_int_Array_0~0.base", "~#signed_short_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= |~#signed_char_Array_0~0.base| (_ bv59 32)) (= (_ bv63 32) |~#signed_long_int_Array_0~0.base|) (not (bvsgt (bvor ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (_ bv61 32)))) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (_ bv60 32))))) (select |#memory_int| (_ bv71 32)))) (= (_ bv75 32) |~#signed_short_int_Array_0~0.base|) (exists ((|v_ULTIMATE.start_step_#t~mem19#1_36| (_ BitVec 16))) (not (bvsgt ((_ zero_extend 16) |v_ULTIMATE.start_step_#t~mem19#1_36|) (select |#memory_int| (_ bv71 32))))))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (_ bv71 32)))) (and (exists ((|v_ULTIMATE.start_step_#t~mem19#1_32| (_ BitVec 16))) (not (bvsgt ((_ zero_extend 16) |v_ULTIMATE.start_step_#t~mem19#1_32|) .cse0))) (= |~#signed_char_Array_0~0.base| (_ bv59 32)) (= (_ bv63 32) |~#signed_long_int_Array_0~0.base|) (not (bvsgt (bvor ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (_ bv61 32)))) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (_ bv60 32))))) .cse0)) (= (_ bv75 32) |~#signed_short_int_Array_0~0.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1263d8f3_3e6cb6ce_Treesizes_44_32() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_5_Pointer~0.base", "~var_1_3_Pointer~0.base", "~var_1_11_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_65 (_ BitVec 32)) (v_ArrVal_69 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_65) ~var_1_1_Pointer~0.base ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_65) ~var_1_3_Pointer~0.base)))) ~var_1_5_Pointer~0.base v_ArrVal_69) ~var_1_1_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_65) ~var_1_1_Pointer~0.base ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_65) ~var_1_3_Pointer~0.base)))) ~var_1_5_Pointer~0.base v_ArrVal_69) ~var_1_3_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_69 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~var_1_1_Pointer~0.base ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| ~var_1_3_Pointer~0.base)))) ~var_1_5_Pointer~0.base v_ArrVal_69))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~var_1_1_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~var_1_3_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_133c2b2e_431ff8d6_Treesizes_4_4() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_41~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_41~0))";
		final String expectedResultAsString = "(bvsge ((_ zero_extend 24) ~var_1_41~0) (_ bv1 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_13ba5c40_edf20ff2_Treesizes_30_30() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (bvslt (bvadd (select |#memory_int| |~#WrapperStruct00~0.base|) (_ bv10 32)) (select |#memory_int| (bvadd (_ bv12 32) |~#WrapperStruct00~0.base|))) (= (bvadd (select |#memory_int| |~#WrapperStruct00~0.base|) (_ bv10 32)) (select |#memory_int| (bvadd (_ bv8 32) |~#WrapperStruct00~0.base|))) (bvsge (bvadd (select |#memory_int| |~#WrapperStruct00~0.base|) (_ bv10 32)) (_ bv4294967295 32)))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (bvadd (_ bv8 32) |~#WrapperStruct00~0.base|)))) (and (bvslt .cse0 (select |#memory_int| (bvadd (_ bv12 32) |~#WrapperStruct00~0.base|))) (= (bvadd (select |#memory_int| |~#WrapperStruct00~0.base|) (_ bv10 32)) .cse0) (bvsge .cse0 (_ bv4294967295 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1442ecb4_cd18958c_Treesizes_21_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base_BEFORE_CALL_2| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base_BEFORE_CALL_2| (_ bv8 32)) (_ bv2147483647 32)) (= |v_ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base_BEFORE_CALL_2| (bvadd (_ bv8 32) (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base_BEFORE_CALL_2| (_ bv4294967280 32))))) (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base_BEFORE_CALL_2| (_ bv4294967288 32)) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base_BEFORE_CALL_1| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base_BEFORE_CALL_1| (_ bv4294967288 32)) (_ bv2147483647 32)) (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base_BEFORE_CALL_1| (_ bv8 32)) (_ bv2147483647 32)) (= (bvadd (_ bv8 32) (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base_BEFORE_CALL_1| (_ bv4294967280 32)))) |v_ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base_BEFORE_CALL_1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_14aab975_16b28fa8_Treesizes_21_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "~var_1_5~0", "~var_1_6~0"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_13~0"),
		};
		final String formulaAsString = "(and (or (bvsge ((_ zero_extend 16) ~var_1_5~0) ~var_1_13~0) (not (bvsgt ~var_1_13~0 ((_ zero_extend 16) ~var_1_6~0)))) (or (bvsgt ~var_1_13~0 ((_ zero_extend 16) ~var_1_6~0)) (bvsge ((_ zero_extend 16) ~var_1_5~0) ((_ zero_extend 16) ~var_1_6~0))))";
		final String expectedResultAsString = "(let ((.cse0 ((_ zero_extend 16) ~var_1_5~0))) (and (bvsge .cse0 ~var_1_13~0) (bvsge .cse0 ((_ zero_extend 16) ~var_1_6~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1509f4f2_9ddbae4b_Treesizes_8_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_8~0", "~var_1_34~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_8~0) (_ bv0 32)) (= (_ bv0 8) ~var_1_34~0))";
		final String expectedResultAsString = "(and (= (_ bv0 8) ~var_1_34~0) (= ~var_1_8~0 (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_15e2e8fc_296eef87_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_back_~list#1.base_BEFORE_CALL_5| (_ BitVec 32))) (and (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_back_~list#1.base_BEFORE_CALL_5|) (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_back_~list#1.base_BEFORE_CALL_5|)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv70 32)) (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_back_~list#1.base_BEFORE_CALL_5|) |#StackHeapBarrier|))) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_back_~list#1.base_BEFORE_CALL_5|) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19| (_ BitVec 32))) (let ((.cse0 (bvadd |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19| (_ bv16 32)))) (and (bvult .cse0 (_ bv2147483647 32)) (= (bvadd |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19| (_ bv8 32)) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19|)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv70 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1644bf48_5ce9afc4_Treesizes_160_154() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_15_Pointer~0.base", "~WrapperStruct00_var_1_9_Pointer~0.base", "~WrapperStruct00_var_1_2_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ~WrapperStruct00_var_1_2_Pointer~0.base (_ bv54 32)) (= (_ bv62 32) ~WrapperStruct00_var_1_3_Pointer~0.base) (= ~WrapperStruct00_var_1_15_Pointer~0.base (_ bv97 32)) (exists ((|v_skolemized_q#valueAsBitvector_39| (_ BitVec 64))) (and (= ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_39|) (select |#memory_int| (_ bv62 32))) (= ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_39|) (select |#memory_int| (_ bv66 32))))) (= (_ bv88 32) ~WrapperStruct00_var_1_9_Pointer~0.base) (= (_ bv46 32) |~#WrapperStruct00~0.base|) (fp.geq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854776000.0)))) (exists ((|v_skolemized_q#valueAsBitvector_38| (_ BitVec 64))) (and (fp.leq (fp ((_ extract 63 63) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32)))) ((_ extract 62 52) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32)))) ((_ extract 51 0) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))) (fp.geq (fp ((_ extract 63 63) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32)))) ((_ extract 62 52) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32)))) ((_ extract 51 0) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854776000.0)))) (= (select |#memory_int| (_ bv58 32)) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|)))) (fp.leq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))))";
		final String expectedResultAsString = "(let ((.cse3 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))) (.cse4 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854776000.0))))) (and (= ~WrapperStruct00_var_1_2_Pointer~0.base (_ bv54 32)) (= (_ bv62 32) ~WrapperStruct00_var_1_3_Pointer~0.base) (exists ((|v_skolemized_q#valueAsBitvector_39| (_ BitVec 64))) (let ((.cse1 (select |#memory_int| (_ bv66 32))) (.cse0 ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_39|))) (let ((.cse2 (let ((.cse5 (concat .cse1 .cse0))) (fp ((_ extract 63 63) .cse5) ((_ extract 62 52) .cse5) ((_ extract 51 0) .cse5))))) (and (= .cse0 (select |#memory_int| (_ bv62 32))) (= ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_39|) .cse1) (fp.leq .cse2 .cse3) (fp.geq .cse2 .cse4))))) (= ~WrapperStruct00_var_1_15_Pointer~0.base (_ bv97 32)) (= (_ bv88 32) ~WrapperStruct00_var_1_9_Pointer~0.base) (= (_ bv46 32) |~#WrapperStruct00~0.base|) (exists ((|v_skolemized_q#valueAsBitvector_38| (_ BitVec 64))) (let ((.cse7 ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|))) (let ((.cse6 (let ((.cse8 (concat .cse7 (select |#memory_int| (_ bv54 32))))) (fp ((_ extract 63 63) .cse8) ((_ extract 62 52) .cse8) ((_ extract 51 0) .cse8))))) (and (fp.leq .cse6 .cse3) (fp.geq .cse6 .cse4) (= (select |#memory_int| (_ bv58 32)) .cse7)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_16be6525_936bcea9_Treesizes_47_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_pop_back_~list#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|) (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|)) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|) (_ bv2147483647 32)) (exists ((|v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19| (_ bv16 32)) (_ bv2147483647 32)) (= (bvadd |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19| (_ bv8 32)) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19|)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19| (_ bv16 32)) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv70 32)))))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv70 32)) (bvugt (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|) |#StackHeapBarrier|))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|))) (and (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|) (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|)) (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv70 32)) (bvugt .cse0 |#StackHeapBarrier|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_17f14338_3e6541a9_Treesizes_16_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo1_#in~n"),
		};
		final String formulaAsString = "(and (not (bvslt (bvadd |fibo1_#in~n| (_ bv4294967294 32)) (_ bv1 32))) (not (= |fibo1_#in~n| (_ bv3 32))) (bvslt (bvadd |fibo1_#in~n| (_ bv4294967292 32)) (_ bv1 32)))";
		final String expectedResultAsString = "(= |fibo1_#in~n| (_ bv4 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_18b2b7fe_7de08c3d_Treesizes_50_34() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~MINVAL~0#1", "~CELLCOUNT~0", "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#volArray~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(or (bvsle (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv2 32)) (bvsdiv ~CELLCOUNT~0 (_ bv2 32))) (forall ((v_ArrVal_36 (_ BitVec 32)) (v_ArrVal_37 (_ BitVec 32))) (or (bvsge (select (store (store |#memory_int| (bvadd (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv8 32)) (_ bv4294967292 32) |ULTIMATE.start_main_~#volArray~0#1.base|) v_ArrVal_36) (bvadd (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv8 32)) |ULTIMATE.start_main_~#volArray~0#1.base|) v_ArrVal_37) |ULTIMATE.start_main_~#volArray~0#1.base|) |ULTIMATE.start_main_~MINVAL~0#1|) (= (_ bv0 32) (select (store (store |#memory_int| (bvadd (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv8 32)) (_ bv4294967292 32) |ULTIMATE.start_main_~#volArray~0#1.base|) v_ArrVal_36) (bvadd (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv8 32)) |ULTIMATE.start_main_~#volArray~0#1.base|) v_ArrVal_37) |ULTIMATE.start_main_~#volArray~0#1.base|)))))";
		final String expectedResultAsString = "(or (forall ((v_ArrVal_37 (_ BitVec 32))) (let ((.cse0 (select (store |#memory_int| (bvadd (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv8 32)) |ULTIMATE.start_main_~#volArray~0#1.base|) v_ArrVal_37) |ULTIMATE.start_main_~#volArray~0#1.base|))) (or (bvsge .cse0 |ULTIMATE.start_main_~MINVAL~0#1|) (= (_ bv0 32) .cse0)))) (bvsle (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv2 32)) (bvsdiv ~CELLCOUNT~0 (_ bv2 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_19436742_3a1f4f58_Treesizes_26_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#double_Array_0~0.base", "~#signed_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_57 (_ BitVec 32)) (v_ArrVal_58 (_ BitVec 32)) (v_ArrVal_59 (_ BitVec 32))) (not (bvslt ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| (bvadd |~#signed_char_Array_0~0.base| (_ bv5 32)) v_ArrVal_57) (bvadd (_ bv16 32) |~#double_Array_0~0.base|) v_ArrVal_59) (bvadd (_ bv20 32) |~#double_Array_0~0.base|) v_ArrVal_58) (bvadd |~#signed_char_Array_0~0.base| (_ bv2 32))))) (_ bv0 32))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_58 (_ BitVec 32)) (v_ArrVal_59 (_ BitVec 32))) (not (bvslt ((_ sign_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| (bvadd (_ bv16 32) |~#double_Array_0~0.base|) v_ArrVal_59) (bvadd (_ bv20 32) |~#double_Array_0~0.base|) v_ArrVal_58) (bvadd |~#signed_char_Array_0~0.base| (_ bv2 32))))) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_196815b4_93d8bb5c_Treesizes_21_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_85| (_ BitVec 32))) (or (= (bvadd |mult_#in~n| |mult_#res|) (bvmul (_ bv5 32) |v_mult_#in~n_BEFORE_CALL_85|)) (not (= (bvmul |mult_#in~n| (_ bv5 32)) (bvmul (_ bv5 32) |v_mult_#in~n_BEFORE_CALL_85|))))) (= |mult_#in~m| (_ bv4 32)))";
		final String expectedResultAsString = "(and (= (bvmul |mult_#in~n| (_ bv4 32)) |mult_#res|) (= |mult_#in~m| (_ bv4 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_19e39837_4f6f7511_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_array_list_back_~list#1.base_BEFORE_CALL_8| (_ BitVec 32))) (and (bvult (bvadd (_ bv20 32) |v_ULTIMATE.start_aws_array_list_back_~list#1.base_BEFORE_CALL_8|) (_ bv2147483647 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_array_list_back_~list#1.base_BEFORE_CALL_8|))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv20 32) |v_ULTIMATE.start_aws_array_list_back_~list#1.base_BEFORE_CALL_8|) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8422 32))))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_array_list_back_~list#1.base_BEFORE_CALL_7| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv20 32) |v_ULTIMATE.start_aws_array_list_back_~list#1.base_BEFORE_CALL_7|))) (and (bvult .cse0 (_ bv2147483647 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_array_list_back_~list#1.base_BEFORE_CALL_7|))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8422 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1a9eb866_37d9be52_Treesizes_6_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_2| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_2|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_16| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_16|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1ab826d6_5b7f6079_Treesizes_21_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_88| (_ BitVec 32))) (or (= (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_88|) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_88|))))) (= |mult_#in~m| (_ bv1 32)))";
		final String expectedResultAsString = "(and (= |mult_#in~n| |mult_#res|) (= |mult_#in~m| (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1ac5d712_56612f1b_Treesizes_48_36() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#signed_long_int_Array_0~0.base", "~#unsigned_long_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| (bvadd (_ bv20 32) |~#signed_long_int_Array_0~0.base|)) (bvadd (bvneg (select |#memory_int| (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|))) (select |#memory_int| (bvadd (_ bv16 32) |~#signed_long_int_Array_0~0.base|)) (select |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|)))) (not (= (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) |~#unsigned_long_int_Array_0~0.base|)) (not (= (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) |~#unsigned_long_int_Array_0~0.base|)) (not (= (bvadd (_ bv20 32) |~#signed_long_int_Array_0~0.base|) |~#unsigned_long_int_Array_0~0.base|)) (not (= (bvadd (_ bv16 32) |~#signed_long_int_Array_0~0.base|) |~#unsigned_long_int_Array_0~0.base|)))";
		final String expectedResultAsString = "(forall ((v_ArrVal_140 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_140))) (= (select .cse0 (bvadd (_ bv20 32) |~#signed_long_int_Array_0~0.base|)) (bvadd (select .cse0 (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|)) (select .cse0 (bvadd (_ bv16 32) |~#signed_long_int_Array_0~0.base|)) (bvneg (select .cse0 (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1be17da9_ce0619c1_Treesizes_4_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "bounded_malloc_#res.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |bounded_malloc_#res.base|))";
		final String expectedResultAsString = "(bvugt |bounded_malloc_#res.base| (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1c19457a_fce5422d_Treesizes_19_19() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_dynamic_~from#1.base_BEFORE_CALL_7| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_aws_byte_buf_append_dynamic_~from#1.base_BEFORE_CALL_7| (_ bv8 32)) (_ bv2147483647 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_byte_buf_append_dynamic_~from#1.base_BEFORE_CALL_7| (_ bv4 32)))) (bvult (bvadd |v_ULTIMATE.start_aws_byte_buf_append_dynamic_~from#1.base_BEFORE_CALL_7| (_ bv4294967280 32)) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#from~0#1.base_BEFORE_CALL_7| (_ BitVec 32))) (and (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#from~0#1.base_BEFORE_CALL_7|))) (bvult (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#from~0#1.base_BEFORE_CALL_7|) (_ bv2147483647 32)) (bvult (bvadd |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#from~0#1.base_BEFORE_CALL_7| (_ bv4294967280 32)) (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1d1cbaa8_554062e4_Treesizes_55_53() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id1~0", "~max1~0", "~max2~0", "~p32_old~0"),
		};
		final String formulaAsString = "(and (exists ((~max3~0 (_ BitVec 8)) (~id3~0 (_ BitVec 8))) (and (= ((_ sign_extend 24) ~id3~0) ((_ sign_extend 24) ~max3~0)) (= ((_ extract 7 0) ((_ sign_extend 24) ~max3~0)) ~max2~0) (= ((_ extract 7 0) ((_ sign_extend 24) ~max3~0)) ~p32_old~0))) (exists ((~id2~0 (_ BitVec 8)) (v_~max2~0_55 (_ BitVec 8)) (v_~max1~0_39 (_ BitVec 8))) (and (= ((_ sign_extend 24) v_~max1~0_39) ((_ sign_extend 24) ~id1~0)) (= ((_ sign_extend 24) ~id2~0) ((_ sign_extend 24) v_~max2~0_55)) (bvsgt ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~max2~0))) ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) v_~max2~0_55)))) (bvsgt ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) v_~max2~0_55))) ((_ sign_extend 24) v_~max1~0_39)))) (= ((_ extract 7 0) ((_ sign_extend 24) ~max2~0)) ~max1~0) (bvsge ((_ sign_extend 24) ~id1~0) (_ bv0 32)))";
		final String expectedResultAsString = "(let ((.cse5 ((_ extract 7 0) ((_ sign_extend 24) ~max2~0))) (.cse1 ((_ sign_extend 24) ~id1~0))) (and (exists ((~id2~0 (_ BitVec 8)) (~max3~0 (_ BitVec 8)) (~id3~0 (_ BitVec 8)) (v_~max2~0_55 (_ BitVec 8)) (v_~max1~0_39 (_ BitVec 8))) (let ((.cse4 ((_ sign_extend 24) v_~max2~0_55)) (.cse2 ((_ sign_extend 24) ~max3~0))) (let ((.cse3 ((_ extract 7 0) .cse2)) (.cse6 ((_ sign_extend 24) ((_ extract 7 0) .cse4))) (.cse0 ((_ sign_extend 24) v_~max1~0_39))) (and (= .cse0 .cse1) (= ((_ sign_extend 24) ~id3~0) .cse2) (= .cse3 ~max2~0) (= ((_ sign_extend 24) ~id2~0) .cse4) (bvsgt ((_ sign_extend 24) .cse5) .cse6) (= .cse3 ~p32_old~0) (bvsgt .cse6 .cse0))))) (= .cse5 ~max1~0) (bvsge .cse1 (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1dd73fe4_8cedf471_Treesizes_91_45() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_4| (_ BitVec 32)) (|v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_8| (_ BitVec 32))) (and (= (select |#memory_int| (bvadd (_ bv5 32) |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_4|)) ((_ extract 15 8) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_8|)) (= ((_ extract 31 24) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_8|) (select |#memory_int| (bvadd (_ bv7 32) |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_4|))) (bvult |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_8| (_ bv16 32)) (= (select |#memory_int| (bvadd (_ bv6 32) |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_4|)) ((_ extract 23 16) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_8|)) (= (_ bv0 8) (select |#memory_int| (bvadd (_ bv8 32) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_8| |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_4|))) (= (select |#memory_int| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_4|)) ((_ extract 7 0) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_8|)))) (exists ((|v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_3| (_ BitVec 32)) (|v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7| (_ BitVec 32))) (and (= ((_ extract 23 16) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7|) (select |#memory_int| (bvadd (_ bv6 32) |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_3|))) (= (select |#memory_int| (bvadd (_ bv5 32) |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_3|)) ((_ extract 15 8) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7|)) (= (select |#memory_int| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_3|)) ((_ extract 7 0) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7|)) (= ((_ extract 31 24) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7|) (select |#memory_int| (bvadd (_ bv7 32) |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_3|))) (= (select |#memory_int| (bvadd (_ bv8 32) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7| |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_3|)) (_ bv0 8)) (bvult |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7| (_ bv16 32)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_3| (_ BitVec 32)) (|v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7| (_ BitVec 32))) (and (= ((_ extract 23 16) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7|) (select |#memory_int| (bvadd (_ bv6 32) |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_3|))) (= (select |#memory_int| (bvadd (_ bv5 32) |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_3|)) ((_ extract 15 8) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7|)) (= (select |#memory_int| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_3|)) ((_ extract 7 0) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7|)) (= ((_ extract 31 24) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7|) (select |#memory_int| (bvadd (_ bv7 32) |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_3|))) (= (select |#memory_int| (bvadd (_ bv8 32) |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7| |v_ULTIMATE.start_aws_string_compare_harness_~str_b~1#1.base_BEFORE_CALL_3|)) (_ bv0 8)) (bvult |v_ensure_string_is_allocated_bounded_length_ensure_string_is_allocated_~len#1_7| (_ bv16 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1e4acee4_b43cbc2d_Treesizes_29_27() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start___ieee754_hypotf_~hb~0#1"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_#StackAllocations_43| (_ BitVec 32)) (currentRoundingMode RoundingMode)) (and (= |ULTIMATE.start___ieee754_hypotf_~hb~0#1| (bvand (_ bv2147483647 32) (select |#memory_int| |v_#StackAllocations_43|))) (= (fp ((_ extract 31 31) (select |#memory_int| |v_#StackAllocations_43|)) ((_ extract 30 23) (select |#memory_int| |v_#StackAllocations_43|)) ((_ extract 22 0) (select |#memory_int| |v_#StackAllocations_43|))) (fp.div currentRoundingMode ((_ to_fp 8 24) currentRoundingMode 1.0) (_ +zero 8 24)))))";
		final String expectedResultAsString = "(exists ((|v_#StackAllocations_43| (_ BitVec 32)) (currentRoundingMode RoundingMode)) (let ((.cse0 (select |#memory_int| |v_#StackAllocations_43|))) (and (= |ULTIMATE.start___ieee754_hypotf_~hb~0#1| .cse0) (= (fp ((_ extract 31 31) .cse0) ((_ extract 30 23) .cse0) ((_ extract 22 0) .cse0)) (fp.div currentRoundingMode ((_ to_fp 8 24) currentRoundingMode 1.0) (_ +zero 8 24))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1eabe79b_39d1b9c2_Treesizes_10_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= (_ bv0 8) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv30 32) |~#WrapperStruct00~0.base|))))))";
		final String expectedResultAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv30 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1effa205_9081716b_Treesizes_41_36() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~p~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~p~0#1.base_51| (_ BitVec 32))) (and (= |ULTIMATE.start_main_~p~0#1.base| (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~p~0#1.base_51|))) (= (bvadd (_ bv8 32) |v_ULTIMATE.start_main_~p~0#1.base_51|) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~p~0#1.base_51|))) (not (= (bvadd (_ bv9 32) |v_ULTIMATE.start_main_~p~0#1.base_51|) (_ bv0 32))) (bvugt (bvadd (_ bv8 32) |v_ULTIMATE.start_main_~p~0#1.base_51|) (_ bv32 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_main_~p~0#1.base_51|))))) (not (= (_ bv0 32) |ULTIMATE.start_main_~p~0#1.base|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_main_~p~0#1.base_51| (_ BitVec 32))) (let ((.cse0 (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~p~0#1.base_51|))) (.cse1 (bvadd (_ bv8 32) |v_ULTIMATE.start_main_~p~0#1.base_51|))) (and (= |ULTIMATE.start_main_~p~0#1.base| .cse0) (= .cse1 .cse0) (not (= (bvadd (_ bv9 32) |v_ULTIMATE.start_main_~p~0#1.base_51|) (_ bv0 32))) (bvugt .cse1 (_ bv32 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_main_~p~0#1.base_51|))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_1fb819c8_1308ab82_Treesizes_44_32() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_16_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~WrapperStruct00_var_1_5_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_93 (_ BitVec 32)) (v_ArrVal_68 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_93) ~WrapperStruct00_var_1_1_Pointer~0.base ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_93) ~WrapperStruct00_var_1_3_Pointer~0.base)))) ~WrapperStruct00_var_1_5_Pointer~0.base v_ArrVal_68) ~WrapperStruct00_var_1_3_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_93) ~WrapperStruct00_var_1_1_Pointer~0.base ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_93) ~WrapperStruct00_var_1_3_Pointer~0.base)))) ~WrapperStruct00_var_1_5_Pointer~0.base v_ArrVal_68) ~WrapperStruct00_var_1_1_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_68 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| ~WrapperStruct00_var_1_3_Pointer~0.base)))) ~WrapperStruct00_var_1_5_Pointer~0.base v_ArrVal_68))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_3_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_20050565_ea023dbf_Treesizes_103_103() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~state_323~0#1", "ULTIMATE.start_main_~var_344~0#1", "ULTIMATE.start_main_~state_319~0#1", "ULTIMATE.start_main_~state_343~0#1", "ULTIMATE.start_main_~var_333~0#1", "ULTIMATE.start_main_~var_302~0#1", "ULTIMATE.start_main_~var_326~0#1", "ULTIMATE.start_main_~var_421~0#1", "ULTIMATE.start_main_~var_82~0#1", "ULTIMATE.start_main_~var_1391~0#1", "ULTIMATE.start_main_~var_334~0#1", "ULTIMATE.start_main_~mask_SORT_16~0#1", "ULTIMATE.start_main_~mask_SORT_1~0#1", "ULTIMATE.start_main_~input_11~0#1", "ULTIMATE.start_main_~mask_SORT_96~0#1"),
		};
		final String formulaAsString = "(and (or (and (exists ((|v_ULTIMATE.start_main_~var_334_arg_1~0#1_21| (_ BitVec 8))) (= ((_ extract 7 0) (bvand (_ bv63 32) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_334_arg_1~0#1_21|))))) |ULTIMATE.start_main_~var_334~0#1|)) (not (= (_ bv0 8) |ULTIMATE.start_main_~input_11~0#1|))) (and (= (_ bv0 8) |ULTIMATE.start_main_~input_11~0#1|) (= ((_ extract 7 0) (bvand (_ bv63 32) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvadd (bvneg ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) |ULTIMATE.start_main_~var_302~0#1|))))) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv255 32) ((_ zero_extend 24) |ULTIMATE.start_main_~var_326~0#1|)))))))))))))))) |ULTIMATE.start_main_~var_334~0#1|))) (= (_ bv17 8) |ULTIMATE.start_main_~state_343~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~var_333~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~state_323~0#1|) (= (_ bv17 8) |ULTIMATE.start_main_~var_1391~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~state_319~0#1|) (= |ULTIMATE.start_main_~var_421~0#1| (_ bv16 8)) (= (_ bv31 8) |ULTIMATE.start_main_~mask_SORT_16~0#1|) (= (_ bv63 8) |ULTIMATE.start_main_~mask_SORT_96~0#1|) (not (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor (_ bv254 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor (_ bv254 32) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) |ULTIMATE.start_main_~var_302~0#1|))))))))))))))) (= (_ bv1 8) |ULTIMATE.start_main_~mask_SORT_1~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~var_344~0#1|) (= (_ bv1 8) |ULTIMATE.start_main_~var_82~0#1|))";
		final String expectedResultAsString = "(let ((.cse1 ((_ zero_extend 24) |ULTIMATE.start_main_~var_302~0#1|))) (and (= (_ bv17 8) |ULTIMATE.start_main_~state_343~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~var_333~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~state_323~0#1|) (= (_ bv17 8) |ULTIMATE.start_main_~var_1391~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~state_319~0#1|) (= |ULTIMATE.start_main_~var_421~0#1| (_ bv16 8)) (= (_ bv31 8) |ULTIMATE.start_main_~mask_SORT_16~0#1|) (= (_ bv63 8) |ULTIMATE.start_main_~mask_SORT_96~0#1|) (let ((.cse0 (= (_ bv0 8) |ULTIMATE.start_main_~input_11~0#1|))) (or (and (exists ((|v_ULTIMATE.start_main_~var_334_arg_1~0#1_16| (_ BitVec 8))) (= ((_ extract 7 0) (bvand (_ bv63 32) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_334_arg_1~0#1_16|))))) |ULTIMATE.start_main_~var_334~0#1|)) (not .cse0)) (and .cse0 (= ((_ extract 7 0) (bvand (_ bv63 32) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvadd (bvneg ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv1 32) .cse1)))) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv255 32) ((_ zero_extend 24) |ULTIMATE.start_main_~var_326~0#1|)))))))))))))))) |ULTIMATE.start_main_~var_334~0#1|)))) (not (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor (_ bv254 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor (_ bv254 32) ((_ zero_extend 24) ((_ extract 7 0) (bvnot .cse1)))))))))))))) (= (_ bv1 8) |ULTIMATE.start_main_~mask_SORT_1~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~var_344~0#1|) (= (_ bv1 8) |ULTIMATE.start_main_~var_82~0#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_207f4868_fe380819_Treesizes_16_5() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~i~0#1_15| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul (_ bv4 32) |v_ULTIMATE.start_main_~i~0#1_15|))))) (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_main_~x~0#1.base|)))";
		final String expectedResultAsString = "(= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_main_~x~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_20e876e4_3753bdd7_Treesizes_51_42() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#Ultimate.C_memset_#ptr.base", "#Ultimate.C_memset_#amount", "#Ultimate.C_memset_#value"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (bvult (_ bv4 32) |#Ultimate.C_memset_#amount|) (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd (_ bv1 32) |#Ultimate.C_memset_#ptr.base|))) (= (select |#memory_int| |#Ultimate.C_memset_#ptr.base|) ((_ extract 7 0) |#Ultimate.C_memset_#value|)) (= (select |#memory_int| (bvadd (_ bv3 32) |#Ultimate.C_memset_#ptr.base|)) ((_ extract 7 0) |#Ultimate.C_memset_#value|)) (exists ((|v_#Ultimate.C_memset_#t~loopctr676_39| (_ BitVec 32))) (= (select |#memory_int| (bvadd |#Ultimate.C_memset_#ptr.base| |v_#Ultimate.C_memset_#t~loopctr676_39|)) ((_ extract 7 0) |#Ultimate.C_memset_#value|))) (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd (_ bv2 32) |#Ultimate.C_memset_#ptr.base|))) (= (select |#memory_int| (bvadd (_ bv4 32) |#Ultimate.C_memset_#ptr.base|)) ((_ extract 7 0) |#Ultimate.C_memset_#value|)))";
		final String expectedResultAsString = "(let ((.cse0 ((_ extract 7 0) |#Ultimate.C_memset_#value|))) (and (bvult (_ bv4 32) |#Ultimate.C_memset_#amount|) (= .cse0 (select |#memory_int| (bvadd (_ bv1 32) |#Ultimate.C_memset_#ptr.base|))) (= (select |#memory_int| |#Ultimate.C_memset_#ptr.base|) .cse0) (= (select |#memory_int| (bvadd (_ bv3 32) |#Ultimate.C_memset_#ptr.base|)) .cse0) (= .cse0 (select |#memory_int| (bvadd (_ bv2 32) |#Ultimate.C_memset_#ptr.base|))) (= (select |#memory_int| (bvadd (_ bv4 32) |#Ultimate.C_memset_#ptr.base|)) .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_21befa7f_33a84731_Treesizes_36_36() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_16_Pointer~0.base", "~WrapperStruct00_var_1_17_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_11_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_124 (_ BitVec 32)) (v_ArrVal_123 (_ BitVec 32)) (v_ArrVal_122 (_ BitVec 32)) (v_ArrVal_153 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_153) ~WrapperStruct00_var_1_11_Pointer~0.base v_ArrVal_122) ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_123) ~WrapperStruct00_var_1_17_Pointer~0.base v_ArrVal_124) ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_153) ~WrapperStruct00_var_1_11_Pointer~0.base v_ArrVal_122) ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_123) ~WrapperStruct00_var_1_17_Pointer~0.base v_ArrVal_124) ~WrapperStruct00_var_1_4_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_124 (_ BitVec 32)) (v_ArrVal_123 (_ BitVec 32)) (v_ArrVal_122 (_ BitVec 32)) (v_ArrVal_121 (_ BitVec 32))) (let ((.cse0 (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_121) ~WrapperStruct00_var_1_11_Pointer~0.base v_ArrVal_122) ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_123) ~WrapperStruct00_var_1_17_Pointer~0.base v_ArrVal_124))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_4_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_226f893a_b07c2b2a_Treesizes_15_15() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_12_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_150 (_ BitVec 32)) (v_ArrVal_149 (_ BitVec 32))) (not (bvult (_ bv4294967168 32) (select (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_150) (bvadd ~WrapperStruct00_var_1_1_Pointer~0.base (_ bv4 32)) v_ArrVal_149) ~WrapperStruct00_var_1_12_Pointer~0.base))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_113 (_ BitVec 32)) (v_ArrVal_112 (_ BitVec 32))) (not (bvult (_ bv4294967168 32) (select (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_113) (bvadd ~WrapperStruct00_var_1_1_Pointer~0.base (_ bv4 32)) v_ArrVal_112) ~WrapperStruct00_var_1_12_Pointer~0.base))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_235f8315_b062614b_Treesizes_79_39() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base|)) (select |#memory_int| (bvadd (_ bv2 32) |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base|))) (select |#memory_int| (bvadd (_ bv1 32) |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base|))) (select |#memory_int| |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base|))) (exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7| (_ BitVec 32))) (and (bvult (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7|) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8836 32)) (bvugt (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7|) |#StackHeapBarrier|))) (= (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7|))) (select |#memory_int| |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7|)) (_ bv0 32)))) (bvult (bvadd (_ bv8 32) |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base|) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8836 32)) (bvugt (bvadd (_ bv8 32) |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base|) |#StackHeapBarrier|))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv8 32) |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base|))) (and (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base|)) (select |#memory_int| (bvadd (_ bv2 32) |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base|))) (select |#memory_int| (bvadd (_ bv1 32) |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base|))) (select |#memory_int| |ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base|))) (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8836 32)) (bvugt .cse0 |#StackHeapBarrier|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_23ffe182_c192994f_Treesizes_32_28() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~g2v_new~0", "~g1v_new~0", "~nomsg~0"),
		};
		final String formulaAsString = "(and (or (not (= ((_ sign_extend 24) (_ bv0 8)) ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~g1v_new~0))))) (not (= ((_ sign_extend 24) ~g2v_new~0) ((_ sign_extend 24) ~nomsg~0)))) (or (= ((_ sign_extend 24) ~g2v_new~0) ((_ sign_extend 24) ~nomsg~0)) (not (= ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~g2v_new~0))) ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~g1v_new~0)))))))";
		final String expectedResultAsString = "(let ((.cse0 ((_ sign_extend 24) ~g2v_new~0))) (let ((.cse1 ((_ sign_extend 24) ~g1v_new~0)) (.cse2 (= .cse0 ((_ sign_extend 24) ~nomsg~0)))) (and (or (not (= ((_ sign_extend 24) ((_ extract 7 0) .cse0)) .cse1)) .cse2) (or (not (= .cse1 ((_ sign_extend 24) (_ bv0 8)))) (not .cse2)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_24821101_23c78528_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var5_Pointer~0.base", "~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var2_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_151 (_ BitVec 32))) (bvugt (bvadd (bvneg (select (store |#memory_int| ~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var5_Pointer~0.base v_ArrVal_151) ~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var2_Pointer~0.base)) (_ bv3934615513 32)) (_ bv1000000000 32)))";
		final String expectedResultAsString = "(forall ((v_ArrVal_129 (_ BitVec 32))) (bvugt (bvadd (bvneg (select (store |#memory_int| ~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var5_Pointer~0.base v_ArrVal_129) ~unsigned_long_int_Array_0_arrayunsigned_long_int_Array_0Var2_Pointer~0.base)) (_ bv3934615513 32)) (_ bv1000000000 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_249007a7_73cb9aaa_Treesizes_21_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#Ultimate.C_memset_#ptr.base", "#Ultimate.C_memset_#amount", "#Ultimate.C_memset_#value"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_#Ultimate.C_memset_#t~loopctr676_124| (_ BitVec 32))) (= (select |#memory_int| (bvadd |#Ultimate.C_memset_#ptr.base| |v_#Ultimate.C_memset_#t~loopctr676_124|)) ((_ extract 7 0) |#Ultimate.C_memset_#value|))) (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd (_ bv2 32) |#Ultimate.C_memset_#ptr.base|))) (bvult (_ bv2 32) |#Ultimate.C_memset_#amount|))";
		final String expectedResultAsString = "(and (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd (_ bv2 32) |#Ultimate.C_memset_#ptr.base|))) (bvult (_ bv2 32) |#Ultimate.C_memset_#amount|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_24ce643d_bce4702_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_29| (_ BitVec 32))) (not (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_29|) (_ bv0 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_27| (_ BitVec 32))) (not (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_27|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_25da4346_c8722b3f_Treesizes_19_19() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_7| (_ BitVec 32))) (and (= (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_7|)) (_ bv0 32)) (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_7|) (_ bv8692 32)) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_7|) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_5| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_5|))) (and (= (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_5|)) (_ bv0 32)) (bvult .cse0 (_ bv2147483647 32)) (bvugt .cse0 (_ bv8692 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_26322fe_12ebdacb_Treesizes_23_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_0~0#1", "ULTIMATE.start_step_#t~mem12#1"),
		};
		final String formulaAsString = "(and (exists ((v_arrayElimCell_164 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_164) |ULTIMATE.start_step_#t~mem12#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_164)) (_ bv31 32)))) (exists ((v_arrayElimCell_165 (_ BitVec 32))) (and (bvsge ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_165)) (_ bv127 32)) (= |ULTIMATE.start_step_~stepLocal_0~0#1| ((_ extract 7 0) v_arrayElimCell_165)))))";
		final String expectedResultAsString = "(and (exists ((v_arrayElimCell_147 (_ BitVec 32))) (let ((.cse0 ((_ extract 7 0) v_arrayElimCell_147))) (and (bvsge ((_ zero_extend 24) .cse0) (_ bv127 32)) (= .cse0 |ULTIMATE.start_step_~stepLocal_0~0#1|)))) (exists ((v_arrayElimCell_148 (_ BitVec 32))) (let ((.cse1 ((_ extract 7 0) v_arrayElimCell_148))) (and (bvsle ((_ zero_extend 24) .cse1) (_ bv31 32)) (= .cse1 |ULTIMATE.start_step_#t~mem12#1|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2681926c_dd9aa2ca_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_5 (_ BitVec 32))) (and (= (select |#memory_$Pointer$.base| v_aws_linked_list_front_~list.base_BEFORE_CALL_5) (bvadd (_ bv8 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_5)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_5) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv67 32)))) (bvult (bvadd (_ bv16 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_5) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14| (_ BitVec 32))) (let ((.cse0 (bvadd |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14| (_ bv16 32)))) (and (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv67 32)) (bvugt .cse0 |#StackHeapBarrier|))) (= (bvadd |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14| (_ bv8 32)) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_276290e4_207e4de4_Treesizes_43_42() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~signed_char_Array_0_arraysigned_char_Array_0Var3_Pointer~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (_ bv65 32)))) (select |#memory_int| (_ bv67 32))) (= (_ bv67 32) ~signed_char_Array_0_arraysigned_char_Array_0Var3_Pointer~0.base) (exists ((v_arrayElimCell_14 (_ BitVec 32))) (and (bvsle ((_ zero_extend 16) ((_ extract 15 0) v_arrayElimCell_14)) ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (_ bv65 32))))))) (= (select |#memory_int| (_ bv68 32)) ((_ zero_extend 16) ((_ extract 15 0) v_arrayElimCell_14))))) (bvsle ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (_ bv65 32)))) (_ bv31 32)) (= (_ bv65 32) ~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (_ bv68 32))) (.cse1 ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (_ bv65 32)))))) (and (exists ((v_arrayElimCell_14 (_ BitVec 32))) (= .cse0 ((_ zero_extend 16) ((_ extract 15 0) v_arrayElimCell_14)))) (= .cse1 (select |#memory_int| (_ bv67 32))) (= (_ bv67 32) ~signed_char_Array_0_arraysigned_char_Array_0Var3_Pointer~0.base) (bvsle .cse0 ((_ sign_extend 24) ((_ extract 7 0) .cse1))) (bvsle .cse1 (_ bv31 32)) (= (_ bv65 32) ~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2858273c_f56b4ad1_Treesizes_10_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "addition_#in~n"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_32| (_ BitVec 32))) (or (bvslt |v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_32| (_ bv100 32)) (not (= ((_ sign_extend 32) |v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_32|) |addition_#in~n|))))";
		final String expectedResultAsString = "(forall ((|v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_31| (_ BitVec 32))) (or (bvslt |v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_31| (_ bv100 32)) (not (= ((_ sign_extend 32) |v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_31|) |addition_#in~n|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_28e1c5a7_1bec25df_Treesizes_135_110() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#signed_long_int_Array_0~0.base", "~#signed_short_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_83 (_ BitVec 32)) (v_ArrVal_81 (_ BitVec 32))) (or (not (= (bvadd ((_ sign_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|)))) (bvshl ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_short_int_Array_0~0.base|) v_ArrVal_81) (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) ((_ sign_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|))))) (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|)))) ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_short_int_Array_0~0.base|) v_ArrVal_81) (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) ((_ sign_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|))))) (bvadd (_ bv6 32) |~#signed_short_int_Array_0~0.base|)))))) ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_short_int_Array_0~0.base|) v_ArrVal_81) (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) ((_ sign_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|))))) |~#signed_short_int_Array_0~0.base|))))) (bvslt ((_ sign_extend 16) ((_ extract 15 0) (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_short_int_Array_0~0.base|) v_ArrVal_81) (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) ((_ sign_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|))))) (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_83) (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|)))) ((_ sign_extend 16) ((_ extract 15 0) (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_short_int_Array_0~0.base|) v_ArrVal_81) (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) ((_ sign_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|))))) (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_83) |~#signed_short_int_Array_0~0.base|))))))";
		final String expectedResultAsString = "(let ((.cse1 (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|))) (let ((.cse3 ((_ sign_extend 16) ((_ extract 15 0) (select |#memory_int| .cse1))))) (let ((.cse2 (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) .cse3))) (or (forall ((v_ArrVal_83 (_ BitVec 32))) (let ((.cse0 (store .cse2 (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_83))) (bvslt ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 .cse1))) ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 |~#signed_short_int_Array_0~0.base|)))))) (not (= (bvadd (bvshl ((_ sign_extend 16) ((_ extract 15 0) (select .cse2 .cse1))) ((_ sign_extend 16) ((_ extract 15 0) (select .cse2 (bvadd (_ bv6 32) |~#signed_short_int_Array_0~0.base|))))) .cse3) ((_ sign_extend 16) ((_ extract 15 0) (select .cse2 |~#signed_short_int_Array_0~0.base|)))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2951cdf9_9a00ed15_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_17_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_156 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_17_Pointer~0.base v_ArrVal_156) ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_17_Pointer~0.base v_ArrVal_156) ~WrapperStruct00_var_1_4_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_124 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~WrapperStruct00_var_1_17_Pointer~0.base v_ArrVal_124))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_4_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_29ea2cef_21c75e34_Treesizes_18_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "func_to_recursive_line_12_to_13_0_~d.base", "func_to_recursive_line_12_to_13_0_~e.base", "func_to_recursive_line_12_to_13_0_~c.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= func_to_recursive_line_12_to_13_0_~e.base (bvadd (_ bv4 32) func_to_recursive_line_12_to_13_0_~d.base)) (= (select |#memory_int| (bvadd func_to_recursive_line_12_to_13_0_~d.base (_ bv4294967292 32))) (_ bv1 32)) (= (bvadd (_ bv4 32) func_to_recursive_line_12_to_13_0_~c.base) func_to_recursive_line_12_to_13_0_~d.base))";
		final String expectedResultAsString = "(and (= (_ bv1 32) (select |#memory_int| func_to_recursive_line_12_to_13_0_~c.base)) (= func_to_recursive_line_12_to_13_0_~e.base (bvadd (_ bv8 32) func_to_recursive_line_12_to_13_0_~c.base)) (= (bvadd (_ bv4 32) func_to_recursive_line_12_to_13_0_~c.base) func_to_recursive_line_12_to_13_0_~d.base))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2a9d1f33_d12eac03_Treesizes_6_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2b942d6a_1eb39130_Treesizes_11_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_3_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_184 (_ BitVec 32))) (bvslt ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_184) ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv1 32)))";
		final String expectedResultAsString = "(forall ((v_ArrVal_155 (_ BitVec 32))) (bvslt ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_155) ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2c94217c_ad0a0464_Treesizes_4_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_88~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_88~0) (_ bv0 32))";
		final String expectedResultAsString = "(= (_ bv0 8) ~var_1_88~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2cf9a726_494165e0_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_array_list_get_at_~list#1.base_BEFORE_CALL_8| (_ BitVec 32))) (and (= (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_array_list_get_at_~list#1.base_BEFORE_CALL_8| (_ bv16 32))) (_ bv0 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd |v_ULTIMATE.start_aws_array_list_get_at_~list#1.base_BEFORE_CALL_8| (_ bv20 32)) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8424 32)))) (bvult (bvadd |v_ULTIMATE.start_aws_array_list_get_at_~list#1.base_BEFORE_CALL_8| (_ bv20 32)) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_array_list_get_at_~list#1.base_BEFORE_CALL_7| (_ BitVec 32))) (let ((.cse0 (bvadd |v_ULTIMATE.start_aws_array_list_get_at_~list#1.base_BEFORE_CALL_7| (_ bv20 32)))) (and (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8424 32)) (bvugt .cse0 |#StackHeapBarrier|))) (= (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_array_list_get_at_~list#1.base_BEFORE_CALL_7| (_ bv16 32))) (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2dad18a_fdea9845_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~g2v_new~0", "~g1v_new~0", "~nomsg~0"),
		};
		final String formulaAsString = "(and (= (_ bv0 8) ~g1v_new~0) (= (_ bv0 8) (bvadd (_ bv1 8) ~nomsg~0)) (= ~g2v_new~0 ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8)))))";
		final String expectedResultAsString = "(and (= (bvadd ~g2v_new~0 (_ bv1 8)) (_ bv0 8)) (= (_ bv0 8) ~g1v_new~0) (= (_ bv0 8) (bvadd (_ bv1 8) ~nomsg~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2e5ff8b9_1cf58b5d_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_init_harness_~#list~0#1.base_BEFORE_CALL_13| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_init_harness_~#list~0#1.base_BEFORE_CALL_13|))))";
		final String expectedResultAsString = "(exists ((|v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_9| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_9|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2eb23e82_97570cad_Treesizes_136_92() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4_Pointer~0.base", "~var_1_5_Pointer~0.base", "~var_1_11_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_220 (_ BitVec 32))) (or (forall ((v_ArrVal_198 (_ BitVec 32))) (or (= (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_220) ~var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~var_1_5_Pointer~0.base v_ArrVal_198) ~var_1_1_Pointer~0.base)))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_220) ~var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~var_1_5_Pointer~0.base v_ArrVal_198) ~var_1_4_Pointer~0.base)))))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_220) ~var_1_4_Pointer~0.base)))))) (forall ((v_ArrVal_220 (_ BitVec 32))) (or (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_220) ~var_1_4_Pointer~0.base))) (forall ((v_ArrVal_198 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_220) ~var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~var_1_5_Pointer~0.base v_ArrVal_198) ~var_1_1_Pointer~0.base))) (_ bv0 32))))) (forall ((v_ArrVal_220 (_ BitVec 32))) (or (forall ((v_ArrVal_198 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_220) ~var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~var_1_5_Pointer~0.base v_ArrVal_198) ~var_1_4_Pointer~0.base))))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_220) ~var_1_4_Pointer~0.base))))) (forall ((v_ArrVal_220 (_ BitVec 32))) (or (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_220) ~var_1_4_Pointer~0.base)))) (forall ((v_ArrVal_198 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store (store (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_220) ~var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~var_1_5_Pointer~0.base v_ArrVal_198) ~var_1_4_Pointer~0.base)))))))";
		final String expectedResultAsString = "(let ((.cse0 (= ((_ extract 7 0) (select |#memory_int| ~var_1_4_Pointer~0.base)) (_ bv0 8)))) (and (or (not .cse0) (let ((.cse2 (store |#memory_int| ~var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))))) (and (forall ((v_ArrVal_198 (_ BitVec 32))) (let ((.cse1 (store .cse2 ~var_1_5_Pointer~0.base v_ArrVal_198))) (or (= (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (select .cse1 ~var_1_1_Pointer~0.base)))) (not (= (_ bv0 8) ((_ extract 7 0) (select .cse1 ~var_1_4_Pointer~0.base))))))) (forall ((v_ArrVal_198 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store .cse2 ~var_1_5_Pointer~0.base v_ArrVal_198) ~var_1_4_Pointer~0.base))))))) (or (let ((.cse3 (store |#memory_int| ~var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))))) (and (forall ((v_ArrVal_198 (_ BitVec 32))) (not (= ((_ extract 7 0) (select (store .cse3 ~var_1_5_Pointer~0.base v_ArrVal_198) ~var_1_4_Pointer~0.base)) (_ bv0 8)))) (forall ((v_ArrVal_198 (_ BitVec 32))) (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store .cse3 ~var_1_5_Pointer~0.base v_ArrVal_198) ~var_1_1_Pointer~0.base))))))) .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2f28317c_fb31fe5e_Treesizes_49_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_byte_buf_secure_zero_~buf#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |aws_byte_buf_secure_zero_~buf#1.base|)))) (exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_10| (_ BitVec 32))) (and (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_10|) (_ bv2147483647 32)) (not (= (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_10|)) (_ bv0 32))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8687 32)) (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_~buf#1.base_BEFORE_CALL_10|) |#StackHeapBarrier|))))) (bvult (bvadd (_ bv16 32) |aws_byte_buf_secure_zero_~buf#1.base|) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |aws_byte_buf_secure_zero_~buf#1.base|) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8687 32)))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv16 32) |aws_byte_buf_secure_zero_~buf#1.base|))) (and (not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |aws_byte_buf_secure_zero_~buf#1.base|)))) (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8687 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_2fb48d26_7a2079d1_Treesizes_71_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 32) |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|)) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14| (_ bv16 32)) (_ bv2147483647 32)) (= (bvadd |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14| (_ bv8 32)) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14|)) (bvugt |#StackHeapBarrier| (_ bv67 32)) (bvugt (bvadd |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14| (_ bv16 32)) |#StackHeapBarrier|))) (exists ((|v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_15| (_ BitVec 32)) (|v_#StackHeapBarrier_3| (_ BitVec 32))) (and (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_15|) (bvadd |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_15| (_ bv8 32))) (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_15| (_ bv16 32)) (_ bv2147483647 32)) (bvugt (bvadd |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_15| (_ bv16 32)) |v_#StackHeapBarrier_3|) (bvugt |v_#StackHeapBarrier_3| (_ bv67 32)))) (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|) (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|)) (exists ((|v_#StackHeapBarrier_4| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|) |v_#StackHeapBarrier_4|) (bvugt |v_#StackHeapBarrier_4| (_ bv67 32)))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|))) (and (bvult .cse0 (_ bv2147483647 32)) (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|) (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base|)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv67 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_305d5464_dd5e8042_Treesizes_11_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_2~0", "~x_1~0", "~a~0"),
		};
		final String formulaAsString = "(or (bvult (_ bv0 32) ~a~0) (= (bvadd ~x_1~0 (bvmul ~a~0 (_ bv2 32))) ~x_2~0))";
		final String expectedResultAsString = "(or (bvult (_ bv0 32) ~a~0) (= (bvadd ~a~0 ~x_1~0) ~x_2~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_30fb1d6f_fbb7b7c2_Treesizes_11_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem19#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_33 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_33) |ULTIMATE.start_step_#t~mem19#1|) (bvsge ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_33)) (_ bv0 32))))";
		final String expectedResultAsString = "(exists ((v_arrayElimCell_12 (_ BitVec 32))) (let ((.cse0 ((_ extract 7 0) v_arrayElimCell_12))) (and (bvsge ((_ sign_extend 24) .cse0) (_ bv0 32)) (= .cse0 |ULTIMATE.start_step_#t~mem19#1|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_314f6ced_45bbe024_Treesizes_37_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base|)) (_ bv0 32)) (bvugt (bvadd (_ bv16 32) |ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base|) (_ bv8679 32)) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base|) (_ bv2147483647 32)) (exists ((|v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_14| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_14|) (_ bv8679 32)) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_14|)) (_ bv0 32)) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_14|) (_ bv2147483647 32)))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv16 32) |ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base|))) (and (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base|)) (_ bv0 32)) (bvugt .cse0 (_ bv8679 32)) (bvult .cse0 (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_31daa12c_e1739ded_Treesizes_17_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_17| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_17| (_ bv16 32)) (_ bv2147483647 32)) (bvult |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_17| (_ bv2147483647 32)) (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_17|) (bvadd |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_17| (_ bv8 32)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ BitVec 32))) (and (bvult |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ bv2147483647 32)) (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15|) (bvadd |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ bv8 32))) (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ bv16 32)) (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_324d3d0e_c7c5fe33_Treesizes_37_33() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem24#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_step_~stepLocal_1~0#1"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_updateVariables_#t~nondet60#1_29| (_ BitVec 8))) (and (= ((_ extract 7 0) ((_ sign_extend 24) |v_ULTIMATE.start_updateVariables_#t~nondet60#1_29|)) |ULTIMATE.start_step_#t~mem24#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) ((_ sign_extend 24) |v_ULTIMATE.start_updateVariables_#t~nondet60#1_29|))) (_ bv63 32)))) (exists ((|v_ULTIMATE.start_updateVariables_#t~nondet57#1_28| (_ BitVec 8))) (and (= |ULTIMATE.start_step_~stepLocal_1~0#1| ((_ extract 15 0) ((_ sign_extend 16) ((_ zero_extend 8) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (bvadd (_ bv128 32) (bvneg ((_ zero_extend 24) ((_ extract 7 0) ((_ sign_extend 24) |v_ULTIMATE.start_updateVariables_#t~nondet57#1_28|)))))))))))) (bvsle ((_ zero_extend 24) ((_ extract 7 0) ((_ sign_extend 24) |v_ULTIMATE.start_updateVariables_#t~nondet57#1_28|))) (_ bv64 32)))))";
		final String expectedResultAsString = "(and (exists ((v_arrayElimCell_165 (_ BitVec 32))) (let ((.cse0 ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_165)))) (and (bvsle .cse0 (_ bv64 32)) (= |ULTIMATE.start_step_~stepLocal_1~0#1| ((_ extract 15 0) ((_ sign_extend 16) ((_ zero_extend 8) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (bvadd (_ bv128 32) (bvneg .cse0)))))))))))) (exists ((v_arrayElimCell_163 (_ BitVec 32))) (let ((.cse1 ((_ extract 7 0) v_arrayElimCell_163))) (and (= .cse1 |ULTIMATE.start_step_#t~mem24#1|) (bvsle ((_ zero_extend 24) .cse1) (_ bv63 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_32fc07b3_4cbb2a62_Treesizes_13_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~y~0#1_21| (_ BitVec 32))) (and (not (= |ULTIMATE.start_main_~x~0#1| |v_ULTIMATE.start_main_~y~0#1_21|)) (not (bvugt |ULTIMATE.start_main_~x~0#1| |v_ULTIMATE.start_main_~y~0#1_21|)) (bvult |v_ULTIMATE.start_main_~y~0#1_21| (_ bv2 32))))";
		final String expectedResultAsString = "(= |ULTIMATE.start_main_~x~0#1| (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_33336f31_39472272_Treesizes_6_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_6| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_6|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_15| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_15|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3358a7a_4128fe9f_Treesizes_82_76() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (_ bv45 32) |~#WrapperStruct00~0.base|) (exists ((|v_skolemized_q#valueAsBitvector_73| (_ BitVec 64))) (and (= (select |#memory_int| (_ bv70 32)) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_73|)) (= ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_73|) (select |#memory_int| (_ bv74 32))))) (fp.leq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))) (fp.geq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854766000.0)))))";
		final String expectedResultAsString = "(and (= (_ bv45 32) |~#WrapperStruct00~0.base|) (exists ((|v_skolemized_q#valueAsBitvector_73| (_ BitVec 64))) (let ((.cse2 (select |#memory_int| (_ bv74 32))) (.cse1 ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_73|))) (let ((.cse0 (let ((.cse3 (concat .cse2 .cse1))) (fp ((_ extract 63 63) .cse3) ((_ extract 62 52) .cse3) ((_ extract 51 0) .cse3))))) (and (fp.leq .cse0 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))) (= (select |#memory_int| (_ bv70 32)) .cse1) (= ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_73|) .cse2) (fp.geq .cse0 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854766000.0)))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_339feda3_ba8e4905_Treesizes_6_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_b~1#1.base_BEFORE_CALL_7| (_ BitVec 32))) (bvugt (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_b~1#1.base_BEFORE_CALL_7|) (_ bv0 32)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_b~1#1.base_BEFORE_CALL_6| (_ BitVec 32))) (bvugt (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_b~1#1.base_BEFORE_CALL_6|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_345171b4_d813420d_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base", "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var0_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_177 (_ BitVec 32))) (not (bvslt ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base v_ArrVal_177) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var0_Pointer~0.base))) (_ bv1 32))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_157 (_ BitVec 32))) (not (bvslt ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base v_ArrVal_157) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var0_Pointer~0.base))) (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_35735e00_14be894f_Treesizes_29_29() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4_Pointer~0.base", "~var_1_5_Pointer~0.base", "~var_1_6_Pointer~0.base", "~var_1_7_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_71 (_ BitVec 32))) (bvsle ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~var_1_7_Pointer~0.base v_ArrVal_71) ~var_1_4_Pointer~0.base))) (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~var_1_7_Pointer~0.base v_ArrVal_71) ~var_1_5_Pointer~0.base))) (_ bv4294967294 32) (bvneg ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~var_1_7_Pointer~0.base v_ArrVal_71) ~var_1_6_Pointer~0.base)))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_51 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~var_1_7_Pointer~0.base v_ArrVal_51))) (bvsle ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~var_1_4_Pointer~0.base))) (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~var_1_5_Pointer~0.base))) (_ bv4294967294 32) (bvneg ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~var_1_6_Pointer~0.base))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_365cd1e1_636bf87d_Treesizes_19_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base", "ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#rhs~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base|) (_ bv0 32)) (exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#rhs~0#1.base_BEFORE_CALL_15| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#rhs~0#1.base_BEFORE_CALL_15| (_ bv4294967288 32))))) (= (bvadd |ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base| (_ bv8 32)) |ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#rhs~0#1.base|))";
		final String expectedResultAsString = "(and (= (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base|) (_ bv0 32)) (= (bvadd |ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#lhs~0#1.base| (_ bv8 32)) |ULTIMATE.start_aws_byte_cursor_compare_lookup_harness_~#rhs~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_36cbda96_224cc9e4_Treesizes_17_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_2_Pointer~0.base", "~var_1_7_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_102 (_ BitVec 32)) (v_ArrVal_101 (_ BitVec 32))) (not (bvslt ((_ sign_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~var_1_7_Pointer~0.base v_ArrVal_101) (bvadd ~var_1_7_Pointer~0.base (_ bv4 32)) v_ArrVal_102) ~var_1_2_Pointer~0.base))) (_ bv0 32))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_68 (_ BitVec 32)) (v_ArrVal_69 (_ BitVec 32))) (not (bvslt ((_ sign_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~var_1_7_Pointer~0.base v_ArrVal_69) (bvadd ~var_1_7_Pointer~0.base (_ bv4 32)) v_ArrVal_68) ~var_1_2_Pointer~0.base))) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_373814ea_a4bac309_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem63#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_property_#t~mem64#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_66 (_ BitVec 32))) (and (not (bvsle |ULTIMATE.start_property_#t~mem64#1| ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_66)))) (= |ULTIMATE.start_property_#t~mem63#1| ((_ extract 7 0) v_arrayElimCell_66))))";
		final String expectedResultAsString = "(exists ((v_arrayElimCell_60 (_ BitVec 32))) (let ((.cse0 ((_ extract 7 0) v_arrayElimCell_60))) (and (= |ULTIMATE.start_property_#t~mem63#1| .cse0) (not (bvsle |ULTIMATE.start_property_#t~mem64#1| ((_ zero_extend 24) .cse0))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_37c81728_dfd85667_Treesizes_23_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "~ARR_SIZE~0"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~index1~0#1_BEFORE_CALL_2| (_ BitVec 16))) (and (bvsge ((_ sign_extend 16) |v_ULTIMATE.start_main_~index1~0#1_BEFORE_CALL_2|) (_ bv0 32)) (bvslt ((_ sign_extend 32) ((_ sign_extend 16) |v_ULTIMATE.start_main_~index1~0#1_BEFORE_CALL_2|)) ~ARR_SIZE~0))) (not (bvslt ((_ sign_extend 32) (_ bv1 32)) ~ARR_SIZE~0)) (exists ((|v_ULTIMATE.start_main_~column~0#1_18| (_ BitVec 32))) (not (bvslt ((_ sign_extend 32) |v_ULTIMATE.start_main_~column~0#1_18|) ~ARR_SIZE~0))))";
		final String expectedResultAsString = "(and (not (bvslt ((_ sign_extend 32) (_ bv1 32)) ~ARR_SIZE~0)) (bvslt ((_ sign_extend 32) (_ bv0 32)) ~ARR_SIZE~0) (exists ((|v_ULTIMATE.start_main_~column~0#1_18| (_ BitVec 32))) (not (bvslt ((_ sign_extend 32) |v_ULTIMATE.start_main_~column~0#1_18|) ~ARR_SIZE~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3832ccd9_b5ac63f8_Treesizes_47_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_array_list_back_~list#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (bvult (bvadd (_ bv20 32) |ULTIMATE.start_aws_array_list_back_~list#1.base|) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8422 32)) (bvugt (bvadd (_ bv20 32) |ULTIMATE.start_aws_array_list_back_~list#1.base|) |#StackHeapBarrier|))) (exists ((|v_ULTIMATE.start_aws_array_list_back_~list#1.base_BEFORE_CALL_7| (_ BitVec 32))) (and (bvult (bvadd (_ bv20 32) |v_ULTIMATE.start_aws_array_list_back_~list#1.base_BEFORE_CALL_7|) (_ bv2147483647 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_array_list_back_~list#1.base_BEFORE_CALL_7|))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv20 32) |v_ULTIMATE.start_aws_array_list_back_~list#1.base_BEFORE_CALL_7|) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8422 32)))))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv16 32) |ULTIMATE.start_aws_array_list_back_~list#1.base|))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv20 32) |ULTIMATE.start_aws_array_list_back_~list#1.base|))) (and (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8422 32)) (bvugt .cse0 |#StackHeapBarrier|))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv16 32) |ULTIMATE.start_aws_array_list_back_~list#1.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_38fc3460_ee559ec4_Treesizes_14_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_89| (_ BitVec 32))) (or (not (bvsge (bvadd (_ bv26 32) |v_fibonacci_#t~ret4_BEFORE_CALL_89|) (_ bv34 32))) (bvsge (bvadd (_ bv21 32) |v_fibonacci_#t~ret4_BEFORE_CALL_89| |fibonacci_#res|) (_ bv34 32))))";
		final String expectedResultAsString = "(= (_ bv5 32) |fibonacci_#res|)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_396b6337_df7c47f8_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_right_trim_pred_~source.base_BEFORE_CALL_8 (_ BitVec 32))) (= (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) v_aws_byte_cursor_right_trim_pred_~source.base_BEFORE_CALL_8)) (select |#memory_int| (bvadd (_ bv2 32) v_aws_byte_cursor_right_trim_pred_~source.base_BEFORE_CALL_8))) (select |#memory_int| (bvadd (_ bv1 32) v_aws_byte_cursor_right_trim_pred_~source.base_BEFORE_CALL_8))) (select |#memory_int| v_aws_byte_cursor_right_trim_pred_~source.base_BEFORE_CALL_8)) (_ bv0 32)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14| (_ BitVec 32))) (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14|))) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_39c6a732_503d1fa2_Treesizes_32_32() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#unsigned_short_int_Array_0~0.base", "~#signed_short_int_Array_0~0.base", "~#unsigned_long_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_149 (_ BitVec 32)) (v_ArrVal_120 (_ BitVec 32))) (= ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_149) (bvadd (_ bv6 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_120) (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|)))) ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_149) (bvadd (_ bv6 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_120) (bvadd (_ bv8 32) |~#signed_short_int_Array_0~0.base|))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_119 (_ BitVec 32)) (v_ArrVal_120 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_119) (bvadd (_ bv6 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_120))) (= ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|)))) ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 (bvadd (_ bv8 32) |~#signed_short_int_Array_0~0.base|)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3a21e13f_5886655e_Treesizes_17_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_6~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (or (= ~var_1_1~0 (_ bv0 8)) (= ~var_1_6~0 (_ bv0 8))) (or (= ((_ zero_extend 24) ~var_1_1~0) (_ bv1 32)) (not (= ~var_1_6~0 (_ bv0 8)))))";
		final String expectedResultAsString = "(let ((.cse0 (= ~var_1_6~0 (_ bv0 8)))) (or (and (= ~var_1_1~0 (_ bv1 8)) .cse0) (and (= ~var_1_1~0 (_ bv0 8)) (not .cse0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3a737bc7_c708b899_Treesizes_15_15() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "~ARR_SIZE~0"),
		};
		final String formulaAsString = "(and (not (bvslt ((_ sign_extend 32) (_ bv1 32)) ~ARR_SIZE~0)) (bvslt ((_ sign_extend 32) (_ bv0 32)) ~ARR_SIZE~0) (exists ((|v_ULTIMATE.start_main_#t~nondet4#1_11| (_ BitVec 16))) (= ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet4#1_11|) ~ARR_SIZE~0)))";
		final String expectedResultAsString = "(and (bvsgt ~ARR_SIZE~0 (_ bv0 64)) (not (bvslt ((_ sign_extend 32) (_ bv1 32)) ~ARR_SIZE~0)) (exists ((|v_ULTIMATE.start_main_~column~0#1_18| (_ BitVec 32))) (not (bvslt ((_ sign_extend 32) |v_ULTIMATE.start_main_~column~0#1_18|) ~ARR_SIZE~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3ae969b_e8dfc9ae_Treesizes_19_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~n"),
		};
		final String formulaAsString = "(forall ((|v_mult_#in~n_BEFORE_CALL_43| (_ BitVec 32))) (or (not (= (bvmul |mult_#in~n| (_ bv4 32)) (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_43|))) (= (bvadd (_ bv1 32) (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_43|)) (bvadd |mult_#in~n| |mult_#res|))))";
		final String expectedResultAsString = "(= |mult_#res| (bvadd (_ bv1 32) (bvmul |mult_#in~n| (_ bv3 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3b5fee11_9f40b51d_Treesizes_22_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base", "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var1_Pointer~0.base", "~signed_long_int_Array_0_arraysigned_long_int_Array_0Var2_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_128 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var2_Pointer~0.base v_ArrVal_128) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var1_Pointer~0.base))) (_ bv4294967264 32)))) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var2_Pointer~0.base v_ArrVal_128) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_106 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var2_Pointer~0.base v_ArrVal_106))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var1_Pointer~0.base))) (_ bv4294967264 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3b6a66f8_8d693768_Treesizes_13_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_86 (_ BitVec 32))) (and (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_86))) |ULTIMATE.start_step_#t~mem13#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_86)) (_ bv0 32))))";
		final String expectedResultAsString = "(= (_ bv0 8) |ULTIMATE.start_step_#t~mem13#1|)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3be0ecf_c65212ac_Treesizes_12_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~result~0#1"),
		};
		final String formulaAsString = "(and (bvsgt (bvadd (_ bv10 32) |ULTIMATE.start_main_~result~0#1|) (_ bv100 32)) (not (bvsgt (bvadd (_ bv9 32) |ULTIMATE.start_main_~result~0#1|) (_ bv100 32))))";
		final String expectedResultAsString = "(= (_ bv91 32) |ULTIMATE.start_main_~result~0#1|)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3c66f967_3790e444_Treesizes_87_87() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_9_Pointer~0.base", "~WrapperStruct00_var_1_14_Pointer~0.base", "~WrapperStruct00_var_1_6_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~WrapperStruct00_var_1_5_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_75 (_ BitVec 32)) (v_ArrVal_111 (_ BitVec 32)) (v_ArrVal_110 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_110) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_9_Pointer~0.base) v_ArrVal_111) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_75) ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_110) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_9_Pointer~0.base) v_ArrVal_111) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_75) ~WrapperStruct00_var_1_3_Pointer~0.base))) (bvneg (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_110) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_9_Pointer~0.base) v_ArrVal_111) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_75) ~WrapperStruct00_var_1_6_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_110) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_9_Pointer~0.base) v_ArrVal_111) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_75) ~WrapperStruct00_var_1_4_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_110) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_9_Pointer~0.base) v_ArrVal_111) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_75) ~WrapperStruct00_var_1_5_Pointer~0.base))))))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_75 (_ BitVec 32)) (v_ArrVal_73 (_ BitVec 32)) (v_ArrVal_74 (_ BitVec 32))) (let ((.cse0 (store (store (store |#memory_int| ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_74) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_9_Pointer~0.base) v_ArrVal_73) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_75))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (bvadd (bvneg (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_5_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_6_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_4_Pointer~0.base))))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_3_Pointer~0.base)))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3d2b718a_e05aa1c6_Treesizes_32_32() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#signed_char_Array_0~0.base", "~#signed_long_int_Array_0~0.base", "~#signed_short_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_331 (_ BitVec 32))) (not (bvsgt (bvor ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_331) (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32))))) ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_331) (bvadd |~#signed_char_Array_0~0.base| (_ bv2 32)))))) (select (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_331) (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_315 (_ BitVec 32))) (not (let ((.cse0 (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_315))) (bvsgt (bvor ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 (bvadd |~#signed_char_Array_0~0.base| (_ bv2 32))))) ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32)))))) (select .cse0 (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3e17db45_997078b8_Treesizes_27_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_end_~list#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_end_~list#1.base_BEFORE_CALL_4| (_ BitVec 32))) (and (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_end_~list#1.base_BEFORE_CALL_4|))) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_end_~list#1.base_BEFORE_CALL_4|) (_ bv2147483647 32)))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_end_~list#1.base|))) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_end_~list#1.base|) (_ bv2147483647 32)))";
		final String expectedResultAsString = "(and (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_end_~list#1.base|))) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_end_~list#1.base|) (_ bv2147483647 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3ed8d86f_cf6b7bf1_Treesizes_80_68() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (fp.geq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32))))) ((_ to_fp 11 53) roundNearestTiesToEven ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0)))) (= (_ bv46 32) |~#WrapperStruct00~0.base|) (exists ((|v_skolemized_q#valueAsBitvector_52| (_ BitVec 64))) (and (= ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_52|) (select |#memory_int| (_ bv74 32))) (= (select |#memory_int| (_ bv70 32)) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_52|)))) (fp.leq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32))))) ((_ to_fp 11 53) roundNearestTiesToEven ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854766000.0))))";
		final String expectedResultAsString = "(and (exists ((|v_skolemized_q#valueAsBitvector_52| (_ BitVec 64))) (let ((.cse0 ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_52|)) (.cse1 ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_52|))) (let ((.cse2 (let ((.cse3 (concat .cse0 .cse1))) (fp ((_ extract 63 63) .cse3) ((_ extract 62 52) .cse3) ((_ extract 51 0) .cse3))))) (and (= .cse0 (select |#memory_int| (_ bv74 32))) (= (select |#memory_int| (_ bv70 32)) .cse1) (fp.leq .cse2 ((_ to_fp 11 53) roundNearestTiesToEven ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854766000.0))) (fp.geq .cse2 ((_ to_fp 11 53) roundNearestTiesToEven ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0)))))))) (= (_ bv46 32) |~#WrapperStruct00~0.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_3fb00f42_823d002f_Treesizes_19_19() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var3_Pointer~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base", "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_67 (_ BitVec 32))) (not (bvslt ((_ zero_extend 16) ((_ extract 15 0) (select (store |#memory_int| ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base v_ArrVal_67) ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var4_Pointer~0.base))) ((_ zero_extend 16) ((_ extract 15 0) (select (store |#memory_int| ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base v_ArrVal_67) ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var3_Pointer~0.base))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_48 (_ BitVec 32))) (not (let ((.cse0 (store |#memory_int| ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base v_ArrVal_48))) (bvslt ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var4_Pointer~0.base))) ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var3_Pointer~0.base)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4055fbdc_1f8ff1a1_Treesizes_48_29() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#y~0#1.base", "ULTIMATE.start_main_~#x~0#1.base", "ULTIMATE.start_main_~#c~0#1.base", "ULTIMATE.start_main_~#z~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (bvsge (select |#memory_int| |ULTIMATE.start_main_~#z~0#1.base|) (_ bv1 32)) (= |ULTIMATE.start_main_~#c~0#1.base| (bvadd |ULTIMATE.start_main_~#y~0#1.base| (_ bv8 32))) (= |ULTIMATE.start_main_~#y~0#1.base| (bvadd |ULTIMATE.start_main_~#x~0#1.base| (_ bv8 32))) (= |ULTIMATE.start_main_~#x~0#1.base| (bvadd |ULTIMATE.start_main_~#z~0#1.base| (_ bv8 32))) (bvult |ULTIMATE.start_main_~#x~0#1.base| (_ bv2147483647 32)) (bvult (bvadd |ULTIMATE.start_main_~#y~0#1.base| (_ bv16 32)) (_ bv2147483647 32)) (exists ((|v_ULTIMATE.start_main_~#c~0#1.base_BEFORE_CALL_2| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_main_~#c~0#1.base_BEFORE_CALL_2| (_ bv4294967280 32)) (_ bv2147483647 32)) (bvsge (select |#memory_int| (bvadd |v_ULTIMATE.start_main_~#c~0#1.base_BEFORE_CALL_2| (_ bv4294967272 32))) (_ bv1 32)) (bvult (bvadd |v_ULTIMATE.start_main_~#c~0#1.base_BEFORE_CALL_2| (_ bv8 32)) (_ bv2147483647 32)))))";
		final String expectedResultAsString = "(and (bvsge (select |#memory_int| |ULTIMATE.start_main_~#z~0#1.base|) (_ bv1 32)) (= |ULTIMATE.start_main_~#c~0#1.base| (bvadd |ULTIMATE.start_main_~#y~0#1.base| (_ bv8 32))) (= |ULTIMATE.start_main_~#y~0#1.base| (bvadd |ULTIMATE.start_main_~#x~0#1.base| (_ bv8 32))) (= |ULTIMATE.start_main_~#x~0#1.base| (bvadd |ULTIMATE.start_main_~#z~0#1.base| (_ bv8 32))) (bvult |ULTIMATE.start_main_~#x~0#1.base| (_ bv2147483647 32)) (bvult (bvadd |ULTIMATE.start_main_~#y~0#1.base| (_ bv16 32)) (_ bv2147483647 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_410453a_57c07f7a_Treesizes_47_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (bvult (bvadd (_ bv20 32) |ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base|) (_ bv2147483647 32)) (exists ((|v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_51| (_ BitVec 32))) (and (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8424 32)) (bvugt (bvadd (_ bv20 32) |v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_51|) |#StackHeapBarrier|))) (bvult (bvadd (_ bv20 32) |v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_51|) (_ bv2147483647 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base_BEFORE_CALL_51|))))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8424 32)) (bvugt (bvadd (_ bv20 32) |ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base|) |#StackHeapBarrier|))) (= (select |#memory_$Pointer$.base| (bvadd (_ bv16 32) |ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base|)) (_ bv0 32)))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv20 32) |ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base|))) (and (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8424 32)) (bvugt .cse0 |#StackHeapBarrier|))) (= (select |#memory_$Pointer$.base| (bvadd (_ bv16 32) |ULTIMATE.start_aws_array_list_set_at_harness_~#list~0#1.base|)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_419efbcb_6cd64170_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_12| (_ BitVec 32))) (and (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_12|) (_ bv2147483647 32)) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_12|)) (_ bv0 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_12|) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8821 32))))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_8| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_8|))) (and (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_harness_~#buf~3#1.base_BEFORE_CALL_8|)) (_ bv0 32)) (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8821 32)) (bvugt .cse0 |#StackHeapBarrier|))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_42391f44_484cb45b_Treesizes_55_50() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#unsigned_short_int_Array_0~0.base", "~#signed_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (not (= |~#signed_char_Array_0~0.base| (bvadd (_ bv5 32) |~#unsigned_short_int_Array_0~0.base|))) (bvsle ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv6 32) |~#unsigned_short_int_Array_0~0.base|)))) (_ bv32767 32)) (bvsge ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv8 32) |~#unsigned_short_int_Array_0~0.base|)))) (_ bv16383 32)) (exists ((|v_ULTIMATE.start_updateVariables_#t~nondet82#1_17| (_ BitVec 16))) (= ((_ sign_extend 16) |v_ULTIMATE.start_updateVariables_#t~nondet82#1_17|) (select |#memory_int| (bvadd (_ bv8 32) |~#unsigned_short_int_Array_0~0.base|)))) (bvsle ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv8 32) |~#unsigned_short_int_Array_0~0.base|)))) (_ bv32767 32)) (not (= |~#signed_char_Array_0~0.base| (bvadd (_ bv11 32) |~#unsigned_short_int_Array_0~0.base|))) (not (= (bvadd (_ bv7 32) |~#unsigned_short_int_Array_0~0.base|) |~#signed_char_Array_0~0.base|)))";
		final String expectedResultAsString = "(and (not (= |~#signed_char_Array_0~0.base| (bvadd (_ bv5 32) |~#unsigned_short_int_Array_0~0.base|))) (exists ((|v_ULTIMATE.start_updateVariables_#t~nondet82#1_17| (_ BitVec 16))) (let ((.cse1 ((_ sign_extend 16) |v_ULTIMATE.start_updateVariables_#t~nondet82#1_17|))) (let ((.cse0 ((_ zero_extend 16) ((_ extract 15 0) .cse1)))) (and (bvsle .cse0 (_ bv32767 32)) (bvsge .cse0 (_ bv16383 32)) (= .cse1 (select |#memory_int| (bvadd (_ bv8 32) |~#unsigned_short_int_Array_0~0.base|))))))) (bvsle ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv6 32) |~#unsigned_short_int_Array_0~0.base|)))) (_ bv32767 32)) (not (= |~#signed_char_Array_0~0.base| (bvadd (_ bv11 32) |~#unsigned_short_int_Array_0~0.base|))) (not (= (bvadd (_ bv7 32) |~#unsigned_short_int_Array_0~0.base|) |~#signed_char_Array_0~0.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_42f4d09e_252b3a70_Treesizes_9_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_9~0", "~var_1_10~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_10~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_9~0) (_ bv0 32)))";
		final String expectedResultAsString = "(and (= ~var_1_9~0 (_ bv0 8)) (= (_ bv0 8) ~var_1_10~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_439fc69d_9ec8d1c8_Treesizes_8_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (bvsgt (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv12 32))) (_ bv3 32)))";
		final String expectedResultAsString = "(bvsle (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv12 32))) (_ bv3 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_44080e26_a43ec067_Treesizes_14_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (forall ((|v_isOdd_#in~n_BEFORE_CALL_21| (_ BitVec 32))) (= (bvsrem |v_isOdd_#in~n_BEFORE_CALL_21| (_ bv2 32)) (_ bv1 32))) (= (_ bv4 32) |isEven_#in~n|)) (= (_ bv1 32) |isEven_#res|))";
		final String expectedResultAsString = "(and (= (_ bv4 32) |isEven_#in~n|) (= (_ bv1 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_449e0ec6_77b9345_Treesizes_19_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_11~0"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_14~0"),
		};
		final String formulaAsString = "(or (not (bvsle ((_ sign_extend 24) ~var_1_11~0) (bvsdiv ~var_1_14~0 (_ bv4294967294 32)))) (forall ((~var_1_27~0 (_ BitVec 8)) (~var_1_31~0 (_ BitVec 8)) (~var_1_30~0 (_ BitVec 8))) (bvsge (bvsdiv ~var_1_14~0 (bvadd ((_ zero_extend 24) ~var_1_31~0) ((_ zero_extend 24) ~var_1_30~0))) ((_ sign_extend 24) ~var_1_27~0))))";
		final String expectedResultAsString = "(not (bvsle ((_ sign_extend 24) ~var_1_11~0) (bvsdiv ~var_1_14~0 (_ bv4294967294 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4585f0cc_4b0e4010_Treesizes_12_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967292 32)) (_ bv0 32))) (= |ULTIMATE.start_main_~n~0#1| (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv4 32))))";
		final String expectedResultAsString = "(and (not (bvugt |ULTIMATE.start_main_~x~0#1| (_ bv0 32))) (= |ULTIMATE.start_main_~n~0#1| (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv4 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_460b0f03_260472bb_Treesizes_25_25() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_32| (_ BitVec 32))) (not (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_32|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_32|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_32|))) (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_32|)))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_31| (_ BitVec 32))) (not (= (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_31|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_31|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_31|))) (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_reserve_harness_~#buf~3#1.base_BEFORE_CALL_31|)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_46b06d28_6cfdb5f9_Treesizes_17_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~z~0#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (bvsge |ULTIMATE.start_main_~z~0#1| (_ bv1 32)) (= (_ bv0 64) (bvadd (bvneg |ULTIMATE.start_main_~y~0#1|) ((_ sign_extend 32) |ULTIMATE.start_main_~z~0#1|))) (= (_ bv1 64) |ULTIMATE.start_main_~x~0#1|) (bvsle |ULTIMATE.start_main_~z~0#1| (_ bv50 32)))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_main_~y~0#1| ((_ sign_extend 32) |ULTIMATE.start_main_~z~0#1|)) (bvsge |ULTIMATE.start_main_~z~0#1| (_ bv1 32)) (= (_ bv1 64) |ULTIMATE.start_main_~x~0#1|) (bvsle |ULTIMATE.start_main_~z~0#1| (_ bv50 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_47598345_d1b849da_Treesizes_28_28() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var3_Pointer~0.base", "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var2_Pointer~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base", "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var6_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_86 (_ BitVec 32)) (v_ArrVal_104 (_ BitVec 32))) (= ((_ zero_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var2_Pointer~0.base v_ArrVal_104) ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base v_ArrVal_86) ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var6_Pointer~0.base))) ((_ zero_extend 16) ((_ extract 15 0) (bvadd ((_ zero_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var2_Pointer~0.base v_ArrVal_104) ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base v_ArrVal_86) ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var3_Pointer~0.base))) (_ bv4294967274 32))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_86 (_ BitVec 32)) (v_ArrVal_85 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var2_Pointer~0.base v_ArrVal_85) ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base v_ArrVal_86))) (= ((_ zero_extend 16) ((_ extract 15 0) (bvadd ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var3_Pointer~0.base))) (_ bv4294967274 32)))) ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var6_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4835379_bbfe6055_Treesizes_15_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem7#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base", "~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base"),
		};
		final String formulaAsString = "(and (= (_ bv83 32) ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base) (= (_ bv49 32) ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base) (= (_ bv48 32) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base) (exists ((v_arrayElimCell_29 (_ BitVec 32))) (= ((_ extract 7 0) v_arrayElimCell_29) |ULTIMATE.start_step_#t~mem7#1|)))";
		final String expectedResultAsString = "(and (= (_ bv83 32) ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base) (= (_ bv49 32) ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base) (= (_ bv48 32) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var1_Pointer~0.base))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_48d70bc6_d724645b_Treesizes_65_65() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#float_Array_0~0.base", "~#signed_long_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_74 (_ BitVec 32))) (not (fp.leq (fp ((_ extract 31 31) (select (store |#memory_int| (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_74) (bvadd |~#float_Array_0~0.base| (_ bv8 32)))) ((_ extract 30 23) (select (store |#memory_int| (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_74) (bvadd |~#float_Array_0~0.base| (_ bv8 32)))) ((_ extract 22 0) (select (store |#memory_int| (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_74) (bvadd |~#float_Array_0~0.base| (_ bv8 32))))) (fp ((_ extract 31 31) (select (store |#memory_int| (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_74) |~#float_Array_0~0.base|)) ((_ extract 30 23) (select (store |#memory_int| (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_74) |~#float_Array_0~0.base|)) ((_ extract 22 0) (select (store |#memory_int| (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_74) |~#float_Array_0~0.base|))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_50 (_ BitVec 32))) (not (let ((.cse1 (store |#memory_int| (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_50))) (fp.leq (let ((.cse0 (select .cse1 (bvadd |~#float_Array_0~0.base| (_ bv8 32))))) (fp ((_ extract 31 31) .cse0) ((_ extract 30 23) .cse0) ((_ extract 22 0) .cse0))) (let ((.cse2 (select .cse1 |~#float_Array_0~0.base|))) (fp ((_ extract 31 31) .cse2) ((_ extract 30 23) .cse2) ((_ extract 22 0) .cse2)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_497be806_ce40567a_Treesizes_23_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#y~0#1.base", "ULTIMATE.start_main_~#w~0#1.base", "ULTIMATE.start_main_~#x~0#1.base", "ULTIMATE.start_main_~#z~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| |ULTIMATE.start_main_~#w~0#1.base|) (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|)) (= |ULTIMATE.start_main_~#z~0#1.base| (bvadd |ULTIMATE.start_main_~#y~0#1.base| (_ bv4 32))) (= |ULTIMATE.start_main_~#z~0#1.base| (bvadd |ULTIMATE.start_main_~#w~0#1.base| (_ bv12 32))) (= |ULTIMATE.start_main_~#z~0#1.base| (bvadd |ULTIMATE.start_main_~#x~0#1.base| (_ bv8 32))))";
		final String expectedResultAsString = "(and (= (select |#memory_int| |ULTIMATE.start_main_~#w~0#1.base|) (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|)) (= |ULTIMATE.start_main_~#z~0#1.base| (bvadd |ULTIMATE.start_main_~#y~0#1.base| (_ bv4 32))) (= |ULTIMATE.start_main_~#z~0#1.base| (bvadd |ULTIMATE.start_main_~#w~0#1.base| (_ bv12 32))) (= |ULTIMATE.start_main_~#x~0#1.base| (bvadd |ULTIMATE.start_main_~#w~0#1.base| (_ bv4 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4a162f1e_b23e435e_Treesizes_64_64() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~mask_SORT_12~0#1", "ULTIMATE.start_main_~var_114~0#1", "ULTIMATE.start_main_~var_8~0#1", "ULTIMATE.start_main_~mask_SORT_1~0#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_main_~state_117~0#1"),
		};
		final String formulaAsString = "(and (or (not (bvslt ((_ zero_extend 16) ((_ zero_extend 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_12~0#1|) ((_ zero_extend 24) |ULTIMATE.start_main_~var_114~0#1|))))) ((_ zero_extend 16) |ULTIMATE.start_main_~state_117~0#1|))) (forall ((|v_ULTIMATE.start_main_~var_120_arg_1~0#1_46| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_123_arg_1~0#1_46| (_ BitVec 8))) (= ((_ extract 7 0) (bvand ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_123_arg_1~0#1_46|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_120_arg_1~0#1_46|))))))))))) (_ bv0 8)))) (or (bvslt ((_ zero_extend 16) ((_ zero_extend 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_12~0#1|) ((_ zero_extend 24) |ULTIMATE.start_main_~var_114~0#1|))))) ((_ zero_extend 16) |ULTIMATE.start_main_~state_117~0#1|)) (forall ((|v_ULTIMATE.start_main_~var_123_arg_1~0#1_46| (_ BitVec 8))) (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |ULTIMATE.start_main_~var_8~0#1|)))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_123_arg_1~0#1_46|)))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|))) (_ bv0 8)))))";
		final String expectedResultAsString = "(let ((.cse0 (bvslt ((_ zero_extend 16) ((_ zero_extend 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_12~0#1|) ((_ zero_extend 24) |ULTIMATE.start_main_~var_114~0#1|))))) ((_ zero_extend 16) |ULTIMATE.start_main_~state_117~0#1|))) (.cse1 ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|))) (and (or (not .cse0) (forall ((|v_ULTIMATE.start_main_~var_120_arg_1~0#1_40| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_123_arg_1~0#1_40| (_ BitVec 8))) (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_120_arg_1~0#1_40|)))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_123_arg_1~0#1_40|)))) .cse1)) (_ bv0 8)))) (or .cse0 (forall ((|v_ULTIMATE.start_main_~var_123_arg_1~0#1_40| (_ BitVec 8))) (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |ULTIMATE.start_main_~var_8~0#1|)))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_123_arg_1~0#1_40|)))) .cse1)) (_ bv0 8))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4a873c69_39ef6ecf_Treesizes_40_40() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#signed_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (_ bv89 32)))) (select |#memory_int| (_ bv67 32))) (bvsle ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (_ bv89 32)))) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (_ bv66 32))))) (bvsle ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (_ bv64 32)))) (_ bv31 32)) (= ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (_ bv64 32)))) (select |#memory_int| (_ bv66 32))) (= |~#signed_char_Array_0~0.base| (_ bv63 32)))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (_ bv67 32))) (.cse1 ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (_ bv64 32)))))) (and (= ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (_ bv89 32)))) .cse0) (bvsle .cse1 (_ bv31 32)) (= .cse1 (select |#memory_int| (_ bv66 32))) (bvsle .cse0 ((_ sign_extend 24) ((_ extract 7 0) .cse1))) (= |~#signed_char_Array_0~0.base| (_ bv63 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4aed3ee0_5ef9076d_Treesizes_24_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "size_#res"),
		};
		final String formulaAsString = "(and (forall ((|v_size_#t~ret28_BEFORE_CALL_2| (_ BitVec 32))) (or (bvult (_ bv0 32) (bvadd (bvmul (_ bv4 32) |v_size_#t~ret28_BEFORE_CALL_2|) (_ bv4 32) (bvmul |size_#res| (_ bv4 32)))) (not (bvult (_ bv0 32) (bvadd (bvmul (_ bv4 32) |v_size_#t~ret28_BEFORE_CALL_2|) (_ bv4 32)))))) (= |size_#res| (_ bv0 32)))";
		final String expectedResultAsString = "(= |size_#res| (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4b3f8a00_9f8a56a2_Treesizes_17_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_property_#t~mem87#1", "ULTIMATE.start_property_#t~mem86#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_18 (_ BitVec 32)) (v_arrayElimCell_17 (_ BitVec 32))) (and (bvsgt ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_17)) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_18))) (= |ULTIMATE.start_property_#t~mem87#1| ((_ extract 15 0) v_arrayElimCell_18)) (= |ULTIMATE.start_property_#t~mem86#1| ((_ extract 15 0) v_arrayElimCell_17))))";
		final String expectedResultAsString = "(exists ((v_arrayElimCell_12 (_ BitVec 32)) (v_arrayElimCell_11 (_ BitVec 32))) (let ((.cse0 ((_ extract 15 0) v_arrayElimCell_11)) (.cse1 ((_ extract 15 0) v_arrayElimCell_12))) (and (= |ULTIMATE.start_property_#t~mem86#1| .cse0) (bvsgt ((_ sign_extend 16) .cse0) ((_ sign_extend 16) .cse1)) (= .cse1 |ULTIMATE.start_property_#t~mem87#1|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4b963ed4_ab388f55_Treesizes_85_85() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_#t~ite12#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "~ARR_SIZE~0", "ULTIMATE.start_main_~index1~0#1", "ULTIMATE.start_main_~index2~0#1", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(or (and (= (_ bv0 32) (bvadd (bvmul (_ bv4 32) ((_ extract 31 0) |ULTIMATE.start_main_~index2~0#1|)) (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) (bvadd (bvneg |ULTIMATE.start_main_~index1~0#1|) ~ARR_SIZE~0 (_ bv18446744073709551615 64))) ((_ extract 31 0) ~ARR_SIZE~0))))) (= (_ bv1 64) (bvadd ((_ sign_extend 32) |ULTIMATE.start_main_#t~ite12#1|) |ULTIMATE.start_main_~sum~0#1|))) (and (forall ((v_arrayElimCell_5 (_ BitVec 32))) (or (= (_ bv1 64) (bvadd ((_ sign_extend 32) v_arrayElimCell_5) |ULTIMATE.start_main_~sum~0#1|)) (= (_ bv0 64) (bvadd ((_ sign_extend 32) v_arrayElimCell_5) |ULTIMATE.start_main_~sum~0#1|)))) (not (= (_ bv0 32) (bvadd (bvmul (_ bv4 32) ((_ extract 31 0) |ULTIMATE.start_main_~index2~0#1|)) (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) (bvadd (bvneg |ULTIMATE.start_main_~index1~0#1|) ~ARR_SIZE~0 (_ bv18446744073709551615 64))) ((_ extract 31 0) ~ARR_SIZE~0))))))) (and (= (_ bv0 32) (bvadd (bvmul (_ bv4 32) ((_ extract 31 0) |ULTIMATE.start_main_~index2~0#1|)) (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) (bvadd (bvneg |ULTIMATE.start_main_~index1~0#1|) ~ARR_SIZE~0 (_ bv18446744073709551615 64))) ((_ extract 31 0) ~ARR_SIZE~0))))) (= (_ bv0 64) (bvadd ((_ sign_extend 32) |ULTIMATE.start_main_#t~ite12#1|) |ULTIMATE.start_main_~sum~0#1|))))";
		final String expectedResultAsString = "(let ((.cse0 (= (_ bv0 32) (bvadd (bvmul (_ bv4 32) ((_ extract 31 0) |ULTIMATE.start_main_~index2~0#1|)) (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) (bvadd (bvneg |ULTIMATE.start_main_~index1~0#1|) ~ARR_SIZE~0 (_ bv18446744073709551615 64))) ((_ extract 31 0) ~ARR_SIZE~0)))))) (.cse1 (bvadd ((_ sign_extend 32) |ULTIMATE.start_main_#t~ite12#1|) |ULTIMATE.start_main_~sum~0#1|))) (or (and .cse0 (= (_ bv1 64) .cse1)) (and (not .cse0) (forall ((v_arrayElimCell_2 (_ BitVec 32))) (let ((.cse2 (bvadd ((_ sign_extend 32) v_arrayElimCell_2) |ULTIMATE.start_main_~sum~0#1|))) (or (= (_ bv0 64) .cse2) (= (_ bv1 64) .cse2))))) (and .cse0 (= (_ bv0 64) .cse1))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4c241023_8b34e13d_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#array~0#1.base", "ULTIMATE.start_main_~#i~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(or (forall ((v_ArrVal_32 (_ BitVec 32))) (bvult (bvadd (select (store |#memory_int| (bvadd (bvmul (_ bv4 32) (select |#memory_int| |ULTIMATE.start_main_~#i~0#1.base|)) |ULTIMATE.start_main_~#array~0#1.base|) v_ArrVal_32) |ULTIMATE.start_main_~#i~0#1.base|) (_ bv1 32)) (_ bv100000 32))) (not (bvult (select |#memory_int| |ULTIMATE.start_main_~#i~0#1.base|) (_ bv100000 32))))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| |ULTIMATE.start_main_~#i~0#1.base|))) (or (forall ((|v_func_to_recursive_line_40_to_41_0_#t~nondet26_13| (_ BitVec 32))) (bvult (bvadd (_ bv1 32) (select (store |#memory_int| (bvadd (bvmul (_ bv4 32) .cse0) |ULTIMATE.start_main_~#array~0#1.base|) |v_func_to_recursive_line_40_to_41_0_#t~nondet26_13|) |ULTIMATE.start_main_~#i~0#1.base|)) (_ bv100000 32))) (not (bvult .cse0 (_ bv100000 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4c857e87_b57633d4_Treesizes_40_40() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~state_85~0#1", "ULTIMATE.start_main_~mask_SORT_1~0#1"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_main_~var_91_arg_1~0#1_48| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_88_arg_1~0#1_48| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_103_arg_1~0#1_48| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_107_arg_1~0#1_48| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_115_arg_0~0#1_49| (_ BitVec 8))) (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvor ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_107_arg_1~0#1_48|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_103_arg_1~0#1_48|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_91_arg_1~0#1_48|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_88_arg_1~0#1_48|) ((_ zero_extend 24) |ULTIMATE.start_main_~state_85~0#1|))))))))))))))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_115_arg_0~0#1_49|)))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|))) (_ bv0 8)))";
		final String expectedResultAsString = "(forall ((|v_ULTIMATE.start_main_~var_115_arg_0~0#1_46| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_103_arg_1~0#1_45| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_107_arg_1~0#1_45| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_88_arg_1~0#1_45| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_91_arg_1~0#1_45| (_ BitVec 8))) (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_115_arg_0~0#1_46|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvor ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |ULTIMATE.start_main_~state_85~0#1|) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_88_arg_1~0#1_45|)))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_91_arg_1~0#1_45|)))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_103_arg_1~0#1_45|))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_107_arg_1~0#1_45|)))))))))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|))) (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4d9917a3_efebe0fe_Treesizes_14_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_27| (_ BitVec 32))) (not (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_27|) (_ bv0 32)))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|))))";
		final String expectedResultAsString = "(not (= (_ bv0 32) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4e67e544_56a1539b_Treesizes_91_91() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_main_~index2~0#1", "ULTIMATE.start_main_~index1~0#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_#t~ite12#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "~ARR_SIZE~0", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(or (and (= (_ bv0 32) (bvadd (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) ~ARR_SIZE~0) ((_ sign_extend 16) |ULTIMATE.start_main_~index1~0#1|))) (bvmul (_ bv4 32) ((_ extract 31 0) (bvadd ~ARR_SIZE~0 (_ bv18446744073709551615 64) (bvneg ((_ sign_extend 32) ((_ sign_extend 16) |ULTIMATE.start_main_~index2~0#1|)))))))) (= (_ bv0 64) (bvadd ((_ sign_extend 32) |ULTIMATE.start_main_#t~ite12#1|) |ULTIMATE.start_main_~sum~0#1|))) (and (= (_ bv0 32) (bvadd (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) ~ARR_SIZE~0) ((_ sign_extend 16) |ULTIMATE.start_main_~index1~0#1|))) (bvmul (_ bv4 32) ((_ extract 31 0) (bvadd ~ARR_SIZE~0 (_ bv18446744073709551615 64) (bvneg ((_ sign_extend 32) ((_ sign_extend 16) |ULTIMATE.start_main_~index2~0#1|)))))))) (= (_ bv1 64) (bvadd ((_ sign_extend 32) |ULTIMATE.start_main_#t~ite12#1|) |ULTIMATE.start_main_~sum~0#1|))) (and (not (= (_ bv0 32) (bvadd (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) ~ARR_SIZE~0) ((_ sign_extend 16) |ULTIMATE.start_main_~index1~0#1|))) (bvmul (_ bv4 32) ((_ extract 31 0) (bvadd ~ARR_SIZE~0 (_ bv18446744073709551615 64) (bvneg ((_ sign_extend 32) ((_ sign_extend 16) |ULTIMATE.start_main_~index2~0#1|))))))))) (forall ((v_arrayElimCell_5 (_ BitVec 32))) (or (= (_ bv1 64) (bvadd ((_ sign_extend 32) v_arrayElimCell_5) |ULTIMATE.start_main_~sum~0#1|)) (= (_ bv0 64) (bvadd ((_ sign_extend 32) v_arrayElimCell_5) |ULTIMATE.start_main_~sum~0#1|))))))";
		final String expectedResultAsString = "(let ((.cse1 (bvadd ((_ sign_extend 32) |ULTIMATE.start_main_#t~ite12#1|) |ULTIMATE.start_main_~sum~0#1|)) (.cse0 (= (_ bv0 32) (bvadd (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) ~ARR_SIZE~0) ((_ sign_extend 16) |ULTIMATE.start_main_~index1~0#1|))) (bvmul (_ bv4 32) ((_ extract 31 0) (bvadd ~ARR_SIZE~0 (_ bv18446744073709551615 64) (bvneg ((_ sign_extend 32) ((_ sign_extend 16) |ULTIMATE.start_main_~index2~0#1|)))))))))) (or (and .cse0 (= (_ bv0 64) .cse1)) (and .cse0 (= (_ bv1 64) .cse1)) (and (not .cse0) (forall ((v_arrayElimCell_2 (_ BitVec 32))) (let ((.cse2 (bvadd ((_ sign_extend 32) v_arrayElimCell_2) |ULTIMATE.start_main_~sum~0#1|))) (or (= (_ bv0 64) .cse2) (= (_ bv1 64) .cse2)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_4f40fe41_7e2952c9_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_12_Pointer~0.base", "~WrapperStruct00_var_1_7_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_180 (_ BitVec 32)) (v_ArrVal_158 (_ BitVec 32))) (= ((_ sign_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_180) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_158) ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ sign_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_180) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_158) ~WrapperStruct00_var_1_7_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_158 (_ BitVec 32)) (v_ArrVal_157 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_157) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_158))) (= ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_7_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_500d3f4_573c5f54_Treesizes_9_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_24~0", "~var_1_23~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_23~0) (_ bv0 32)) (bvsge ((_ zero_extend 24) ~var_1_24~0) (_ bv1 32)))";
		final String expectedResultAsString = "(and (= (_ bv0 8) ~var_1_23~0) (not (= (_ bv0 8) ~var_1_24~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_50a7caed_4c24e141_Treesizes_14_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~z~0#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (bvsge |ULTIMATE.start_main_~z~0#1| (_ bv1 32)) (= (_ bv0 64) (bvadd (bvneg |ULTIMATE.start_main_~y~0#1|) ((_ sign_extend 32) |ULTIMATE.start_main_~z~0#1|))) (= (_ bv1 64) |ULTIMATE.start_main_~x~0#1|))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_main_~y~0#1| ((_ sign_extend 32) |ULTIMATE.start_main_~z~0#1|)) (bvsge |ULTIMATE.start_main_~z~0#1| (_ bv1 32)) (= (_ bv1 64) |ULTIMATE.start_main_~x~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_514d8b42_8e30e340_Treesizes_4_4() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_0~0#1"),
		};
		final String formulaAsString = "(not (= |ULTIMATE.start_step_~stepLocal_0~0#1| (_ bv0 8)))";
		final String expectedResultAsString = "(bvsge ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_0~0#1|) (_ bv1 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_52374797_10c3288c_Treesizes_23_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#t~ret4", "sum_#in~m"),
		};
		final String formulaAsString = "(and (not (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967293 32)) (_ bv0 32))) (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967292 32)) (_ bv0 32)) (= |sum_#t~ret4| (bvadd |sum_#in~m| |sum_#in~n|)))";
		final String expectedResultAsString = "(and (bvsle (bvadd |sum_#in~n| (_ bv4294967292 32)) (_ bv0 32)) (= |sum_#t~ret4| (bvadd |sum_#in~m| |sum_#in~n|)) (not (bvsle (bvadd |sum_#in~n| (_ bv4294967293 32)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_52a0efb4_5af45e66_Treesizes_9_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_28~0", "~var_1_27~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_27~0)) (not (= (_ bv0 8) ~var_1_28~0)))";
		final String expectedResultAsString = "(and (bvsge ((_ zero_extend 24) ~var_1_27~0) (_ bv1 32)) (bvsge ((_ zero_extend 24) ~var_1_28~0) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_53432464_110fb52b_Treesizes_132_127() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#double_Array_0~0.base", "~#signed_long_int_Array_0~0.base", "~#unsigned_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (fp.geq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv52 32)) (select |#memory_int| (_ bv48 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv52 32)) (select |#memory_int| (_ bv48 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv52 32)) (select |#memory_int| (_ bv48 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854776000.0)))) (exists ((|v_skolemized_q#valueAsBitvector_21| (_ BitVec 64))) (= (select |#memory_int| (_ bv60 32)) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_21|))) (fp.geq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv60 32)) (select |#memory_int| (_ bv56 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv60 32)) (select |#memory_int| (_ bv56 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv60 32)) (select |#memory_int| (_ bv56 32))))) (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv52 32)) (select |#memory_int| (_ bv48 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv52 32)) (select |#memory_int| (_ bv48 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv52 32)) (select |#memory_int| (_ bv48 32)))))) (= (_ bv48 32) |~#double_Array_0~0.base|) (= (_ bv64 32) |~#signed_long_int_Array_0~0.base|) (fp.leq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv60 32)) (select |#memory_int| (_ bv56 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv60 32)) (select |#memory_int| (_ bv56 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv60 32)) (select |#memory_int| (_ bv56 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))) (= (_ bv68 32) |~#unsigned_char_Array_0~0.base|))";
		final String expectedResultAsString = "(let ((.cse0 (let ((.cse4 (concat (select |#memory_int| (_ bv52 32)) (select |#memory_int| (_ bv48 32))))) (fp ((_ extract 63 63) .cse4) ((_ extract 62 52) .cse4) ((_ extract 51 0) .cse4))))) (and (fp.geq .cse0 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854776000.0)))) (exists ((|v_skolemized_q#valueAsBitvector_21| (_ BitVec 64))) (let ((.cse2 ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_21|))) (let ((.cse1 (let ((.cse3 (concat .cse2 (select |#memory_int| (_ bv56 32))))) (fp ((_ extract 63 63) .cse3) ((_ extract 62 52) .cse3) ((_ extract 51 0) .cse3))))) (and (fp.geq .cse1 .cse0) (= (select |#memory_int| (_ bv60 32)) .cse2) (fp.leq .cse1 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))))))) (= (_ bv48 32) |~#double_Array_0~0.base|) (= (_ bv64 32) |~#signed_long_int_Array_0~0.base|) (= (_ bv68 32) |~#unsigned_char_Array_0~0.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_53d64f45_1d14a197_Treesizes_9_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv45 32) |~#WrapperStruct00~0.base|)))))";
		final String expectedResultAsString = "(bvsge ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv45 32) |~#WrapperStruct00~0.base|)))) (_ bv1 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_54af6544_d9c434a9_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_19_Pointer~0.base", "~WrapperStruct00_var_1_7_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_260 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_19_Pointer~0.base v_ArrVal_260) ~WrapperStruct00_var_1_7_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_19_Pointer~0.base v_ArrVal_260) ~WrapperStruct00_var_1_1_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_211 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~WrapperStruct00_var_1_19_Pointer~0.base v_ArrVal_211))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_7_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5513f1fa_5bfb2b0b_Treesizes_59_37() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_7_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_40 (_ BitVec 32))) (or (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| (bvadd (_ bv34 32) |~#WrapperStruct00~0.base|) v_ArrVal_40) ~WrapperStruct00_var_1_7_Pointer~0.base))) (not (= ((_ extract 7 0) (select (store (store |#memory_int| (bvadd (_ bv34 32) |~#WrapperStruct00~0.base|) v_ArrVal_40) ~WrapperStruct00_var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~WrapperStruct00_var_1_7_Pointer~0.base)) (_ bv0 8))))) (forall ((v_ArrVal_40 (_ BitVec 32))) (or (= (_ bv0 8) ((_ extract 7 0) (select (store (store |#memory_int| (bvadd (_ bv34 32) |~#WrapperStruct00~0.base|) v_ArrVal_40) ~WrapperStruct00_var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~WrapperStruct00_var_1_7_Pointer~0.base))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| (bvadd (_ bv34 32) |~#WrapperStruct00~0.base|) v_ArrVal_40) ~WrapperStruct00_var_1_7_Pointer~0.base)))))))";
		final String expectedResultAsString = "(let ((.cse0 (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| ~WrapperStruct00_var_1_7_Pointer~0.base))))) (and (or (not .cse0) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~WrapperStruct00_var_1_7_Pointer~0.base)))) (or .cse0 (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~WrapperStruct00_var_1_7_Pointer~0.base)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_55bb55eb_e46afd90_Treesizes_57_57() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_15_Pointer~0.base", "~WrapperStruct00_var_1_14_Pointer~0.base", "~WrapperStruct00_var_1_17_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_162 (_ BitVec 32)) (v_ArrVal_129 (_ BitVec 32)) (v_ArrVal_128 (_ BitVec 32)) (v_ArrVal_131 (_ BitVec 32)) (v_ArrVal_163 (_ BitVec 32)) (v_ArrVal_130 (_ BitVec 32))) (= ((_ zero_extend 16) ((_ zero_extend 8) ((_ extract 7 0) (select (store (store (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_162) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_8_Pointer~0.base) v_ArrVal_163) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_130) ~WrapperStruct00_var_1_15_Pointer~0.base v_ArrVal_131) ~WrapperStruct00_var_1_17_Pointer~0.base v_ArrVal_129) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_17_Pointer~0.base) v_ArrVal_128) ~WrapperStruct00_var_1_4_Pointer~0.base)))) ((_ zero_extend 16) ((_ extract 15 0) (select (store (store (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_162) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_8_Pointer~0.base) v_ArrVal_163) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_130) ~WrapperStruct00_var_1_15_Pointer~0.base v_ArrVal_131) ~WrapperStruct00_var_1_17_Pointer~0.base v_ArrVal_129) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_17_Pointer~0.base) v_ArrVal_128) ~WrapperStruct00_var_1_1_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_129 (_ BitVec 32)) (v_ArrVal_128 (_ BitVec 32)) (v_ArrVal_127 (_ BitVec 32)) (v_ArrVal_126 (_ BitVec 32)) (v_ArrVal_131 (_ BitVec 32)) (v_ArrVal_130 (_ BitVec 32))) (let ((.cse0 (store (store (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_127) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_8_Pointer~0.base) v_ArrVal_126) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_130) ~WrapperStruct00_var_1_15_Pointer~0.base v_ArrVal_131) ~WrapperStruct00_var_1_17_Pointer~0.base v_ArrVal_129) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_17_Pointer~0.base) v_ArrVal_128))) (= ((_ zero_extend 16) ((_ zero_extend 8) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_4_Pointer~0.base)))) ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_56730337_65bfdb61_Treesizes_53_44() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~CELLCOUNT~0", "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#volArray~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(or (forall ((v_ArrVal_58 (_ BitVec 32))) (= (select (store (store (store (store |#memory_int| (bvadd (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv8 32)) (_ bv4294967292 32) |ULTIMATE.start_main_~#volArray~0#1.base|) v_ArrVal_58) (bvadd (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv8 32)) |ULTIMATE.start_main_~#volArray~0#1.base|) (_ bv0 32)) (bvadd (_ bv8 32) (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv8 32)) |ULTIMATE.start_main_~#volArray~0#1.base|) (_ bv0 32)) (bvadd (_ bv16 32) (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv8 32)) |ULTIMATE.start_main_~#volArray~0#1.base|) (_ bv0 32)) |ULTIMATE.start_main_~#volArray~0#1.base|) (_ bv0 32))) (not (bvsle (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv3 32)) (bvsdiv ~CELLCOUNT~0 (_ bv2 32)))) (bvsle (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv4 32)) (bvsdiv ~CELLCOUNT~0 (_ bv2 32))))";
		final String expectedResultAsString = "(let ((.cse0 (bvsdiv ~CELLCOUNT~0 (_ bv2 32)))) (or (not (bvsle (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv3 32)) .cse0)) (bvsle (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv4 32)) .cse0) (= (_ bv0 32) (select (let ((.cse1 (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv8 32)))) (store (store (store |#memory_int| (bvadd .cse1 |ULTIMATE.start_main_~#volArray~0#1.base|) (_ bv0 32)) (bvadd (_ bv8 32) .cse1 |ULTIMATE.start_main_~#volArray~0#1.base|) (_ bv0 32)) (bvadd (_ bv16 32) .cse1 |ULTIMATE.start_main_~#volArray~0#1.base|) (_ bv0 32))) |ULTIMATE.start_main_~#volArray~0#1.base|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_56fd7883_adc08fde_Treesizes_37_35() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base", "~last_1_WrapperStruct00_var_1_6~0"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ((_ sign_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv4 32) |~#WrapperStruct00~0.base|)))) (select |#memory_int| (bvadd (_ bv21 32) |~#WrapperStruct00~0.base|))) (bvsgt (_ bv64 32) ((_ sign_extend 16) ((_ extract 15 0) ((_ sign_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv4 32) |~#WrapperStruct00~0.base|))))))) (bvsgt ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv4 32) |~#WrapperStruct00~0.base|)))) (_ bv64 32)) (= ~last_1_WrapperStruct00_var_1_6~0 (_ bv64 32)))";
		final String expectedResultAsString = "(let ((.cse0 ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv4 32) |~#WrapperStruct00~0.base|)))) (.cse1 (select |#memory_int| (bvadd (_ bv21 32) |~#WrapperStruct00~0.base|)))) (and (= ((_ sign_extend 16) .cse0) .cse1) (bvsgt ((_ zero_extend 16) .cse0) (_ bv64 32)) (= ~last_1_WrapperStruct00_var_1_6~0 (_ bv64 32)) (bvsgt (_ bv64 32) ((_ sign_extend 16) ((_ extract 15 0) .cse1)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_57af395_3a01b997_Treesizes_47_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (bvugt (select |#memory_$Pointer$.base| (bvadd |ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base| (_ bv4 32))) (_ bv0 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd |ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base| (_ bv16 32)) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8833 32)))) (bvult (bvadd |ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base| (_ bv16 32)) (_ bv2147483647 32)) (exists ((|v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_12| (_ BitVec 32))) (and (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_12|) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_12|) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8833 32)))) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_12|)) (_ bv0 32)))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd |ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base| (_ bv16 32)))) (and (bvugt (select |#memory_$Pointer$.base| (bvadd |ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base| (_ bv4 32))) (_ bv0 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8833 32)))) (bvult .cse0 (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_586543d9_3394b3ee_Treesizes_44_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#res", "sum_#in~m"),
		};
		final String formulaAsString = "(or (and (forall ((|v_sum_#in~m_BEFORE_CALL_4| (_ BitVec 32))) (bvsle (bvadd (bvmul |v_sum_#in~m_BEFORE_CALL_4| (_ bv4294967295 32)) |sum_#res| (_ bv4294967293 32)) (_ bv0 32))) (forall ((|v_sum_#in~m_BEFORE_CALL_4| (_ BitVec 32))) (not (bvsle (bvadd (bvmul |v_sum_#in~m_BEFORE_CALL_4| (_ bv4294967295 32)) |sum_#res| (_ bv4294967294 32)) (_ bv0 32))))) (and (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (not (bvsle (bvadd (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967295 32)) (_ bv0 32))) (bvsle (bvadd (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967294 32)) (_ bv0 32))))";
		final String expectedResultAsString = "(let ((.cse0 (bvmul |sum_#in~m| (_ bv4294967295 32)))) (and (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (not (bvsle (bvadd .cse0 |sum_#res| (_ bv4294967295 32)) (_ bv0 32))) (bvsle (bvadd .cse0 |sum_#res| (_ bv4294967294 32)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_59081fcc_c8029b5f_Treesizes_47_42() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~Y~0#1", "ULTIMATE.start_main_~X~0#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1", "ULTIMATE.start_main_~v~0#1"),
		};
		final String formulaAsString = "(and (= (_ bv1 64) |ULTIMATE.start_main_~y~0#1|) (bvsle |ULTIMATE.start_main_~X~0#1| (_ bv5 32)) (bvsge |ULTIMATE.start_main_~X~0#1| (_ bv0 32)) (not (bvslt (bvadd |ULTIMATE.start_main_~v~0#1| (bvmul ((_ sign_extend 32) |ULTIMATE.start_main_~Y~0#1|) (_ bv18446744073709551614 64)) (bvmul (bvneg ((_ sign_extend 32) |ULTIMATE.start_main_~X~0#1|)) (_ bv18446744073709551614 64))) (_ bv0 64))) (= (_ bv1 64) |ULTIMATE.start_main_~x~0#1|) (bvsle |ULTIMATE.start_main_~Y~0#1| (_ bv5 32)) (= (_ bv0 64) (bvadd (bvneg |ULTIMATE.start_main_~v~0#1|) (bvmul (_ bv4 64) ((_ sign_extend 32) |ULTIMATE.start_main_~Y~0#1|)) (bvneg (bvmul (_ bv2 64) ((_ sign_extend 32) |ULTIMATE.start_main_~X~0#1|))) (bvneg ((_ sign_extend 32) |ULTIMATE.start_main_~X~0#1|)))))";
		final String expectedResultAsString = "(let ((.cse1 ((_ sign_extend 32) |ULTIMATE.start_main_~Y~0#1|)) (.cse0 (bvneg ((_ sign_extend 32) |ULTIMATE.start_main_~X~0#1|)))) (and (= (_ bv1 64) |ULTIMATE.start_main_~y~0#1|) (bvsle |ULTIMATE.start_main_~X~0#1| (_ bv5 32)) (bvsge |ULTIMATE.start_main_~X~0#1| (_ bv0 32)) (= |ULTIMATE.start_main_~v~0#1| (bvadd (bvmul (_ bv3 64) .cse0) (bvmul (_ bv4 64) .cse1))) (not (bvslt (bvadd |ULTIMATE.start_main_~v~0#1| (bvmul .cse1 (_ bv18446744073709551614 64)) (bvmul .cse0 (_ bv18446744073709551614 64))) (_ bv0 64))) (= (_ bv1 64) |ULTIMATE.start_main_~x~0#1|) (bvsle |ULTIMATE.start_main_~Y~0#1| (_ bv5 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_599f7c94_56e065d7_Treesizes_14_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem98#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_property_#t~mem99#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_17 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem99#1| (bvadd (_ bv1 32) (bvneg ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_17))))) (= |ULTIMATE.start_property_#t~mem98#1| ((_ extract 7 0) v_arrayElimCell_17))))";
		final String expectedResultAsString = "(= |ULTIMATE.start_property_#t~mem99#1| (bvadd (bvneg ((_ sign_extend 24) |ULTIMATE.start_property_#t~mem98#1|)) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5a587dba_7d5bf203_Treesizes_40_40() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base", "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base", "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var1_Pointer~0.base", "~float_Array_0_arrayfloat_Array_0arrayVar1_Pointer~0.base", "~signed_long_int_Array_0_arraysigned_long_int_Array_0Var2_Pointer~0.base", "~float_Array_0_arrayfloat_Array_0arrayVar2_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_106 (_ BitVec 32)) (v_ArrVal_105 (_ BitVec 32)) (v_ArrVal_104 (_ BitVec 32)) (v_ArrVal_125 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~float_Array_0_arrayfloat_Array_0arrayVar1_Pointer~0.base v_ArrVal_125) ~float_Array_0_arrayfloat_Array_0arrayVar2_Pointer~0.base v_ArrVal_104) ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base v_ArrVal_105) ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var2_Pointer~0.base v_ArrVal_106) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~float_Array_0_arrayfloat_Array_0arrayVar1_Pointer~0.base v_ArrVal_125) ~float_Array_0_arrayfloat_Array_0arrayVar2_Pointer~0.base v_ArrVal_104) ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base v_ArrVal_105) ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var2_Pointer~0.base v_ArrVal_106) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var1_Pointer~0.base))) (_ bv4294967264 32))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_106 (_ BitVec 32)) (v_ArrVal_105 (_ BitVec 32)) (v_ArrVal_104 (_ BitVec 32)) (v_ArrVal_103 (_ BitVec 32))) (let ((.cse0 (store (store (store (store |#memory_int| ~float_Array_0_arrayfloat_Array_0arrayVar1_Pointer~0.base v_ArrVal_103) ~float_Array_0_arrayfloat_Array_0arrayVar2_Pointer~0.base v_ArrVal_104) ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base v_ArrVal_105) ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var2_Pointer~0.base v_ArrVal_106))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var1_Pointer~0.base))) (_ bv4294967264 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5afadb_72120a6d_Treesizes_10_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "addition_#in~n"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_14| (_ BitVec 32))) (or (not (= |addition_#in~n| ((_ sign_extend 32) |v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_14|))) (bvslt |v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_14| (_ bv100 32))))";
		final String expectedResultAsString = "(forall ((|v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_13| (_ BitVec 32))) (or (bvslt |v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_13| (_ bv100 32)) (not (= ((_ sign_extend 32) |v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_13|) |addition_#in~n|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5b6024f0_70f293d1_Treesizes_71_71() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~state_432~0#1", "ULTIMATE.start_main_~state_510~0#1", "ULTIMATE.start_main_~mask_SORT_1~0#1"),
		};
		final String formulaAsString = "(and (or (= (_ bv0 8) |ULTIMATE.start_main_~state_510~0#1|) (forall ((|v_ULTIMATE.start_main_~var_536_arg_1~0#1_14| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_539_arg_0~0#1_16| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_536_arg_1~0#1_14|)))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_539_arg_0~0#1_16|)))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|)))))) (or (forall ((|v_ULTIMATE.start_main_~var_435_arg_1~0#1_14| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_454_arg_1~0#1_14| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_438_arg_1~0#1_14| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_539_arg_0~0#1_16| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_450_arg_1~0#1_14| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvor ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_438_arg_1~0#1_14|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |ULTIMATE.start_main_~state_432~0#1|) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_435_arg_1~0#1_14|))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_450_arg_1~0#1_14|))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_454_arg_1~0#1_14|))))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_539_arg_0~0#1_16|)))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|))))) (not (= (_ bv0 8) |ULTIMATE.start_main_~state_510~0#1|))))";
		final String expectedResultAsString = "(let ((.cse0 ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|)) (.cse1 (= (_ bv0 8) |ULTIMATE.start_main_~state_510~0#1|))) (and (or (forall ((|v_ULTIMATE.start_main_~var_539_arg_0~0#1_13| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_438_arg_1~0#1_11| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_435_arg_1~0#1_11| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_454_arg_1~0#1_11| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_450_arg_1~0#1_11| (_ BitVec 8))) (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvor ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_454_arg_1~0#1_11|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_438_arg_1~0#1_11|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_435_arg_1~0#1_11|) ((_ zero_extend 24) |ULTIMATE.start_main_~state_432~0#1|))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_450_arg_1~0#1_11|))))))))))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_539_arg_0~0#1_13|)))) .cse0)) (_ bv0 8))) (not .cse1)) (or (forall ((|v_ULTIMATE.start_main_~var_539_arg_0~0#1_13| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_536_arg_1~0#1_11| (_ BitVec 8))) (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_539_arg_0~0#1_13|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_536_arg_1~0#1_11|))))))))) .cse0)) (_ bv0 8))) .cse1)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5c56b47d_709ba7cb_Treesizes_56_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_b~1#1.base", "ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_a~1#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_b~1#1.base_BEFORE_CALL_8| (_ BitVec 32)) (|v_ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_a~1#1.base_BEFORE_CALL_7| (_ BitVec 32))) (and (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_a~1#1.base_BEFORE_CALL_7|) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_b~1#1.base_BEFORE_CALL_8|)) (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|#StackAllocations| (_ BitVec 32))) (and (bvult |#StackAllocations| (_ bv2147483647 32)) (bvugt |#StackAllocations| |#StackHeapBarrier|) (bvult (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_a~1#1.base_BEFORE_CALL_7|) |#StackHeapBarrier|))))) (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|#StackAllocations| (_ BitVec 32))) (and (bvult |#StackAllocations| (_ bv2147483647 32)) (bvugt |#StackAllocations| |#StackHeapBarrier|) (bvult (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_a~1#1.base|) |#StackHeapBarrier|))) (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_b~1#1.base|) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_a~1#1.base|)) (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|v_ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_a~1#1.base_BEFORE_CALL_6| (_ BitVec 32)) (|#StackAllocations| (_ BitVec 32))) (and (bvult (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_a~1#1.base_BEFORE_CALL_6|) |#StackHeapBarrier|) (bvult |#StackAllocations| (_ bv2147483647 32)) (bvugt |#StackAllocations| |#StackHeapBarrier|))))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_a~1#1.base|))) (and (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|#StackAllocations| (_ BitVec 32))) (and (bvult |#StackAllocations| (_ bv2147483647 32)) (bvugt |#StackAllocations| |#StackHeapBarrier|) (bvult .cse0 |#StackHeapBarrier|))) (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_array_list_comparator_string_harness_~#str_b~1#1.base|) .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5c9a972e_609d359d_Treesizes_93_65() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (bvsge (select |#memory_int| (bvadd (_ bv12 32) |~#WrapperStruct00~0.base|)) (_ bv0 32)) (bvsle (select |#memory_int| (bvadd (_ bv12 32) |~#WrapperStruct00~0.base|)) (_ bv536870912 32)) (bvsle (select |#memory_int| (bvadd (_ bv16 32) |~#WrapperStruct00~0.base|)) (_ bv536870911 32)) (bvsle (bvadd (select |#memory_int| |~#WrapperStruct00~0.base|) (_ bv128 32) (bvmul (select |#memory_int| (bvadd (_ bv12 32) |~#WrapperStruct00~0.base|)) (_ bv4294967295 32)) (bvmul (_ bv4294967295 32) (select |#memory_int| (bvadd (_ bv16 32) |~#WrapperStruct00~0.base|)))) (_ bv1073741823 32)) (= (bvadd (select |#memory_int| (bvadd (_ bv20 32) |~#WrapperStruct00~0.base|)) (select |#memory_int| (bvadd (_ bv12 32) |~#WrapperStruct00~0.base|)) (select |#memory_int| (bvadd (_ bv16 32) |~#WrapperStruct00~0.base|))) (bvadd (select |#memory_int| |~#WrapperStruct00~0.base|) (_ bv128 32))) (bvsge (select |#memory_int| (bvadd (_ bv16 32) |~#WrapperStruct00~0.base|)) (_ bv3758096385 32)) (bvsge (bvadd (select |#memory_int| |~#WrapperStruct00~0.base|) (_ bv128 32) (bvmul (select |#memory_int| (bvadd (_ bv12 32) |~#WrapperStruct00~0.base|)) (_ bv4294967295 32)) (bvmul (_ bv4294967295 32) (select |#memory_int| (bvadd (_ bv16 32) |~#WrapperStruct00~0.base|)))) (_ bv3221225473 32)))";
		final String expectedResultAsString = "(let ((.cse1 (select |#memory_int| (bvadd (_ bv20 32) |~#WrapperStruct00~0.base|))) (.cse0 (select |#memory_int| (bvadd (_ bv12 32) |~#WrapperStruct00~0.base|))) (.cse2 (select |#memory_int| (bvadd (_ bv16 32) |~#WrapperStruct00~0.base|)))) (and (bvsge .cse0 (_ bv0 32)) (bvsge .cse1 (_ bv3221225473 32)) (bvsle .cse0 (_ bv536870912 32)) (bvsle .cse2 (_ bv536870911 32)) (bvsle .cse1 (_ bv1073741823 32)) (= (bvadd .cse1 .cse0 .cse2) (bvadd (select |#memory_int| |~#WrapperStruct00~0.base|) (_ bv128 32))) (bvsge .cse2 (_ bv3758096385 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5d0e6377_5c2c6a38_Treesizes_18_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~i~0#1_246| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul (_ bv4 32) |v_ULTIMATE.start_main_~i~0#1_246|))))) (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv32 32)))))";
		final String expectedResultAsString = "(= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv32 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5e04e77d_72b6d497_Treesizes_9_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv20 32) |~#WrapperStruct00~0.base|)))))";
		final String expectedResultAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv20 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5e648f32_709410b0_Treesizes_72_60() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#unsigned_short_int_Array_0~0.base", "~#signed_char_Array_0~0.base", "~#signed_long_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_172 (_ BitVec 32)) (v_ArrVal_175 (_ BitVec 32))) (= ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| |~#unsigned_short_int_Array_0~0.base| v_ArrVal_172) (bvadd |~#signed_char_Array_0~0.base| (_ bv3 32)) ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| |~#unsigned_short_int_Array_0~0.base| v_ArrVal_172) (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32))))) (_ bv4294967264 32))))) (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_175) (bvadd |~#signed_char_Array_0~0.base| (_ bv3 32))))) ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| |~#unsigned_short_int_Array_0~0.base| v_ArrVal_172) (bvadd |~#signed_char_Array_0~0.base| (_ bv3 32)) ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| |~#unsigned_short_int_Array_0~0.base| v_ArrVal_172) (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32))))) (_ bv4294967264 32))))) (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_175) (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32))))) (_ bv4294967264 32))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_175 (_ BitVec 32))) (let ((.cse1 (bvadd |~#signed_char_Array_0~0.base| (_ bv3 32))) (.cse2 (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32)))) (let ((.cse0 (store (store |#memory_int| .cse1 ((_ sign_extend 24) ((_ extract 7 0) (bvadd (_ bv4294967264 32) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| .cse2))))))) (bvadd (_ bv4 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_175))) (= ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 .cse1))) ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 .cse2))) (_ bv4294967264 32))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5efc89e6_4163f5cb_Treesizes_10_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_13_Pointer~0.base", "~WrapperStruct00_var_1_10_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_70 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_70) ~WrapperStruct00_var_1_13_Pointer~0.base))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_55 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_55) ~WrapperStruct00_var_1_13_Pointer~0.base))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5f9a5739_997b21e4_Treesizes_292_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "~var_1_5~0", "~var_1_6~0", "~var_1_1~0"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4~0", "~var_1_2~0", "~var_1_3~0"),
		};
		final String formulaAsString = "(and (or (not (= ((_ sign_extend 16) ~var_1_1~0) ((_ sign_extend 16) ((_ extract 15 0) (bvadd ((_ sign_extend 16) ~var_1_6~0) ((_ sign_extend 16) ~var_1_5~0)))))) (and (or (= (bvudiv ~var_1_3~0 ~var_1_4~0) ~var_1_2~0) (forall ((~var_1_7~0 (_ BitVec 16)) (~var_1_8~0 (_ BitVec 16))) (or (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) (bvneg ((_ sign_extend 16) ~var_1_5~0)) ((_ sign_extend 16) ~var_1_7~0)))) ((_ sign_extend 16) ~var_1_1~0)) (not (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) ((_ sign_extend 16) ~var_1_7~0) ((_ sign_extend 16) ~var_1_5~0)))) ((_ sign_extend 16) ~var_1_1~0))))) (not (bvslt ((_ sign_extend 16) ~var_1_5~0) (_ bv0 32)))) (or (= (bvudiv ~var_1_3~0 ~var_1_4~0) ~var_1_2~0) (bvslt ((_ sign_extend 16) ~var_1_5~0) (_ bv0 32)) (forall ((~var_1_7~0 (_ BitVec 16)) (~var_1_8~0 (_ BitVec 16))) (or (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) ((_ sign_extend 16) ~var_1_7~0) ((_ sign_extend 16) ~var_1_5~0)))) ((_ sign_extend 16) ~var_1_1~0)) (not (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) (bvneg ((_ sign_extend 16) ~var_1_5~0)) ((_ sign_extend 16) ~var_1_7~0)))) ((_ sign_extend 16) ~var_1_1~0)))))) (or (= (bvudiv ~var_1_3~0 ~var_1_4~0) ~var_1_2~0) (forall ((~var_1_7~0 (_ BitVec 16)) (~var_1_8~0 (_ BitVec 16))) (or (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) ((_ sign_extend 16) ~var_1_7~0) ((_ sign_extend 16) ~var_1_5~0)))) ((_ sign_extend 16) ~var_1_1~0)) (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) (bvneg ((_ sign_extend 16) ~var_1_5~0)) ((_ sign_extend 16) ~var_1_7~0)))) ((_ sign_extend 16) ~var_1_1~0))))))) (or (= ((_ sign_extend 16) ~var_1_1~0) ((_ sign_extend 16) ((_ extract 15 0) (bvadd ((_ sign_extend 16) ~var_1_6~0) ((_ sign_extend 16) ~var_1_5~0))))) (and (or (forall ((~var_1_7~0 (_ BitVec 16)) (~var_1_8~0 (_ BitVec 16))) (or (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) (bvneg ((_ sign_extend 16) ~var_1_5~0)) ((_ sign_extend 16) ~var_1_7~0)))) ((_ sign_extend 16) ~var_1_1~0)) (not (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) ((_ sign_extend 16) ~var_1_7~0) ((_ sign_extend 16) ~var_1_5~0)))) ((_ sign_extend 16) ~var_1_1~0))))) (and (not (bvslt ((_ sign_extend 16) ~var_1_5~0) (_ bv0 32))) (not (= (bvudiv ~var_1_3~0 ~var_1_4~0) ~var_1_2~0)))) (or (forall ((~var_1_7~0 (_ BitVec 16)) (~var_1_8~0 (_ BitVec 16))) (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) ((_ sign_extend 16) ~var_1_7~0) ((_ sign_extend 16) ~var_1_5~0)))) ((_ sign_extend 16) ~var_1_1~0))) (bvslt ((_ sign_extend 16) ~var_1_5~0) (_ bv0 32))) (or (forall ((~var_1_7~0 (_ BitVec 16)) (~var_1_8~0 (_ BitVec 16))) (or (not (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) (bvneg ((_ sign_extend 16) ~var_1_5~0)) ((_ sign_extend 16) ~var_1_7~0)))) ((_ sign_extend 16) ~var_1_1~0))) (not (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) ((_ sign_extend 16) ~var_1_7~0) ((_ sign_extend 16) ~var_1_5~0)))) ((_ sign_extend 16) ~var_1_1~0))))) (not (= (bvudiv ~var_1_3~0 ~var_1_4~0) ~var_1_2~0))) (or (forall ((~var_1_7~0 (_ BitVec 16)) (~var_1_8~0 (_ BitVec 16))) (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) ((_ sign_extend 16) ~var_1_7~0) ((_ sign_extend 16) ~var_1_5~0)))) ((_ sign_extend 16) ~var_1_1~0))) (not (= (bvudiv ~var_1_3~0 ~var_1_4~0) ~var_1_2~0))) (forall ((~var_1_7~0 (_ BitVec 16)) (~var_1_8~0 (_ BitVec 16))) (or (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) ((_ sign_extend 16) ~var_1_7~0) ((_ sign_extend 16) ~var_1_5~0)))) ((_ sign_extend 16) ~var_1_1~0)) (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd (bvneg ((_ sign_extend 16) ~var_1_8~0)) (bvneg ((_ sign_extend 16) ~var_1_5~0)) ((_ sign_extend 16) ~var_1_7~0)))) ((_ sign_extend 16) ~var_1_1~0)))))))";
		final String expectedResultAsString = "(and (= (bvudiv ~var_1_3~0 ~var_1_4~0) ~var_1_2~0) (= ~var_1_1~0 ((_ extract 15 0) (bvadd ((_ sign_extend 16) ~var_1_6~0) ((_ sign_extend 16) ~var_1_5~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_5ffe8b7c_7ab758cf_Treesizes_8_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_5~0", "ULTIMATE.start_step_~stepLocal_3~0#1"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_3~0#1|) (_ bv0 32)) (= ~var_1_5~0 (_ bv0 8)))";
		final String expectedResultAsString = "(and (= ~var_1_5~0 (_ bv0 8)) (= |ULTIMATE.start_step_~stepLocal_3~0#1| (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_607b702a_9526b86c_Treesizes_8_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (bvslt ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base))) (_ bv0 32)))";
		final String expectedResultAsString = "(bvsge ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_614d3ed6_408f3b82_Treesizes_22_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~signed_char_Array_0_arraysigned_char_Array_0Var3_Pointer~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base", "~signed_long_int_Array_0_arraysigned_long_int_Array_0Var1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_129 (_ BitVec 32))) (= ((_ sign_extend 24) ((_ extract 7 0) (bvadd (_ bv4294967264 32) ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var1_Pointer~0.base v_ArrVal_129) ~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base)))))) ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var1_Pointer~0.base v_ArrVal_129) ~signed_char_Array_0_arraysigned_char_Array_0Var3_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_109 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var1_Pointer~0.base v_ArrVal_109))) (= ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 ~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base))) (_ bv4294967264 32)))) ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 ~signed_char_Array_0_arraysigned_char_Array_0Var3_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_618e95e2_479b49a5_Treesizes_88_46() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~#a~0#1.base", "ULTIMATE.start_main_~i~0#1"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|ULTIMATE.start_main_~j~0#1| (_ BitVec 32))) (and (bvslt |ULTIMATE.start_main_~j~0#1| (_ bv10000 32)) (bvslt (bvadd (select |#memory_int| (bvadd |ULTIMATE.start_main_~#a~0#1.base| (_ bv4 32))) (_ bv4294967295 32) (bvmul |ULTIMATE.start_main_~j~0#1| (_ bv4294967295 32))) (_ bv10000 32)) (bvsgt (bvadd (select |#memory_int| (bvadd |ULTIMATE.start_main_~#a~0#1.base| (_ bv4 32))) (_ bv4294967295 32) (bvmul |ULTIMATE.start_main_~j~0#1| (_ bv4294967295 32))) (_ bv0 32)) (bvsgt |ULTIMATE.start_main_~j~0#1| (_ bv0 32)))) (exists ((|v_ULTIMATE.start_main_~#a~0#1.base_BEFORE_CALL_10| (_ BitVec 32)) (|v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_20| (_ BitVec 32)) (|ULTIMATE.start_main_~j~0#1| (_ BitVec 32))) (and (bvslt |v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_20| (_ bv100000 32)) (bvslt |ULTIMATE.start_main_~j~0#1| (_ bv10000 32)) (bvsgt (bvadd (_ bv4294967295 32) (select |#memory_int| (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#a~0#1.base_BEFORE_CALL_10|)) (bvmul |ULTIMATE.start_main_~j~0#1| (_ bv4294967295 32))) (_ bv0 32)) (bvslt (bvadd (_ bv4294967295 32) (select |#memory_int| (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#a~0#1.base_BEFORE_CALL_10|)) (bvmul |ULTIMATE.start_main_~j~0#1| (_ bv4294967295 32))) (_ bv10000 32)) (bvsgt |ULTIMATE.start_main_~j~0#1| (_ bv0 32)) (bvult (bvadd |v_ULTIMATE.start_main_~#a~0#1.base_BEFORE_CALL_10| (bvmul (_ bv4 32) |v_ULTIMATE.start_main_~n~0#1_BEFORE_CALL_20|)) (_ bv2147483647 32)))) (bvult (bvadd |ULTIMATE.start_main_~#a~0#1.base| (bvmul |ULTIMATE.start_main_~n~0#1| (_ bv4 32))) (_ bv2147483647 32)) (bvslt |ULTIMATE.start_main_~n~0#1| (_ bv100000 32)) (= |ULTIMATE.start_main_~i~0#1| (_ bv2 32)))";
		final String expectedResultAsString = "(and (exists ((|ULTIMATE.start_main_~j~0#1| (_ BitVec 32))) (let ((.cse0 (bvadd (select |#memory_int| (bvadd |ULTIMATE.start_main_~#a~0#1.base| (_ bv4 32))) (_ bv4294967295 32) (bvmul |ULTIMATE.start_main_~j~0#1| (_ bv4294967295 32))))) (and (bvslt |ULTIMATE.start_main_~j~0#1| (_ bv10000 32)) (bvslt .cse0 (_ bv10000 32)) (bvsgt .cse0 (_ bv0 32)) (bvsgt |ULTIMATE.start_main_~j~0#1| (_ bv0 32))))) (bvult (bvadd |ULTIMATE.start_main_~#a~0#1.base| (bvmul |ULTIMATE.start_main_~n~0#1| (_ bv4 32))) (_ bv2147483647 32)) (bvslt |ULTIMATE.start_main_~n~0#1| (_ bv100000 32)) (= |ULTIMATE.start_main_~i~0#1| (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_625f2a3b_99ea3572_Treesizes_22_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var3_Pointer~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base", "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var6_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_105 (_ BitVec 32))) (= ((_ zero_extend 16) ((_ extract 15 0) (bvadd ((_ zero_extend 16) ((_ extract 15 0) (select (store |#memory_int| ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base v_ArrVal_105) ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var3_Pointer~0.base))) (_ bv4294967274 32)))) ((_ zero_extend 16) ((_ extract 15 0) (select (store |#memory_int| ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base v_ArrVal_105) ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var6_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_86 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base v_ArrVal_86))) (= ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var6_Pointer~0.base))) ((_ zero_extend 16) ((_ extract 15 0) (bvadd ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var3_Pointer~0.base))) (_ bv4294967274 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6298d055_d13c72c8_Treesizes_22_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_2| (_ BitVec 32))) (and (= (bvadd (_ bv16 32) (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_2| (_ bv4294967292 32)))) |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_2|) (bvugt |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_2| (_ bv71 32)) (bvult |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_2| (_ bv2147483647 32)) (bvult (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_2|) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_1| (_ BitVec 32))) (and (= |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_1| (bvadd (_ bv16 32) (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_1| (_ bv4294967292 32))))) (bvugt |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_1| (_ bv71 32)) (bvult |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_1| (_ bv2147483647 32)) (bvult (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_1|) (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_638840d2_48e5a44d_Treesizes_17_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_ring_buffer_acquire_~dest#1.base_BEFORE_CALL_5| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_aws_ring_buffer_acquire_~dest#1.base_BEFORE_CALL_5| (_ bv16 32)) (_ bv2147483647 32)) (bvugt (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_ring_buffer_acquire_~dest#1.base_BEFORE_CALL_5| (_ bv4 32))) (_ bv0 32)) (bvult |v_ULTIMATE.start_aws_ring_buffer_acquire_~dest#1.base_BEFORE_CALL_5| (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_ring_buffer_acquire_harness_~#buf~3#1.base_BEFORE_CALL_46| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_aws_ring_buffer_acquire_harness_~#buf~3#1.base_BEFORE_CALL_46| (_ bv16 32)) (_ bv2147483647 32)) (bvult |v_ULTIMATE.start_aws_ring_buffer_acquire_harness_~#buf~3#1.base_BEFORE_CALL_46| (_ bv2147483647 32)) (bvugt (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_ring_buffer_acquire_harness_~#buf~3#1.base_BEFORE_CALL_46| (_ bv4 32))) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_63e00156_3c333172_Treesizes_31_29() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36| (_ BitVec 32))) (and (= (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|)) (= (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|)) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv67 32)) (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|) |#StackHeapBarrier|))) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|#StackHeapBarrier| (_ BitVec 32)) (|v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|))) (and (= (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|)) (= (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|)) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|) (bvugt |#StackHeapBarrier| (_ bv67 32)) (bvugt .cse0 |#StackHeapBarrier|) (bvult .cse0 (_ bv2147483647 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_645b6e82_518201b7_Treesizes_45_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_back_~list#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19| (_ BitVec 32))) (and (bvugt (bvadd |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19| (_ bv16 32)) |#StackHeapBarrier|) (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19| (_ bv16 32)) (_ bv2147483647 32)) (= (bvadd |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19| (_ bv8 32)) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_19|)) (bvugt |#StackHeapBarrier| (_ bv70 32)))) (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_back_~list#1.base|) (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_back_~list#1.base|)) (exists ((|v_#StackHeapBarrier_3| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_back_~list#1.base|) |v_#StackHeapBarrier_3|) (bvugt |v_#StackHeapBarrier_3| (_ bv70 32)))) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_back_~list#1.base|) (_ bv2147483647 32)))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_back_~list#1.base|))) (and (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_back_~list#1.base|) (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_back_~list#1.base|)) (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv70 32)) (bvugt .cse0 |#StackHeapBarrier|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_64c2f8e8_54887a5e_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_15| (_ BitVec 32))) (and (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_15|) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8833 32)))) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_15|)) (_ bv0 32)) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_15|) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_12| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_12|))) (and (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8833 32)))) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_string_eq_byte_buf_ignore_case_harness_~#buf~3#1.base_BEFORE_CALL_12|)) (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_64f048ab_c29c5984_Treesizes_19_19() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_addflt_~ma~0#1", "ULTIMATE.start_addflt_~mb~0#1"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_addflt_~b#1_45| (_ BitVec 32)) (|v_ULTIMATE.start_addflt_~delta~0#1_28| (_ BitVec 32))) (= |ULTIMATE.start_addflt_~mb~0#1| (bvlshr (bvor (bvand (_ bv16777215 32) |v_ULTIMATE.start_addflt_~b#1_45|) (_ bv16777216 32)) |v_ULTIMATE.start_addflt_~delta~0#1_28|))) (exists ((|ULTIMATE.start_addflt_~a#1| (_ BitVec 32))) (= |ULTIMATE.start_addflt_~ma~0#1| (bvor (_ bv16777216 32) (bvand (_ bv16777215 32) |ULTIMATE.start_addflt_~a#1|)))))";
		final String expectedResultAsString = "(and (exists ((|v_ULTIMATE.start_addflt_~b#1_45| (_ BitVec 32)) (|v_ULTIMATE.start_addflt_~delta~0#1_26| (_ BitVec 32))) (= |ULTIMATE.start_addflt_~mb~0#1| (bvlshr (bvor (bvand (_ bv16777215 32) |v_ULTIMATE.start_addflt_~b#1_45|) (_ bv16777216 32)) |v_ULTIMATE.start_addflt_~delta~0#1_26|))) (exists ((|ULTIMATE.start_addflt_~a#1| (_ BitVec 32))) (= |ULTIMATE.start_addflt_~ma~0#1| (bvor (_ bv16777216 32) (bvand (_ bv16777215 32) |ULTIMATE.start_addflt_~a#1|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6544ca01_cddb8313_Treesizes_66_66() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_9_Pointer~0.base", "~WrapperStruct00_var_1_10_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_138 (_ BitVec 32))) (or (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_138) ~WrapperStruct00_var_1_8_Pointer~0.base)))) (= (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_138) ~WrapperStruct00_var_1_8_Pointer~0.base)))))) (forall ((v_ArrVal_138 (_ BitVec 32))) (or (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_138) ~WrapperStruct00_var_1_8_Pointer~0.base)))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_138) ~WrapperStruct00_var_1_9_Pointer~0.base))))) (forall ((v_ArrVal_138 (_ BitVec 32))) (or (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_138) ~WrapperStruct00_var_1_9_Pointer~0.base)))) (= (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_138) ~WrapperStruct00_var_1_8_Pointer~0.base)))))))";
		final String expectedResultAsString = "(and (forall ((v_ArrVal_116 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116))) (or (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_8_Pointer~0.base)))) (= ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_9_Pointer~0.base)) (_ bv0 8))))) (forall ((v_ArrVal_116 (_ BitVec 32))) (let ((.cse1 (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116))) (or (= (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (select .cse1 ~WrapperStruct00_var_1_8_Pointer~0.base)))) (not (= ((_ extract 7 0) (select .cse1 ~WrapperStruct00_var_1_9_Pointer~0.base)) (_ bv0 8)))))) (forall ((v_ArrVal_116 (_ BitVec 32))) (let ((.cse2 ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_8_Pointer~0.base))))) (or (= (_ bv1 32) .cse2) (= (_ bv0 32) .cse2)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_65b8f395_85286655_Treesizes_66_30() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_15_Pointer~0.base", "~WrapperStruct00_var_1_14_Pointer~0.base", "~WrapperStruct00_var_1_6_Pointer~0.base", "~WrapperStruct00_var_1_13_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_97 (_ BitVec 32)) (v_ArrVal_98 (_ BitVec 32)) (v_ArrVal_96 (_ BitVec 32)) (v_ArrVal_100 (_ BitVec 32))) (= ((_ zero_extend 16) ((_ extract 15 0) (select (store (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_96) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_98) ~WrapperStruct00_var_1_15_Pointer~0.base v_ArrVal_97) ~WrapperStruct00_var_1_6_Pointer~0.base ((_ zero_extend 16) ((_ extract 15 0) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_96) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_98) ~WrapperStruct00_var_1_15_Pointer~0.base v_ArrVal_97) ~WrapperStruct00_var_1_4_Pointer~0.base)))) ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_100) ~WrapperStruct00_var_1_4_Pointer~0.base))) (select (store (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_96) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_98) ~WrapperStruct00_var_1_15_Pointer~0.base v_ArrVal_97) ~WrapperStruct00_var_1_6_Pointer~0.base ((_ zero_extend 16) ((_ extract 15 0) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_96) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_98) ~WrapperStruct00_var_1_15_Pointer~0.base v_ArrVal_97) ~WrapperStruct00_var_1_4_Pointer~0.base)))) ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_100) ~WrapperStruct00_var_1_6_Pointer~0.base)))";
		final String expectedResultAsString = "(forall ((v_ArrVal_100 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| ~WrapperStruct00_var_1_4_Pointer~0.base)))) ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_100))) (= (select .cse0 ~WrapperStruct00_var_1_6_Pointer~0.base) ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 ~WrapperStruct00_var_1_4_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_66cd4369_2cac510a_Treesizes_6_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_6| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_6|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_5|) (_ bv10 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_66f4f84_10a079b5_Treesizes_13_4() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_7~0"),
		};
		final String formulaAsString = "(forall ((~var_1_12~0 (_ BitVec 8))) (or (not (bvsge ((_ zero_extend 24) ~var_1_12~0) (_ bv127 32))) (not (bvsgt ((_ zero_extend 24) ~var_1_7~0) ((_ zero_extend 24) ~var_1_12~0)))))";
		final String expectedResultAsString = "(bvsle ((_ zero_extend 24) ~var_1_7~0) (_ bv127 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_67b5cee7_ad5dd1c5_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_property_#t~mem87#1", "ULTIMATE.start_property_#t~mem86#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_49 (_ BitVec 32)) (v_arrayElimCell_50 (_ BitVec 32))) (and (= ((_ extract 15 0) v_arrayElimCell_50) |ULTIMATE.start_property_#t~mem87#1|) (not (bvsgt ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_49)) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_50)))) (= |ULTIMATE.start_property_#t~mem86#1| ((_ extract 15 0) v_arrayElimCell_49))))";
		final String expectedResultAsString = "(exists ((v_arrayElimCell_42 (_ BitVec 32)) (v_arrayElimCell_41 (_ BitVec 32))) (let ((.cse0 ((_ extract 15 0) v_arrayElimCell_41)) (.cse1 ((_ extract 15 0) v_arrayElimCell_42))) (and (= |ULTIMATE.start_property_#t~mem86#1| .cse0) (not (bvsgt ((_ sign_extend 16) .cse0) ((_ sign_extend 16) .cse1))) (= |ULTIMATE.start_property_#t~mem87#1| .cse1))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_68525fa4_3e09d7d8_Treesizes_49_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_pop_back_~list#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (not (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|) (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|))) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv70 32)) (bvugt (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|) |#StackHeapBarrier|))) (exists ((|v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_28| (_ BitVec 32))) (and (not (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_28|) (bvadd |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_28| (_ bv8 32)))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_28| (_ bv16 32)) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv70 32)))) (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_pop_back_~list#1.base_BEFORE_CALL_28| (_ bv16 32)) (_ bv2147483647 32)))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|))) (and (not (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|) (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_pop_back_~list#1.base|))) (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv70 32)) (bvugt .cse0 |#StackHeapBarrier|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_689449f6_efc80f02_Treesizes_12_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "ULTIMATE.start_main_~r~0#1"),
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~y~0#1| (_ BitVec 32))) (and (bvsle |ULTIMATE.start_main_~y~0#1| (_ bv5 32)) (bvsge |ULTIMATE.start_main_~r~0#1| ((_ sign_extend 32) |ULTIMATE.start_main_~y~0#1|)) (bvsge |ULTIMATE.start_main_~y~0#1| (_ bv0 32))))";
		final String expectedResultAsString = "(bvsge |ULTIMATE.start_main_~r~0#1| (_ bv0 64))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_69333bfb_51eba749_Treesizes_13_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "save_byte_from_array_#in~size#1", "save_byte_from_array_#in~array#1.base", "save_byte_from_array_#in~storage#1.base"),
		};
		final String formulaAsString = "(or (not (bvugt |save_byte_from_array_#in~storage#1.base| (_ bv0 32))) (not (bvugt |save_byte_from_array_#in~size#1| (_ bv0 32))) (not (bvugt |save_byte_from_array_#in~array#1.base| (_ bv0 32))))";
		final String expectedResultAsString = "(or (= (_ bv0 32) |save_byte_from_array_#in~storage#1.base|) (not (bvugt |save_byte_from_array_#in~size#1| (_ bv0 32))) (= (_ bv0 32) |save_byte_from_array_#in~array#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_69c2c3a7_85f2f796_Treesizes_9_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_12~0", "~var_1_20~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_12~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_20~0) (_ bv0 32)))";
		final String expectedResultAsString = "(and (= (_ bv0 8) ~var_1_20~0) (= (_ bv0 8) ~var_1_12~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6a25698c_249f2120_Treesizes_68_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#res", "sum_#in~m"),
		};
		final String formulaAsString = "(and (not (bvsle (bvadd |sum_#in~n| (_ bv4294967294 32)) (_ bv0 32))) (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (forall ((|v_sum_#in~n_BEFORE_CALL_53| (_ BitVec 32))) (or (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_53| (_ bv4294967293 32)) (_ bv0 32)) (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_53| (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967292 32) (bvmul |sum_#in~n| (_ bv4294967295 32))) (_ bv0 32)) (not (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_53| (_ bv4294967292 32)) (_ bv0 32))))) (forall ((|v_sum_#in~n_BEFORE_CALL_53| (_ BitVec 32))) (or (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_53| (_ bv4294967293 32)) (_ bv0 32)) (not (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_53| (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967293 32) (bvmul |sum_#in~n| (_ bv4294967295 32))) (_ bv0 32))) (not (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_53| (_ bv4294967292 32)) (_ bv0 32))))) (bvsle (bvadd |sum_#in~n| (_ bv4294967293 32)) (_ bv0 32)))";
		final String expectedResultAsString = "(let ((.cse0 (bvmul |sum_#in~m| (_ bv4294967295 32)))) (and (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (not (bvsle (bvadd .cse0 |sum_#res| (_ bv4294967294 32)) (_ bv0 32))) (bvsle (bvadd .cse0 |sum_#res| (_ bv4294967293 32)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6a5b7aaa_7236b6f3_Treesizes_59_30() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (= (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv67 32)))) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|) (_ bv2147483647 32)) (exists ((|v_#StackHeapBarrier_3| (_ BitVec 32)) (|v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|) |v_#StackHeapBarrier_3|) (= (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|)) (= (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|)) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|) (bvugt |v_#StackHeapBarrier_3| (_ bv67 32)) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_36|) (_ bv2147483647 32)))) (= (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|)) |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|))) (and (= (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv67 32)))) (bvult .cse0 (_ bv2147483647 32)) (= (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|)) |ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6aa3c928_f866294f_Treesizes_6_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_~cursor#1.base_BEFORE_CALL_4| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_~cursor#1.base_BEFORE_CALL_4|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~0#1.base_BEFORE_CALL_14| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~0#1.base_BEFORE_CALL_14|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6b381c21_f9e73efe_Treesizes_26_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base", "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var3_Pointer~0.base", "~#unsigned_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_166 (_ BitVec 32))) (not (bvslt (bvadd (bvneg ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| (bvadd (_ bv2 32) |~#unsigned_char_Array_0~0.base|) v_ArrVal_166) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var3_Pointer~0.base)))) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| (bvadd (_ bv2 32) |~#unsigned_char_Array_0~0.base|) v_ArrVal_166) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base)))) (_ bv0 32))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_143 (_ BitVec 32))) (not (bvslt (let ((.cse0 (store |#memory_int| (bvadd (_ bv2 32) |~#unsigned_char_Array_0~0.base|) v_ArrVal_143))) (bvadd (bvneg ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var3_Pointer~0.base)))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base))))) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6bb7254e_4461eed4_Treesizes_31_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~var34~0#1", "ULTIMATE.start_main_~var45~0#1", "ULTIMATE.start_main_~var67~0#1"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 32) |ULTIMATE.start_main_~var67~0#1|)) (bvsle |ULTIMATE.start_main_~var45~0#1| (_ bv1 32)) (not (= |ULTIMATE.start_main_~var45~0#1| (_ bv0 32))) (bvsle |ULTIMATE.start_main_~var67~0#1| (_ bv1 32)) (bvsge |ULTIMATE.start_main_~var67~0#1| (_ bv0 32)) (not (= |ULTIMATE.start_main_~var34~0#1| (_ bv0 32))) (bvsge |ULTIMATE.start_main_~var45~0#1| (_ bv0 32)) (bvsle |ULTIMATE.start_main_~var34~0#1| (_ bv1 32)) (bvsge |ULTIMATE.start_main_~var34~0#1| (_ bv0 32)))";
		final String expectedResultAsString = "(and (= (_ bv1 32) |ULTIMATE.start_main_~var67~0#1|) (= |ULTIMATE.start_main_~var34~0#1| (_ bv1 32)) (= |ULTIMATE.start_main_~var45~0#1| (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6c3b464e_b0c0f5cf_Treesizes_21_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_38| (_ BitVec 32))) (or (not (= (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_38|) (bvmul |mult_#in~n| (_ bv4 32)))) (= (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_38|) (bvadd |mult_#in~n| |mult_#res|)))) (= |mult_#in~m| (_ bv3 32)))";
		final String expectedResultAsString = "(and (= |mult_#res| (bvmul |mult_#in~n| (_ bv3 32))) (= |mult_#in~m| (_ bv3 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6cdc330b_5a269785_Treesizes_34_34() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#StackHeapBarrier", "#HeapAllocations", "old(#HeapAllocations)"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9| (_ BitVec 32))) (and (bvult (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9|) (_ bv2147483647 32)) (bvugt (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9|) |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9| |#StackHeapBarrier|))) (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_12| (_ BitVec 32))) (and (bvugt (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_12|) |#StackHeapBarrier|) (bvult (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_12|) (_ bv2147483647 32)) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_12| |#StackHeapBarrier|))) (= |old(#HeapAllocations)| |#HeapAllocations|))";
		final String expectedResultAsString = "(and (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9|))) (and (bvult .cse0 (_ bv2147483647 32)) (bvugt .cse0 |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_9| |#StackHeapBarrier|)))) (= |old(#HeapAllocations)| |#HeapAllocations|) (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_10| (_ BitVec 32))) (let ((.cse1 (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_10|))) (and (bvugt .cse1 |#StackHeapBarrier|) (bvult .cse1 (_ bv2147483647 32)) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_10| |#StackHeapBarrier|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6d60083b_c0b65d_Treesizes_17_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#signed_long_int_Array_0~0.base", "~#BOOL_unsigned_char_Array_0~0.base", "~#signed_short_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_103 (_ BitVec 32)) (v_ArrVal_130 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store (store |#memory_int| (bvadd (_ bv4 32) |~#signed_short_int_Array_0~0.base|) v_ArrVal_130) |~#signed_long_int_Array_0~0.base| v_ArrVal_103) (bvadd (_ bv1 32) |~#BOOL_unsigned_char_Array_0~0.base|)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_103 (_ BitVec 32)) (v_ArrVal_102 (_ BitVec 32))) (= ((_ extract 7 0) (select (store (store |#memory_int| (bvadd (_ bv4 32) |~#signed_short_int_Array_0~0.base|) v_ArrVal_102) |~#signed_long_int_Array_0~0.base| v_ArrVal_103) (bvadd (_ bv1 32) |~#BOOL_unsigned_char_Array_0~0.base|))) (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6e432977_7bd47a7f_Treesizes_26_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#StackHeapBarrier", "#HeapAllocations", "old(#HeapAllocations)"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_create_sll_~#list~0#1.base_BEFORE_CALL_5| (_ BitVec 32))) (and (bvugt (bvadd (_ bv4294967288 32) |v_ULTIMATE.start_create_sll_~#list~0#1.base_BEFORE_CALL_5|) |#StackHeapBarrier|) (bvult (bvadd (_ bv4294967292 32) |v_ULTIMATE.start_create_sll_~#list~0#1.base_BEFORE_CALL_5|) (_ bv2147483647 32)) (bvugt (bvadd (_ bv4294967292 32) |v_ULTIMATE.start_create_sll_~#list~0#1.base_BEFORE_CALL_5|) |#StackHeapBarrier|) (bvult (bvadd (_ bv4 32) |v_ULTIMATE.start_create_sll_~#list~0#1.base_BEFORE_CALL_5|) (_ bv2147483647 32)))) (= |old(#HeapAllocations)| |#HeapAllocations|))";
		final String expectedResultAsString = "(and (exists ((|v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv12 32) |v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2|))) (and (bvugt (bvadd (_ bv8 32) |v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2|) |#StackHeapBarrier|) (bvugt .cse0 |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2| |#StackHeapBarrier|) (bvult .cse0 (_ bv2147483647 32))))) (= |old(#HeapAllocations)| |#HeapAllocations|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6ed0bd17_6669761_Treesizes_59_49() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_byte_cursor_right_trim_pred_~source.base", "#StackAllocations"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd |#StackAllocations| (_ bv4294967283 32)) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8690 32)))) (bvult |#StackAllocations| (_ bv2147483647 32)) (bvult (bvadd (_ bv8 32) aws_byte_cursor_right_trim_pred_~source.base) (_ bv2147483647 32)) (exists ((|v_#StackHeapBarrier_6| (_ BitVec 32))) (and (bvugt |v_#StackHeapBarrier_6| (_ bv8690 32)) (bvugt (bvadd (_ bv8 32) aws_byte_cursor_right_trim_pred_~source.base) |v_#StackHeapBarrier_6|))) (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd |#StackAllocations| (_ bv4294967278 32))) (select |#memory_int| (bvadd |#StackAllocations| (_ bv4294967277 32)))) (select |#memory_int| (bvadd |#StackAllocations| (_ bv4294967276 32)))) (select |#memory_int| (bvadd |#StackAllocations| (_ bv4294967275 32))))) (= |#StackAllocations| (bvadd (_ bv21 32) aws_byte_cursor_right_trim_pred_~source.base)))";
		final String expectedResultAsString = "(let ((.cse1 (bvadd (_ bv8 32) aws_byte_cursor_right_trim_pred_~source.base)) (.cse0 (bvadd (_ bv21 32) aws_byte_cursor_right_trim_pred_~source.base))) (and (bvult .cse0 (_ bv2147483647 32)) (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) aws_byte_cursor_right_trim_pred_~source.base)) (select |#memory_int| (bvadd (_ bv2 32) aws_byte_cursor_right_trim_pred_~source.base))) (select |#memory_int| (bvadd (_ bv1 32) aws_byte_cursor_right_trim_pred_~source.base))) (select |#memory_int| aws_byte_cursor_right_trim_pred_~source.base))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse1 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8690 32)))) (bvult .cse1 (_ bv2147483647 32)) (= |#StackAllocations| .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6f10596d_6af71d03_Treesizes_21_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#Ultimate.C_memset_#ptr.base", "#Ultimate.C_memset_#amount", "#Ultimate.C_memset_#value"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd (_ bv1 32) |#Ultimate.C_memset_#ptr.base|))) (exists ((|v_#Ultimate.C_memset_#t~loopctr676_89| (_ BitVec 32))) (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd |#Ultimate.C_memset_#ptr.base| |v_#Ultimate.C_memset_#t~loopctr676_89|)))) (bvult (_ bv1 32) |#Ultimate.C_memset_#amount|))";
		final String expectedResultAsString = "(and (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd (_ bv1 32) |#Ultimate.C_memset_#ptr.base|))) (bvult (_ bv1 32) |#Ultimate.C_memset_#amount|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6f10596d_e98d75ac_Treesizes_21_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#Ultimate.C_memset_#ptr.base", "#Ultimate.C_memset_#amount", "#Ultimate.C_memset_#value"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd (_ bv1 32) |#Ultimate.C_memset_#ptr.base|))) (exists ((|v_#Ultimate.C_memset_#t~loopctr672_73| (_ BitVec 32))) (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd |#Ultimate.C_memset_#ptr.base| |v_#Ultimate.C_memset_#t~loopctr672_73|)))) (bvult (_ bv1 32) |#Ultimate.C_memset_#amount|))";
		final String expectedResultAsString = "(and (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd (_ bv1 32) |#Ultimate.C_memset_#ptr.base|))) (bvult (_ bv1 32) |#Ultimate.C_memset_#amount|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_6fde3941_75233b79_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "ULTIMATE.start_main_~a~0#1", "ULTIMATE.start_main_~b~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~y~0#1| (_ BitVec 32))) (= (bvmul |ULTIMATE.start_main_~a~0#1| ((_ sign_extend 32) |ULTIMATE.start_main_~y~0#1|)) |ULTIMATE.start_main_~b~0#1|))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_main_~a~0#1| (_ bv0 64)) (= |ULTIMATE.start_main_~b~0#1| (_ bv0 64)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_70dc6c5b_cbdbd821_Treesizes_446_443() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~seq_2_start_8~0", "~seq_1_start_1~0", "~score_6~0", "~seq_1_start_7~0", "~result_11~0", "~seq_2_start_2~0", "~score_0~0", "~result_9~0"),
		};
		final String formulaAsString = "(or (and (or (and (= (_ bv0 32) (bvadd (_ bv1 32) ~result_11~0)) (bvslt (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0) (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0)) (bvsle ~score_6~0 ~score_0~0)) (and (bvslt (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0) (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0)) (or (and (= (_ bv0 32) (bvadd (_ bv1 32) ~result_11~0)) (bvslt ~score_6~0 ~score_0~0)) (and (= (_ bv1 32) ~result_11~0) (bvsle ~score_0~0 ~score_6~0)))) (and (bvsle (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0) (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0)) (or (and (= (_ bv0 32) ~result_11~0) (bvsle ~score_6~0 ~score_0~0) (bvsle ~score_0~0 ~score_6~0)) (and (= (_ bv0 32) (bvadd (_ bv1 32) ~result_11~0)) (bvslt ~score_6~0 ~score_0~0))) (bvsle (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0) (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0))) (and (bvslt ~score_0~0 ~score_6~0) (= (_ bv1 32) ~result_11~0))) (= ~result_9~0 (_ bv0 32))) (and (bvslt (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0) (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0)) (= (bvadd ~result_9~0 (_ bv1 32)) (_ bv0 32)) (= (_ bv1 32) ~result_11~0) (bvslt ~score_6~0 ~score_0~0)) (and (= (bvadd ~result_9~0 (_ bv1 32)) (_ bv0 32)) (not (= (_ bv2147483647 32) (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0))) (not (= (_ bv2147483647 32) (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0))) (or (= (_ bv1 32) ~result_11~0) (and (= (_ bv0 32) (bvadd (_ bv1 32) ~result_11~0)) (bvslt ~score_6~0 ~score_0~0)))) (and (= (_ bv0 32) (bvadd (_ bv1 32) ~result_11~0)) (= (bvadd ~result_9~0 (_ bv1 32)) (_ bv0 32)) (exists ((|thread1Thread1of1ForFork0_~s2~0#1| (_ BitVec 32))) (and (bvslt |thread1Thread1of1ForFork0_~s2~0#1| (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0)) (bvslt (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0) |thread1Thread1of1ForFork0_~s2~0#1|))) (bvsle ~score_6~0 ~score_0~0)) (and (= (bvadd ~result_9~0 (_ bv1 32)) (_ bv0 32)) (or (and (= (_ bv0 32) ~result_11~0) (bvslt ~score_6~0 ~score_0~0)) (and (= (_ bv0 32) (bvadd (_ bv1 32) ~result_11~0)) (exists ((~score_3~0 (_ BitVec 32))) (and (bvsgt ~score_0~0 ~score_3~0) (bvsgt ~score_3~0 ~score_6~0)))))) (and (= (_ bv0 32) (bvadd (_ bv1 32) ~result_11~0)) (= (bvadd ~result_9~0 (_ bv1 32)) (_ bv0 32)) (bvslt ~score_6~0 ~score_0~0) (not (= (_ bv0 32) (bvadd ~seq_1_start_7~0 (_ bv2147483648 32) ~seq_2_start_8~0)))) (and (= (bvadd ~result_9~0 (_ bv1 32)) (_ bv0 32)) (= (_ bv0 32) ~result_11~0) (bvslt (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0) (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0)) (bvsle ~score_6~0 ~score_0~0)) (and (= (bvadd ~result_9~0 (_ bv1 32)) (_ bv0 32)) (not (= ~score_0~0 (_ bv2147483648 32))) (= (_ bv1 32) ~result_11~0) (not (= (_ bv0 32) (bvadd ~score_6~0 (_ bv2147483648 32))))) (and (or (and (bvslt (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0) (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0)) (or (and (= (_ bv0 32) (bvadd (_ bv1 32) ~result_11~0)) (not (= (_ bv2147483647 32) ~score_6~0))) (and (= (_ bv0 32) ~result_11~0) (bvsle ~score_0~0 ~score_6~0)))) (and (= (_ bv0 32) (bvadd (_ bv1 32) ~result_11~0)) (not (= (_ bv0 32) (bvadd ~seq_1_start_7~0 (_ bv2147483648 32) ~seq_2_start_8~0))) (not (= (_ bv0 32) (bvadd ~seq_1_start_1~0 (_ bv2147483648 32) ~seq_2_start_2~0))))) (= ~result_9~0 (_ bv1 32))) (and (or (and (bvslt ~score_0~0 ~score_6~0) (not (= (_ bv2147483647 32) (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0))) (= (_ bv1 32) ~result_11~0)) (and (bvslt ~score_0~0 ~score_6~0) (= (_ bv0 32) ~result_11~0))) (= ~result_9~0 (_ bv1 32))) (and (bvslt ~score_0~0 ~score_6~0) (= (bvadd ~result_9~0 (_ bv1 32)) (_ bv0 32)) (not (= (_ bv2147483647 32) (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0))) (= (_ bv1 32) ~result_11~0)) (and (= ~result_9~0 (_ bv1 32)) (or (and (= (_ bv1 32) ~result_11~0) (exists ((~score_3~0 (_ BitVec 32))) (and (bvslt ~score_3~0 ~score_6~0) (bvslt ~score_0~0 ~score_3~0)))) (and (or (and (= (_ bv1 32) ~result_11~0) (exists ((~score_3~0 (_ BitVec 32))) (and (bvslt ~score_3~0 ~score_6~0) (bvslt ~score_0~0 ~score_3~0)))) (and (= (_ bv0 32) (bvadd (_ bv1 32) ~result_11~0)) (not (= (_ bv2147483647 32) ~score_0~0)))) (bvslt (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0) (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0))) (and (= (_ bv0 32) (bvadd (_ bv1 32) ~result_11~0)) (not (= (_ bv2147483647 32) ~score_0~0)) (not (= (_ bv2147483647 32) ~score_6~0))))) (and (or (and (= (_ bv1 32) ~result_11~0) (exists ((|thread1Thread1of1ForFork0_~s2~0#1| (_ BitVec 32))) (and (bvsgt (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0) |thread1Thread1of1ForFork0_~s2~0#1|) (bvsgt |thread1Thread1of1ForFork0_~s2~0#1| (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0)))) (bvsle ~score_0~0 ~score_6~0)) (and (bvslt ~score_0~0 ~score_6~0) (= (_ bv1 32) ~result_11~0) (not (= (_ bv0 32) (bvadd ~seq_1_start_1~0 (_ bv2147483648 32) ~seq_2_start_2~0))))) (= ~result_9~0 (_ bv1 32))))";
		final String expectedResultAsString = "(let ((.cse8 (bvadd ~seq_1_start_1~0 ~seq_2_start_2~0)) (.cse7 (bvadd ~seq_1_start_7~0 ~seq_2_start_8~0)) (.cse0 (= (_ bv0 32) (bvadd (_ bv1 32) ~result_11~0))) (.cse12 (bvslt ~score_6~0 ~score_0~0))) (let ((.cse4 (and .cse0 .cse12)) (.cse2 (bvsle ~score_6~0 ~score_0~0)) (.cse14 (not (= (_ bv2147483647 32) .cse7))) (.cse13 (not (= (_ bv2147483647 32) .cse8))) (.cse1 (bvslt .cse8 .cse7)) (.cse11 (= (bvadd ~result_9~0 (_ bv1 32)) (_ bv0 32))) (.cse10 (bvslt ~score_0~0 ~score_6~0)) (.cse5 (= (_ bv1 32) ~result_11~0)) (.cse3 (bvslt .cse7 .cse8)) (.cse19 (not (= (_ bv2147483647 32) ~score_6~0))) (.cse9 (= (_ bv0 32) ~result_11~0)) (.cse6 (bvsle ~score_0~0 ~score_6~0)) (.cse15 (not (= (_ bv0 32) (bvadd ~seq_1_start_7~0 (_ bv2147483648 32) ~seq_2_start_8~0)))) (.cse16 (= ~result_9~0 (_ bv1 32)))) (or (and (or (and .cse0 .cse1 .cse2) (and .cse3 (or .cse4 (and .cse5 .cse6))) (and (bvsle .cse7 .cse8) (or (and .cse9 .cse2 .cse6) .cse4) (bvsle .cse8 .cse7)) (and .cse10 .cse5)) (= ~result_9~0 (_ bv0 32))) (and .cse3 .cse11 .cse5 .cse12) (and .cse11 .cse13 .cse14 (or .cse5 .cse4)) (and .cse0 .cse11 (exists ((|thread1Thread1of1ForFork0_~s2~0#1| (_ BitVec 32))) (and (bvslt |thread1Thread1of1ForFork0_~s2~0#1| .cse7) (bvslt .cse8 |thread1Thread1of1ForFork0_~s2~0#1|))) .cse2) (and .cse11 (or (and .cse9 .cse12) (and .cse0 (exists ((~score_3~0 (_ BitVec 32))) (and (bvsgt ~score_0~0 ~score_3~0) (bvsgt ~score_3~0 ~score_6~0)))))) (and .cse0 .cse11 .cse12 .cse15) (and .cse11 .cse9 .cse1 .cse2) (and (or (and .cse10 .cse14 .cse5) (and .cse10 .cse9)) .cse16) (and .cse10 .cse11 .cse13 .cse5) (and .cse16 (let ((.cse17 (and .cse5 (exists ((~score_3~0 (_ BitVec 32))) (and (bvslt ~score_3~0 ~score_6~0) (bvslt ~score_0~0 ~score_3~0))))) (.cse18 (not (= (_ bv2147483647 32) ~score_0~0)))) (or .cse17 (and (or .cse17 (and .cse0 .cse18)) .cse1) (and .cse0 .cse18 .cse19)))) (and (not (= ~score_6~0 (_ bv2147483648 32))) .cse11 (not (= ~score_0~0 (_ bv2147483648 32))) .cse5) (and (or (and .cse5 (exists ((|thread1Thread1of1ForFork0_~s2~0#1| (_ BitVec 32))) (and (bvsgt .cse8 |thread1Thread1of1ForFork0_~s2~0#1|) (bvsgt |thread1Thread1of1ForFork0_~s2~0#1| .cse7))) .cse6) (and .cse10 .cse5 (not (= (_ bv0 32) (bvadd ~seq_1_start_1~0 (_ bv2147483648 32) ~seq_2_start_2~0))))) .cse16) (and (or (and .cse3 (or (and .cse0 .cse19) (and .cse9 .cse6))) (and .cse0 .cse15 (not (= .cse8 (_ bv2147483648 32))))) .cse16))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_713152ca_82dd7201_Treesizes_16_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "~ARR_SIZE~0"),
		};
		final String formulaAsString = "(and (bvslt ((_ sign_extend 32) (_ bv1 32)) ~ARR_SIZE~0) (exists ((|v_ULTIMATE.start_main_#t~nondet4#1_17| (_ BitVec 16))) (= ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet4#1_17|) ~ARR_SIZE~0)) (exists ((|v_ULTIMATE.start_main_~count~0#1_39| (_ BitVec 32))) (not (bvslt ((_ sign_extend 32) |v_ULTIMATE.start_main_~count~0#1_39|) ~ARR_SIZE~0))))";
		final String expectedResultAsString = "(and (bvslt ((_ sign_extend 32) (_ bv1 32)) ~ARR_SIZE~0) (exists ((|v_ULTIMATE.start_main_#t~nondet4#1_17| (_ BitVec 16))) (= ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet4#1_17|) ~ARR_SIZE~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_71ef8272_699eff50_Treesizes_19_19() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_3| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_3|) (_ bv8692 32)) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_3|) (_ bv2147483647 32)) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_3|)) (_ bv0 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_2| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_2|))) (and (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_buf_eq_c_str_ignore_case_~buf#1.base_BEFORE_CALL_2|)) (_ bv0 32)) (bvugt .cse0 (_ bv8692 32)) (bvult .cse0 (_ bv2147483647 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_729f4317_be6f54f2_Treesizes_23_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#res", "sum_#in~m"),
		};
		final String formulaAsString = "(and (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (not (bvsle (bvadd (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967292 32)) (_ bv0 32))) (bvsle (bvadd (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967291 32)) (_ bv0 32)))";
		final String expectedResultAsString = "(and (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (not (bvsle (bvadd |sum_#in~n| (_ bv4294967292 32)) (_ bv0 32))) (bvsle (bvadd |sum_#in~n| (_ bv4294967291 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_730abdcb_c10684f3_Treesizes_71_71() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~state_671~0#1", "ULTIMATE.start_main_~state_694~0#1", "ULTIMATE.start_main_~mask_SORT_1~0#1"),
		};
		final String formulaAsString = "(and (or (forall ((|v_ULTIMATE.start_main_~var_717_arg_0~0#1_15| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_713_arg_1~0#1_13| (_ BitVec 8))) (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_717_arg_0~0#1_15|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_713_arg_1~0#1_13|))))))))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|))) (_ bv0 8))) (= (_ bv0 8) |ULTIMATE.start_main_~state_694~0#1|)) (or (not (= (_ bv0 8) |ULTIMATE.start_main_~state_694~0#1|)) (forall ((|v_ULTIMATE.start_main_~var_677_arg_1~0#1_13| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_717_arg_0~0#1_15| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_688_arg_1~0#1_13| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_674_arg_1~0#1_13| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_692_arg_1~0#1_13| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_717_arg_0~0#1_15|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvor ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_688_arg_1~0#1_13|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_674_arg_1~0#1_13|) ((_ zero_extend 24) |ULTIMATE.start_main_~state_671~0#1|)))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_677_arg_1~0#1_13|)))))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_692_arg_1~0#1_13|)))))))))))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|)))))))";
		final String expectedResultAsString = "(let ((.cse1 ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|)) (.cse0 (= (_ bv0 8) |ULTIMATE.start_main_~state_694~0#1|))) (and (or (not .cse0) (forall ((|v_ULTIMATE.start_main_~var_677_arg_1~0#1_10| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_717_arg_0~0#1_12| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_692_arg_1~0#1_10| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_674_arg_1~0#1_10| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_688_arg_1~0#1_10| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_717_arg_0~0#1_12|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvor ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_688_arg_1~0#1_10|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_677_arg_1~0#1_10|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_674_arg_1~0#1_10|) ((_ zero_extend 24) |ULTIMATE.start_main_~state_671~0#1|))))))))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_692_arg_1~0#1_10|)))))))))))) .cse1))))) (or (forall ((|v_ULTIMATE.start_main_~var_717_arg_0~0#1_12| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_713_arg_1~0#1_10| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_713_arg_1~0#1_10|)))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_717_arg_0~0#1_12|)))) .cse1)))) .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_73e69521_716cce67_Treesizes_45_45() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_5 (_ BitVec 32))) (and (bvult (bvadd v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_5 (_ bv21 32)) (_ bv2147483647 32)) (= (concat (concat (concat (select |#memory_int| (bvadd v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_5 (_ bv3 32))) (select |#memory_int| (bvadd v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_5 (_ bv2 32)))) (select |#memory_int| (bvadd v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_5 (_ bv1 32)))) (select |#memory_int| v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_5)) (_ bv0 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8689 32)) (bvugt (bvadd v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_5 (_ bv8 32)) |#StackHeapBarrier|))) (bvult (bvadd v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_5 (_ bv8 32)) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_2 (_ BitVec 32))) (let ((.cse0 (bvadd v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_2 (_ bv8 32)))) (and (bvult (bvadd v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_2 (_ bv21 32)) (_ bv2147483647 32)) (bvult .cse0 (_ bv2147483647 32)) (= (concat (concat (concat (select |#memory_int| (bvadd v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_2 (_ bv3 32))) (select |#memory_int| (bvadd v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_2 (_ bv2 32)))) (select |#memory_int| (bvadd v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_2 (_ bv1 32)))) (select |#memory_int| v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_2)) (_ bv0 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8689 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_74a9f405_6bf0595a_Treesizes_35_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_linked_list_is_valid_#in~list#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (not (= (select |#memory_$Pointer$.base| |aws_linked_list_is_valid_#in~list#1.base|) (bvadd (_ bv8 32) |aws_linked_list_is_valid_#in~list#1.base|))) (exists ((|v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_7| (_ BitVec 32))) (not (= (bvadd (_ bv8 32) |v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_7|) (select |#memory_$Pointer$.base| |v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_7|)))) (exists ((|v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ BitVec 32))) (and (bvult |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ bv2147483647 32)) (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15|) (bvadd |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ bv8 32))) (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ bv16 32)) (_ bv2147483647 32)))))";
		final String expectedResultAsString = "(and (not (= (select |#memory_$Pointer$.base| |aws_linked_list_is_valid_#in~list#1.base|) (bvadd (_ bv8 32) |aws_linked_list_is_valid_#in~list#1.base|))) (exists ((|v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ BitVec 32))) (and (bvult |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ bv2147483647 32)) (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15|) (bvadd |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ bv8 32))) (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ bv16 32)) (_ bv2147483647 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_755e5440_a6784d82_Treesizes_7_5() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(= (bvurem (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv4 32)) (_ bv4 32)) (_ bv0 32))";
		final String expectedResultAsString = "(= (_ bv0 32) (bvurem |ULTIMATE.start_main_~x~0#1| (_ bv4 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_75dd985f_792b65ea_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~bad_19_arg_0~0#1"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~state_3~0#1_9| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_18_arg_0~0#1_25| (_ BitVec 8)) (|ULTIMATE.start_main_~mask_SORT_1~0#1| (_ BitVec 8))) (= |ULTIMATE.start_main_~bad_19_arg_0~0#1| ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_18_arg_0~0#1_25|) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvmul ((_ zero_extend 24) |v_ULTIMATE.start_main_~state_3~0#1_9|) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv2 32) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|))))))))))))))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_main_~state_3~0#1_9| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_18_arg_0~0#1_21| (_ BitVec 8)) (|ULTIMATE.start_main_~mask_SORT_1~0#1| (_ BitVec 8))) (= |ULTIMATE.start_main_~bad_19_arg_0~0#1| ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_18_arg_0~0#1_21|) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvmul ((_ zero_extend 24) |v_ULTIMATE.start_main_~state_3~0#1_9|) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv2 32) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|))))))))))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_76a2a87c_7412d41e_Treesizes_9_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv74 32) |~#WrapperStruct00~0.base|))) (_ bv0 8)))";
		final String expectedResultAsString = "(bvsge ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv74 32) |~#WrapperStruct00~0.base|)))) (_ bv1 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7700e7b8_ac521173_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_14| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base_BEFORE_CALL_14|)))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base|))))";
		final String expectedResultAsString = "(= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |ULTIMATE.start_aws_byte_buf_from_c_str_~#buf~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_77c91d9_c65064f4_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_back_~list.base_BEFORE_CALL_8 (_ BitVec 32))) (and (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) v_aws_linked_list_back_~list.base_BEFORE_CALL_8) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv66 32)))) (= (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) v_aws_linked_list_back_~list.base_BEFORE_CALL_8)) (_ bv0 32)) (bvult (bvadd (_ bv16 32) v_aws_linked_list_back_~list.base_BEFORE_CALL_8) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((v_aws_linked_list_back_~list.base_BEFORE_CALL_7 (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) v_aws_linked_list_back_~list.base_BEFORE_CALL_7))) (and (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) v_aws_linked_list_back_~list.base_BEFORE_CALL_7))) (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv66 32)) (bvugt .cse0 |#StackHeapBarrier|))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_78a14f1b_e8f80a47_Treesizes_14_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base_BEFORE_CALL_16| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base_BEFORE_CALL_16|)))) (not (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base|))))";
		final String expectedResultAsString = "(not (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_79082c95_7112bd2b_Treesizes_38_38() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_6_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base", "~WrapperStruct00_var_1_10_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_178 (_ BitVec 32)) (v_ArrVal_143 (_ BitVec 32))) (= ((_ sign_extend 16) ((_ extract 15 0) (bvadd ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_178) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_143) ~WrapperStruct00_var_1_4_Pointer~0.base))) ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_178) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_143) ~WrapperStruct00_var_1_3_Pointer~0.base)))))) ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_178) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_143) ~WrapperStruct00_var_1_1_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_143 (_ BitVec 32)) (v_ArrVal_142 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_142) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_143))) (= ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ sign_extend 16) ((_ extract 15 0) (bvadd ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 ~WrapperStruct00_var_1_3_Pointer~0.base))) ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 ~WrapperStruct00_var_1_4_Pointer~0.base)))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_79a284cf_d7057542_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_24| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_24|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_23| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_23|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7a7402ef_4eeefa41_Treesizes_83_83() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#float_Array_0~0.base", "~#signed_short_int_Array_0~0.base", "~#unsigned_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_106 (_ BitVec 32)) (v_ArrVal_132 (_ BitVec 32))) (not (fp.lt (fp ((_ extract 31 31) (select (store (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_132) (bvadd (_ bv2 32) |~#unsigned_char_Array_0~0.base|) v_ArrVal_106) (bvadd |~#float_Array_0~0.base| (_ bv4 32)))) ((_ extract 30 23) (select (store (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_132) (bvadd (_ bv2 32) |~#unsigned_char_Array_0~0.base|) v_ArrVal_106) (bvadd |~#float_Array_0~0.base| (_ bv4 32)))) ((_ extract 22 0) (select (store (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_132) (bvadd (_ bv2 32) |~#unsigned_char_Array_0~0.base|) v_ArrVal_106) (bvadd |~#float_Array_0~0.base| (_ bv4 32))))) (fp ((_ extract 31 31) (select (store (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_132) (bvadd (_ bv2 32) |~#unsigned_char_Array_0~0.base|) v_ArrVal_106) |~#float_Array_0~0.base|)) ((_ extract 30 23) (select (store (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_132) (bvadd (_ bv2 32) |~#unsigned_char_Array_0~0.base|) v_ArrVal_106) |~#float_Array_0~0.base|)) ((_ extract 22 0) (select (store (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_132) (bvadd (_ bv2 32) |~#unsigned_char_Array_0~0.base|) v_ArrVal_106) |~#float_Array_0~0.base|))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_106 (_ BitVec 32)) (v_ArrVal_105 (_ BitVec 32))) (not (let ((.cse1 (store (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_105) (bvadd (_ bv2 32) |~#unsigned_char_Array_0~0.base|) v_ArrVal_106))) (fp.lt (let ((.cse0 (select .cse1 (bvadd |~#float_Array_0~0.base| (_ bv4 32))))) (fp ((_ extract 31 31) .cse0) ((_ extract 30 23) .cse0) ((_ extract 22 0) .cse0))) (let ((.cse2 (select .cse1 |~#float_Array_0~0.base|))) (fp ((_ extract 31 31) .cse2) ((_ extract 30 23) .cse2) ((_ extract 22 0) .cse2)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7b28730_c3a30223_Treesizes_34_34() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4_Pointer~0.base", "~var_1_14_Pointer~0.base", "~var_1_15_Pointer~0.base", "~var_1_13_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_149 (_ BitVec 32)) (v_ArrVal_148 (_ BitVec 32)) (v_ArrVal_124 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (bvadd (_ bv4294967264 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~var_1_13_Pointer~0.base v_ArrVal_148) ~var_1_15_Pointer~0.base v_ArrVal_149) ~var_1_14_Pointer~0.base v_ArrVal_124) ~var_1_4_Pointer~0.base)))))) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~var_1_13_Pointer~0.base v_ArrVal_148) ~var_1_15_Pointer~0.base v_ArrVal_149) ~var_1_14_Pointer~0.base v_ArrVal_124) ~var_1_1_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_124 (_ BitVec 32)) (v_ArrVal_123 (_ BitVec 32)) (v_ArrVal_122 (_ BitVec 32))) (let ((.cse0 (store (store (store |#memory_int| ~var_1_13_Pointer~0.base v_ArrVal_123) ~var_1_15_Pointer~0.base v_ArrVal_122) ~var_1_14_Pointer~0.base v_ArrVal_124))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~var_1_1_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (bvadd (_ bv4294967264 32) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~var_1_4_Pointer~0.base)))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7bab3764_98d4bf56_Treesizes_5_4() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~r_add2~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvadd |ULTIMATE.start_main_~r_add2~0#1| (_ bv1 32)))";
		final String expectedResultAsString = "(not (bvult |ULTIMATE.start_main_~r_add2~0#1| (_ bv4294967295 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7c5a28b3_13d02cae_Treesizes_24_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| (bvadd (_ bv13 32) |~#WrapperStruct00~0.base|)) ((_ sign_extend 24) (_ bv32 8))) (= ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv13 32) |~#WrapperStruct00~0.base|)))) ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv16 32) |~#WrapperStruct00~0.base|))))))";
		final String expectedResultAsString = "(let ((.cse0 ((_ sign_extend 24) (_ bv32 8)))) (and (= ((_ zero_extend 24) ((_ extract 7 0) .cse0)) ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv16 32) |~#WrapperStruct00~0.base|))))) (= (select |#memory_int| (bvadd (_ bv13 32) |~#WrapperStruct00~0.base|)) .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7d85bd57_145675c6_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_15_Pointer~0.base", "~WrapperStruct00_var_1_14_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_181 (_ BitVec 32)) (v_ArrVal_155 (_ BitVec 32)) (v_ArrVal_154 (_ BitVec 32)) (v_ArrVal_153 (_ BitVec 32))) (bvslt ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_181) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_154) ~WrapperStruct00_var_1_15_Pointer~0.base v_ArrVal_153) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_155) ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv1 32)))";
		final String expectedResultAsString = "(forall ((v_ArrVal_155 (_ BitVec 32)) (v_ArrVal_154 (_ BitVec 32)) (v_ArrVal_153 (_ BitVec 32)) (v_ArrVal_152 (_ BitVec 32))) (bvslt ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_152) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_154) ~WrapperStruct00_var_1_15_Pointer~0.base v_ArrVal_153) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_155) ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7e8a1bda_3fa400c9_Treesizes_25_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(or (exists ((v_arrayElimCell_4 (_ BitVec 32))) (and (bvsle v_arrayElimCell_4 (bvadd v_arrayElimCell_4 (_ bv2147483647 32))) (= (bvadd (bvneg v_arrayElimCell_4) v_arrayElimCell_4) ~counter~0))) (exists ((v_arrayElimCell_4 (_ BitVec 32))) (and (bvsge v_arrayElimCell_4 (_ bv0 32)) (= (bvadd (bvneg v_arrayElimCell_4) v_arrayElimCell_4) ~counter~0))))";
		final String expectedResultAsString = "(= (_ bv0 32) ~counter~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7e919719_f908b434_Treesizes_47_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base|) (_ bv2147483647 32)) (exists ((|v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_13| (_ BitVec 32))) (and (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8687 32)) (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_13|) |#StackHeapBarrier|))) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_13|) (_ bv2147483647 32)) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base_BEFORE_CALL_13|)) (_ bv0 32)))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8687 32)) (bvugt (bvadd (_ bv16 32) |ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base|) |#StackHeapBarrier|))) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base|)) (_ bv0 32)))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv16 32) |ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base|))) (and (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8687 32)) (bvugt .cse0 |#StackHeapBarrier|))) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |ULTIMATE.start_aws_byte_buf_clean_up_secure_harness_~#buf~3#1.base|)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7f59c4dc_4c5369dc_Treesizes_15_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~b~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ((_ extract 31 0) (_ bv1 64)) (select |#memory_int| |ULTIMATE.start_main_~b~0#1.base|)) (= (select |#memory_int| (bvadd |ULTIMATE.start_main_~b~0#1.base| (_ bv4 32))) ((_ extract 63 32) (_ bv1 64))))";
		final String expectedResultAsString = "(= (concat (select |#memory_int| (bvadd |ULTIMATE.start_main_~b~0#1.base| (_ bv4 32))) (select |#memory_int| |ULTIMATE.start_main_~b~0#1.base|)) ((_ sign_extend 32) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_7fd5215c_61512217_Treesizes_31_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id2~0", "~id3~0", "~id4~0", "~send2~0"),
		};
		final String formulaAsString = "(or (forall ((~send4~0 (_ BitVec 8))) (not (= ((_ sign_extend 24) ~id4~0) ((_ sign_extend 24) ~send4~0)))) (= ((_ sign_extend 24) ~id2~0) ((_ sign_extend 24) ~id4~0)) (not (bvsgt ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~send2~0))) ((_ sign_extend 24) ~id3~0))) (not (= ((_ sign_extend 24) ~id4~0) ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~send2~0))))))))";
		final String expectedResultAsString = "(let ((.cse0 ((_ sign_extend 24) ~id4~0)) (.cse1 ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~send2~0))))) (or (= ((_ sign_extend 24) ~id2~0) .cse0) (not (bvsgt .cse1 ((_ sign_extend 24) ~id3~0))) (not (= .cse0 ((_ sign_extend 24) ((_ extract 7 0) .cse1))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8048b257_5d7d5fb4_Treesizes_71_71() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~state_109~0#1", "ULTIMATE.start_main_~state_132~0#1", "ULTIMATE.start_main_~mask_SORT_1~0#1"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 8) |ULTIMATE.start_main_~state_132~0#1|)) (forall ((|v_ULTIMATE.start_main_~var_130_arg_1~0#1_13| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_126_arg_1~0#1_13| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_112_arg_1~0#1_13| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_155_arg_0~0#1_15| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_115_arg_1~0#1_13| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvor ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_130_arg_1~0#1_13|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_115_arg_1~0#1_13|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_112_arg_1~0#1_13|) ((_ zero_extend 24) |ULTIMATE.start_main_~state_109~0#1|))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_126_arg_1~0#1_13|))))))))))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_155_arg_0~0#1_15|)))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|)))))) (or (= (_ bv0 8) |ULTIMATE.start_main_~state_132~0#1|) (forall ((|v_ULTIMATE.start_main_~var_151_arg_1~0#1_13| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_155_arg_0~0#1_15| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_151_arg_1~0#1_13|)))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_155_arg_0~0#1_15|)))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|)))))))";
		final String expectedResultAsString = "(let ((.cse0 ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|)) (.cse1 (= (_ bv0 8) |ULTIMATE.start_main_~state_132~0#1|))) (and (or (forall ((|v_ULTIMATE.start_main_~var_130_arg_1~0#1_10| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_126_arg_1~0#1_10| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_112_arg_1~0#1_10| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_115_arg_1~0#1_10| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_155_arg_0~0#1_12| (_ BitVec 8))) (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_155_arg_0~0#1_12|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvor ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_130_arg_1~0#1_10|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_126_arg_1~0#1_10|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |ULTIMATE.start_main_~state_109~0#1|) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_112_arg_1~0#1_10|)))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_115_arg_1~0#1_10|))))))))))))))))))))) .cse0)) (_ bv0 8))) (not .cse1)) (or (forall ((|v_ULTIMATE.start_main_~var_151_arg_1~0#1_10| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_155_arg_0~0#1_12| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_155_arg_0~0#1_12|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_151_arg_1~0#1_10|))))))))) .cse0)))) .cse1)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_80e7b3a5_6c8cae0_Treesizes_48_48() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#StackHeapBarrier", "#HeapAllocations", "node_create_~temp~0#1.base", "old(#HeapAllocations)"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base", "old(#memory_$Pointer$.base)"),
		};
		final String formulaAsString = "(and (= (bvadd |old(#HeapAllocations)| (_ bv8 32)) |#HeapAllocations|) (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7| (_ BitVec 32))) (and (bvult (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7|) (_ bv2147483647 32)) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7| |#StackHeapBarrier|) (bvugt (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7|) |#StackHeapBarrier|))) (= |old(#HeapAllocations)| |node_create_~temp~0#1.base|) (bvult |node_create_~temp~0#1.base| |#StackHeapBarrier|) (= |old(#memory_$Pointer$.base)| |#memory_$Pointer$.base|) (exists ((|v_ULTIMATE.start_sll_append_~head#1.base_BEFORE_CALL_5| (_ BitVec 32))) (and (bvugt (bvadd (_ bv4 32) |v_ULTIMATE.start_sll_append_~head#1.base_BEFORE_CALL_5|) |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_sll_append_~head#1.base_BEFORE_CALL_5| |#StackHeapBarrier|) (bvult (bvadd (_ bv4 32) |v_ULTIMATE.start_sll_append_~head#1.base_BEFORE_CALL_5|) (_ bv2147483647 32)))) (bvult |#HeapAllocations| |#StackHeapBarrier|))";
		final String expectedResultAsString = "(and (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7|))) (and (bvult .cse0 (_ bv2147483647 32)) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7| |#StackHeapBarrier|) (bvugt .cse0 |#StackHeapBarrier|)))) (= |old(#HeapAllocations)| |node_create_~temp~0#1.base|) (bvult |node_create_~temp~0#1.base| |#StackHeapBarrier|) (= |old(#memory_$Pointer$.base)| |#memory_$Pointer$.base|) (= |#HeapAllocations| (bvadd (_ bv8 32) |node_create_~temp~0#1.base|)) (exists ((|v_ULTIMATE.start_sll_append_~head#1.base_BEFORE_CALL_5| (_ BitVec 32))) (let ((.cse1 (bvadd (_ bv4 32) |v_ULTIMATE.start_sll_append_~head#1.base_BEFORE_CALL_5|))) (and (bvugt .cse1 |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_sll_append_~head#1.base_BEFORE_CALL_5| |#StackHeapBarrier|) (bvult .cse1 (_ bv2147483647 32))))) (bvult |#HeapAllocations| |#StackHeapBarrier|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_81c13ad1_e81b6b0e_Treesizes_12_12() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~n~0#1| (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv2 32))) (not (bvugt (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv4294967295 32)) (_ bv0 32))))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_main_~n~0#1| (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv2 32))) (not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967293 32)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8297ea0c_c2542014_Treesizes_86_62() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_6_Pointer~0.base", "~WrapperStruct00_var_1_12_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_5_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (bvsle (select |#memory_int| (_ bv66 32)) (_ bv1073741823 32)) (= (_ bv78 32) ~WrapperStruct00_var_1_12_Pointer~0.base) (bvsge (select |#memory_int| (_ bv66 32)) (_ bv3221225473 32)) (bvsge (select |#memory_int| (_ bv58 32)) (_ bv0 32)) (= (bvadd (select |#memory_int| (_ bv46 32)) (_ bv128 32)) (bvadd (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)) (select |#memory_int| (_ bv58 32)))) (= (_ bv66 32) ~WrapperStruct00_var_1_6_Pointer~0.base) (= (_ bv62 32) ~WrapperStruct00_var_1_5_Pointer~0.base) (= ~WrapperStruct00_var_1_1_Pointer~0.base (_ bv46 32)) (bvsle (bvadd (select |#memory_int| (_ bv46 32)) (_ bv128 32) (bvmul (select |#memory_int| (_ bv58 32)) (_ bv4294967295 32)) (bvmul (select |#memory_int| (_ bv66 32)) (_ bv4294967295 32))) (_ bv536870911 32)) (bvsle (select |#memory_int| (_ bv58 32)) (_ bv536870912 32)) (= (_ bv58 32) ~WrapperStruct00_var_1_4_Pointer~0.base) (bvsge (bvadd (select |#memory_int| (_ bv46 32)) (_ bv128 32) (bvmul (select |#memory_int| (_ bv58 32)) (_ bv4294967295 32)) (bvmul (select |#memory_int| (_ bv66 32)) (_ bv4294967295 32))) (_ bv3758096385 32)))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (_ bv66 32))) (.cse2 (select |#memory_int| (_ bv62 32))) (.cse1 (select |#memory_int| (_ bv58 32)))) (and (bvsle .cse0 (_ bv1073741823 32)) (= (_ bv78 32) ~WrapperStruct00_var_1_12_Pointer~0.base) (bvsge .cse0 (_ bv3221225473 32)) (bvsge .cse1 (_ bv0 32)) (bvsge .cse2 (_ bv3758096385 32)) (= (bvadd (select |#memory_int| (_ bv46 32)) (_ bv128 32)) (bvadd .cse0 .cse2 .cse1)) (= (_ bv66 32) ~WrapperStruct00_var_1_6_Pointer~0.base) (= (_ bv62 32) ~WrapperStruct00_var_1_5_Pointer~0.base) (bvsle .cse2 (_ bv536870911 32)) (= ~WrapperStruct00_var_1_1_Pointer~0.base (_ bv46 32)) (bvsle .cse1 (_ bv536870912 32)) (= (_ bv58 32) ~WrapperStruct00_var_1_4_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8351ebb_13c7059a_Treesizes_4_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_buf_write_be32_~buf#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_aws_byte_buf_write_be32_~buf#1.base|))";
		final String expectedResultAsString = "(bvugt |ULTIMATE.start_aws_byte_buf_write_be32_~buf#1.base| (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_840e5cc7_660936bf_Treesizes_157_157() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#unsigned_short_int_Array_0~0.base", "~#double_Array_0~0.base", "~#signed_char_Array_0~0.base", "~#signed_long_int_Array_0~0.base", "~#unsigned_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_86 (_ BitVec 32)) (v_ArrVal_87 (_ BitVec 32)) (v_ArrVal_89 (_ BitVec 32)) (v_ArrVal_117 (_ BitVec 32))) (or (= ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store (store (store |#memory_int| (bvadd (_ bv2 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_117) |~#double_Array_0~0.base| v_ArrVal_87) (bvadd (_ bv4 32) |~#double_Array_0~0.base|) v_ArrVal_86) |~#signed_long_int_Array_0~0.base| ((_ zero_extend 16) ((_ extract 15 0) (select (store (store (store |#memory_int| (bvadd (_ bv2 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_117) |~#double_Array_0~0.base| v_ArrVal_87) (bvadd (_ bv4 32) |~#double_Array_0~0.base|) v_ArrVal_86) (bvadd (_ bv4 32) |~#unsigned_short_int_Array_0~0.base|))))) |~#unsigned_char_Array_0~0.base| v_ArrVal_89) (bvadd |~#signed_char_Array_0~0.base| (_ bv3 32))))) ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store (store (store |#memory_int| (bvadd (_ bv2 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_117) |~#double_Array_0~0.base| v_ArrVal_87) (bvadd (_ bv4 32) |~#double_Array_0~0.base|) v_ArrVal_86) |~#signed_long_int_Array_0~0.base| ((_ zero_extend 16) ((_ extract 15 0) (select (store (store (store |#memory_int| (bvadd (_ bv2 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_117) |~#double_Array_0~0.base| v_ArrVal_87) (bvadd (_ bv4 32) |~#double_Array_0~0.base|) v_ArrVal_86) (bvadd (_ bv4 32) |~#unsigned_short_int_Array_0~0.base|))))) |~#unsigned_char_Array_0~0.base| v_ArrVal_89) (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32)))))) (not (bvsle ((_ zero_extend 16) ((_ extract 15 0) (select (store (store (store |#memory_int| (bvadd (_ bv2 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_117) |~#double_Array_0~0.base| v_ArrVal_87) (bvadd (_ bv4 32) |~#double_Array_0~0.base|) v_ArrVal_86) (bvadd (_ bv4 32) |~#unsigned_short_int_Array_0~0.base|)))) ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| (bvadd (_ bv2 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_117) |~#double_Array_0~0.base| v_ArrVal_87) (bvadd (_ bv4 32) |~#double_Array_0~0.base|) v_ArrVal_86) |~#signed_long_int_Array_0~0.base| ((_ zero_extend 16) ((_ extract 15 0) (select (store (store (store |#memory_int| (bvadd (_ bv2 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_117) |~#double_Array_0~0.base| v_ArrVal_87) (bvadd (_ bv4 32) |~#double_Array_0~0.base|) v_ArrVal_86) (bvadd (_ bv4 32) |~#unsigned_short_int_Array_0~0.base|))))) (bvadd |~#signed_char_Array_0~0.base| (_ bv3 32)))))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_86 (_ BitVec 32)) (v_ArrVal_87 (_ BitVec 32)) (v_ArrVal_89 (_ BitVec 32)) (v_ArrVal_85 (_ BitVec 32))) (let ((.cse4 (store (store (store |#memory_int| (bvadd (_ bv2 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_85) |~#double_Array_0~0.base| v_ArrVal_87) (bvadd (_ bv4 32) |~#double_Array_0~0.base|) v_ArrVal_86))) (let ((.cse3 ((_ zero_extend 16) ((_ extract 15 0) (select .cse4 (bvadd (_ bv4 32) |~#unsigned_short_int_Array_0~0.base|)))))) (let ((.cse2 (store .cse4 |~#signed_long_int_Array_0~0.base| .cse3)) (.cse1 (bvadd |~#signed_char_Array_0~0.base| (_ bv3 32)))) (or (let ((.cse0 (store .cse2 |~#unsigned_char_Array_0~0.base| v_ArrVal_89))) (= ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32))))) ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 .cse1))))) (not (bvsle .cse3 ((_ sign_extend 24) ((_ extract 7 0) (select .cse2 .cse1))))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_84aaf6c0_f9049e22_Treesizes_28_15() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_16~0"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4~0", "~var_1_31~0"),
		};
		final String formulaAsString = "(and (bvsge ((_ sign_extend 24) ~var_1_16~0) (_ bv62 32)) (bvuge ~var_1_4~0 (_ bv1610612735 32)) (not (bvugt ~var_1_4~0 ~var_1_31~0)) (exists ((~var_1_5~0 (_ BitVec 32))) (and (bvule ~var_1_5~0 (_ bv536870912 32)) (bvuge (bvadd ~var_1_31~0 (bvmul (bvneg ~var_1_5~0) (_ bv4294967295 32))) (_ bv2147483647 32)))) (bvule ~var_1_4~0 (_ bv2147483647 32)))";
		final String expectedResultAsString = "(and (bvsge ((_ sign_extend 24) ~var_1_16~0) (_ bv62 32)) (bvuge ~var_1_4~0 (_ bv1610612735 32)) (not (bvugt ~var_1_4~0 ~var_1_31~0)) (bvule ~var_1_4~0 (_ bv2147483647 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_858023e0_487dd209_Treesizes_22_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#Ultimate.C_memset_#ptr.base", "#Ultimate.C_memset_#amount", "#Ultimate.C_memset_#value"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(or (not (= (_ bv0 32) |#Ultimate.C_memset_#value|)) (not (= (_ bv7 32) |#Ultimate.C_memset_#amount|)) (forall ((|#Ultimate.C_memset_#t~loopctr672| (_ BitVec 32))) (= (select (store |#memory_int| (bvadd |#Ultimate.C_memset_#ptr.base| |#Ultimate.C_memset_#t~loopctr672|) (_ bv0 8)) (bvadd (_ bv2 32) |#Ultimate.C_memset_#ptr.base|)) (_ bv0 8))))";
		final String expectedResultAsString = "(or (not (= (_ bv0 32) |#Ultimate.C_memset_#value|)) (= (_ bv0 8) (select |#memory_int| (bvadd (_ bv2 32) |#Ultimate.C_memset_#ptr.base|))) (not (= (_ bv7 32) |#Ultimate.C_memset_#amount|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_85f354e3_503a55c7_Treesizes_49_37() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| (bvadd (_ bv5 32) |~#WrapperStruct00~0.base|)) (bvadd (select |#memory_int| (bvadd (_ bv13 32) |~#WrapperStruct00~0.base|)) (select |#memory_int| (bvadd (_ bv9 32) |~#WrapperStruct00~0.base|)))) (bvult (_ bv128 32) (bvadd (select |#memory_int| (bvadd (_ bv13 32) |~#WrapperStruct00~0.base|)) (select |#memory_int| (bvadd (_ bv9 32) |~#WrapperStruct00~0.base|)))) (not (bvsgt (select |#memory_int| (bvadd (_ bv1 32) |~#WrapperStruct00~0.base|)) (bvadd (select |#memory_int| (bvadd (_ bv13 32) |~#WrapperStruct00~0.base|)) (select |#memory_int| (bvadd (_ bv9 32) |~#WrapperStruct00~0.base|))))))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (bvadd (_ bv5 32) |~#WrapperStruct00~0.base|)))) (and (not (bvsgt (select |#memory_int| (bvadd (_ bv1 32) |~#WrapperStruct00~0.base|)) .cse0)) (= .cse0 (bvadd (select |#memory_int| (bvadd (_ bv13 32) |~#WrapperStruct00~0.base|)) (select |#memory_int| (bvadd (_ bv9 32) |~#WrapperStruct00~0.base|)))) (bvult (_ bv128 32) .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_86c29eca_3ccd92ac_Treesizes_71_71() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~state_655~0#1", "ULTIMATE.start_main_~state_559~0#1", "ULTIMATE.start_main_~mask_SORT_1~0#1"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 8) |ULTIMATE.start_main_~state_655~0#1|)) (forall ((|v_ULTIMATE.start_main_~var_690_arg_0~0#1_16| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_577_arg_1~0#1_14| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_581_arg_1~0#1_14| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_562_arg_1~0#1_14| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_565_arg_1~0#1_14| (_ BitVec 8))) (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvor ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_577_arg_1~0#1_14|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_562_arg_1~0#1_14|) ((_ zero_extend 24) |ULTIMATE.start_main_~state_559~0#1|)))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_565_arg_1~0#1_14|)))))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_581_arg_1~0#1_14|))))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_690_arg_0~0#1_16|)))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|))) (_ bv0 8)))) (or (forall ((|v_ULTIMATE.start_main_~var_690_arg_0~0#1_16| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_687_arg_1~0#1_14| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_690_arg_0~0#1_16|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_687_arg_1~0#1_14|))))))))) ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|))))) (= (_ bv0 8) |ULTIMATE.start_main_~state_655~0#1|)))";
		final String expectedResultAsString = "(let ((.cse1 (= (_ bv0 8) |ULTIMATE.start_main_~state_655~0#1|)) (.cse0 ((_ zero_extend 24) |ULTIMATE.start_main_~mask_SORT_1~0#1|))) (and (or (forall ((|v_ULTIMATE.start_main_~var_690_arg_0~0#1_13| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_687_arg_1~0#1_11| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_687_arg_1~0#1_11|)))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_690_arg_0~0#1_13|)))) .cse0)))) .cse1) (or (not .cse1) (forall ((|v_ULTIMATE.start_main_~var_577_arg_1~0#1_11| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_581_arg_1~0#1_11| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_562_arg_1~0#1_11| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_565_arg_1~0#1_11| (_ BitVec 8)) (|v_ULTIMATE.start_main_~var_690_arg_0~0#1_13| (_ BitVec 8))) (= (_ bv0 8) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvor ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_581_arg_1~0#1_11|) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_565_arg_1~0#1_11|) ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_562_arg_1~0#1_11|) ((_ zero_extend 24) |ULTIMATE.start_main_~state_559~0#1|))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_577_arg_1~0#1_11|))))))))))))))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_690_arg_0~0#1_13|)))) .cse0)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8714efac_585b311e_Treesizes_26_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(or (not (= (_ bv0 32) (select |#memory_int| (_ bv4294967294 32)))) (not (= (_ bv0 32) (select |#memory_int| (_ bv4294967290 32)))) (exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_7| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_7|)))) (not (= (_ bv0 32) (select |#memory_int| (_ bv2 32)))))";
		final String expectedResultAsString = "(or (exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_5| (_ BitVec 32))) (not (= (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_5|) (_ bv0 32)))) (not (= (_ bv0 32) (select |#memory_int| (_ bv2 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8754f2fd_b0b8d6d_Treesizes_66_66() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#BOOL_unsigned_char_Array_0~0.base", "~#unsigned_long_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_148 (_ BitVec 32)) (v_ArrVal_147 (_ BitVec 32))) (or (not (bvult (select (store (store |#memory_int| (bvadd (_ bv20 32) |~#unsigned_long_int_Array_0~0.base|) v_ArrVal_148) (bvadd (_ bv5 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_147) (bvadd (_ bv20 32) |~#unsigned_long_int_Array_0~0.base|)) (select (store (store |#memory_int| (bvadd (_ bv20 32) |~#unsigned_long_int_Array_0~0.base|) v_ArrVal_148) (bvadd (_ bv5 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_147) (bvadd (_ bv12 32) |~#unsigned_long_int_Array_0~0.base|)))) (not (= (select (store (store |#memory_int| (bvadd (_ bv20 32) |~#unsigned_long_int_Array_0~0.base|) v_ArrVal_148) (bvadd (_ bv5 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_147) (bvadd (_ bv16 32) |~#unsigned_long_int_Array_0~0.base|)) (select (store (store |#memory_int| (bvadd (_ bv20 32) |~#unsigned_long_int_Array_0~0.base|) v_ArrVal_148) (bvadd (_ bv5 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_147) (bvadd (_ bv20 32) |~#unsigned_long_int_Array_0~0.base|))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_124 (_ BitVec 32)) (v_ArrVal_123 (_ BitVec 32))) (let ((.cse2 (bvadd (_ bv20 32) |~#unsigned_long_int_Array_0~0.base|))) (let ((.cse1 (store (store |#memory_int| .cse2 v_ArrVal_124) (bvadd (_ bv5 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_123))) (let ((.cse0 (select .cse1 .cse2))) (or (not (= .cse0 (select .cse1 (bvadd (_ bv16 32) |~#unsigned_long_int_Array_0~0.base|)))) (not (bvult .cse0 (select .cse1 (bvadd (_ bv12 32) |~#unsigned_long_int_Array_0~0.base|)))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_879740f9_f3e0f50a_Treesizes_68_68() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4| (_ BitVec 32))) (and (= (select |#memory_int| (bvadd (_ bv10 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4|)) (_ bv0 8)) (= (_ bv0 8) (select |#memory_int| (bvadd (_ bv11 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4|))) (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4|) (_ bv8689 32)) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4|) (_ bv2147483647 32)) (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4|))) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4|))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4|))) (= (_ bv0 8) (select |#memory_int| (bvadd (_ bv9 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4|))) (bvult (bvadd (_ bv26 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4|) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2|))) (and (bvugt .cse0 (_ bv8689 32)) (= (_ bv0 8) (select |#memory_int| (bvadd (_ bv9 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2|))) (bvult .cse0 (_ bv2147483647 32)) (= (select |#memory_int| (bvadd (_ bv10 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2|)) (_ bv0 8)) (bvult (bvadd (_ bv26 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2|) (_ bv2147483647 32)) (= (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2|))) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2|)) (_ bv0 32)) (= (select |#memory_int| (bvadd (_ bv11 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2|)) (_ bv0 8)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2|))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_87d95e88_b037ad44_Treesizes_59_52() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~node4__m4~0#1", "~id4~0"),
		};
		final String formulaAsString = "(and (exists ((~id1~0 (_ BitVec 8)) (~id2~0 (_ BitVec 8)) (~send4~0 (_ BitVec 8)) (~id3~0 (_ BitVec 8)) (~send1~0 (_ BitVec 8)) (~send2~0 (_ BitVec 8)) (~send3~0 (_ BitVec 8))) (and (= |ULTIMATE.start_main_~node4__m4~0#1| ((_ extract 7 0) ((_ sign_extend 24) ~send3~0))) (= ((_ sign_extend 24) ~send2~0) ((_ sign_extend 24) ~id2~0)) (bvsge ((_ sign_extend 24) ~id3~0) (_ bv0 32)) (bvsgt ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~send2~0))) ((_ sign_extend 24) ~id3~0)) (= ((_ sign_extend 24) ~id4~0) ((_ sign_extend 24) ~send4~0)) (= ((_ sign_extend 24) ~id2~0) ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~send1~0)))) (= ((_ sign_extend 24) ~id1~0) ((_ sign_extend 24) ~send1~0)) (= ((_ sign_extend 24) ~id3~0) ((_ sign_extend 24) ~send3~0)) (bvsgt ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~send4~0))) ((_ sign_extend 24) ~id1~0)))) (not (bvsgt ((_ sign_extend 24) |ULTIMATE.start_main_~node4__m4~0#1|) ((_ sign_extend 24) ~id4~0))))";
		final String expectedResultAsString = "(exists ((~id1~0 (_ BitVec 8)) (~id2~0 (_ BitVec 8)) (~send4~0 (_ BitVec 8)) (~id3~0 (_ BitVec 8)) (~send1~0 (_ BitVec 8)) (~send2~0 (_ BitVec 8)) (~send3~0 (_ BitVec 8))) (let ((.cse1 ((_ sign_extend 24) ~send2~0)) (.cse2 ((_ sign_extend 24) ~id2~0)) (.cse5 ((_ sign_extend 24) ~send1~0)) (.cse3 ((_ sign_extend 24) ~id3~0)) (.cse0 ((_ sign_extend 24) ~send3~0)) (.cse4 ((_ sign_extend 24) ~send4~0)) (.cse6 ((_ sign_extend 24) ~id1~0))) (and (= |ULTIMATE.start_main_~node4__m4~0#1| ((_ extract 7 0) .cse0)) (= .cse1 .cse2) (bvsge .cse3 (_ bv0 32)) (bvsgt ((_ sign_extend 24) ((_ extract 7 0) .cse1)) .cse3) (= ((_ sign_extend 24) ~id4~0) .cse4) (= .cse2 ((_ sign_extend 24) ((_ extract 7 0) .cse5))) (= .cse6 .cse5) (= .cse3 .cse0) (bvsgt ((_ sign_extend 24) ((_ extract 7 0) .cse4)) .cse6))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_883356dc_df790e28_Treesizes_53_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_linked_list_front_~list.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (bvult (bvadd aws_linked_list_front_~list.base (_ bv16 32)) (_ bv2147483647 32)) (exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_15 (_ BitVec 32))) (and (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_15))) (bvult (bvadd (_ bv16 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_15) (_ bv2147483647 32)) (bvugt v_aws_linked_list_front_~list.base_BEFORE_CALL_15 (_ bv67 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_15) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv67 32)))))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd aws_linked_list_front_~list.base (_ bv8 32)))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd aws_linked_list_front_~list.base (_ bv16 32)) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv67 32)))) (bvugt aws_linked_list_front_~list.base (_ bv67 32)))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd aws_linked_list_front_~list.base (_ bv16 32)))) (and (bvult .cse0 (_ bv2147483647 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd aws_linked_list_front_~list.base (_ bv8 32)))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv67 32)))) (bvugt aws_linked_list_front_~list.base (_ bv67 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_88a1a0f2_1a38b13f_Treesizes_276_152() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_9_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base", "~WrapperStruct00_var_1_10_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_136 (_ BitVec 32)) (v_ArrVal_135 (_ BitVec 32))) (or (= (_ bv0 8) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_9_Pointer~0.base))) (forall ((v_ArrVal_116 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_8_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_9_Pointer~0.base))))))) (forall ((v_ArrVal_136 (_ BitVec 32)) (v_ArrVal_135 (_ BitVec 32))) (or (= (_ bv0 8) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_9_Pointer~0.base))) (forall ((v_ArrVal_116 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_8_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_8_Pointer~0.base))) (_ bv0 32))))) (forall ((v_ArrVal_136 (_ BitVec 32)) (v_ArrVal_135 (_ BitVec 32))) (or (forall ((v_ArrVal_116 (_ BitVec 32))) (or (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_8_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_8_Pointer~0.base))) (_ bv1 32)) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_8_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_8_Pointer~0.base))) (_ bv0 32)))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_9_Pointer~0.base)))))) (forall ((v_ArrVal_136 (_ BitVec 32)) (v_ArrVal_135 (_ BitVec 32))) (or (forall ((v_ArrVal_116 (_ BitVec 32))) (= ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_8_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_9_Pointer~0.base)) (_ bv0 8))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_9_Pointer~0.base)))))) (forall ((v_ArrVal_136 (_ BitVec 32)) (v_ArrVal_135 (_ BitVec 32))) (or (forall ((v_ArrVal_116 (_ BitVec 32))) (or (not (= ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_8_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_9_Pointer~0.base)) (_ bv0 8))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_8_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_8_Pointer~0.base))) (_ bv1 32)))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_9_Pointer~0.base)))))) (forall ((v_ArrVal_136 (_ BitVec 32)) (v_ArrVal_135 (_ BitVec 32))) (or (forall ((v_ArrVal_116 (_ BitVec 32))) (or (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_8_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_8_Pointer~0.base))) (_ bv1 32)) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_8_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_8_Pointer~0.base))) (_ bv0 32)))) (= (_ bv0 8) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_135) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_136) ~WrapperStruct00_var_1_9_Pointer~0.base))))))";
		final String expectedResultAsString = "(let ((.cse0 (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| ~WrapperStruct00_var_1_9_Pointer~0.base))))) (and (or .cse0 (let ((.cse2 (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))))) (and (forall ((v_ArrVal_116 (_ BitVec 32))) (let ((.cse1 ((_ zero_extend 24) ((_ extract 7 0) (select (store .cse2 ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_8_Pointer~0.base))))) (or (= (_ bv1 32) .cse1) (= (_ bv0 32) .cse1)))) (forall ((v_ArrVal_116 (_ BitVec 32))) (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store .cse2 ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_8_Pointer~0.base))))) (forall ((v_ArrVal_116 (_ BitVec 32))) (not (= ((_ extract 7 0) (select (store .cse2 ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_9_Pointer~0.base)) (_ bv0 8))))))) (or (let ((.cse4 (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))))) (and (forall ((v_ArrVal_116 (_ BitVec 32))) (let ((.cse3 ((_ zero_extend 24) ((_ extract 7 0) (select (store .cse4 ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_8_Pointer~0.base))))) (or (= (_ bv0 32) .cse3) (= (_ bv1 32) .cse3)))) (forall ((v_ArrVal_116 (_ BitVec 32))) (let ((.cse5 (store .cse4 ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116))) (or (not (= (_ bv0 8) ((_ extract 7 0) (select .cse5 ~WrapperStruct00_var_1_9_Pointer~0.base)))) (= (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (select .cse5 ~WrapperStruct00_var_1_8_Pointer~0.base))))))) (forall ((v_ArrVal_116 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store .cse4 ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_116) ~WrapperStruct00_var_1_9_Pointer~0.base)))))) (not .cse0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_890770e5_d8d3413e_Treesizes_83_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~acopy~0#1.base", "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(or (and (= (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (select |#memory_int| |ULTIMATE.start_main_~acopy~0#1.base|)) (exists ((~SIZE~0 (_ BitVec 32))) (and (not (= (bvadd |ULTIMATE.start_main_~acopy~0#1.base| (bvmul (_ bv4 32) ~SIZE~0)) (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv4 32)))) (= (_ bv0 32) (bvsrem ~SIZE~0 (_ bv2 32)))))) (exists ((~SIZE~0 (_ BitVec 32))) (and (= (bvadd |ULTIMATE.start_main_~acopy~0#1.base| (bvmul (_ bv4 32) ~SIZE~0)) (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv4 32))) (exists ((v_DerPreprocessor_2 (_ BitVec 32)) (v_DerPreprocessor_1 (_ BitVec 32))) (= (select |#memory_int| (bvadd |ULTIMATE.start_main_~acopy~0#1.base| (_ bv4294967292 32) (bvmul (_ bv4 32) ~SIZE~0))) (select (store (store |#memory_int| (bvadd |ULTIMATE.start_main_~acopy~0#1.base| (_ bv4294967292 32) (bvmul (_ bv4 32) ~SIZE~0)) v_DerPreprocessor_1) |ULTIMATE.start_main_~acopy~0#1.base| v_DerPreprocessor_2) (bvadd |ULTIMATE.start_main_~acopy~0#1.base| (_ bv4294967292 32) (bvmul (_ bv4 32) ~SIZE~0))))) (= (select |#memory_int| (bvadd |ULTIMATE.start_main_~acopy~0#1.base| (_ bv4294967292 32) (bvmul (_ bv4 32) ~SIZE~0))) (select |#memory_int| |ULTIMATE.start_main_~acopy~0#1.base|)) (= (_ bv0 32) (bvsrem ~SIZE~0 (_ bv2 32))))))";
		final String expectedResultAsString = "(= (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (select |#memory_int| |ULTIMATE.start_main_~acopy~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8a1b632a_3d95272d_Treesizes_6_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967293 32)) (_ bv0 32)))";
		final String expectedResultAsString = "(= |ULTIMATE.start_main_~n~0#1| (_ bv3 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8a929579_156d85fc_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_whiteheat_attach_~#alen~0#1.base_BEFORE_CALL_2| (_ BitVec 32))) (= (_ bv2 32) (concat (concat (concat (select |#memory_int| (bvadd |v_whiteheat_attach_~#alen~0#1.base_BEFORE_CALL_2| (_ bv3 32))) (select |#memory_int| (bvadd |v_whiteheat_attach_~#alen~0#1.base_BEFORE_CALL_2| (_ bv2 32)))) (select |#memory_int| (bvadd |v_whiteheat_attach_~#alen~0#1.base_BEFORE_CALL_2| (_ bv1 32)))) (select |#memory_int| |v_whiteheat_attach_~#alen~0#1.base_BEFORE_CALL_2|))))";
		final String expectedResultAsString = "(exists ((|v_whiteheat_attach_~#alen~0#1.base_BEFORE_CALL_1| (_ BitVec 32))) (= (_ bv2 32) (concat (concat (concat (select |#memory_int| (bvadd |v_whiteheat_attach_~#alen~0#1.base_BEFORE_CALL_1| (_ bv3 32))) (select |#memory_int| (bvadd |v_whiteheat_attach_~#alen~0#1.base_BEFORE_CALL_1| (_ bv2 32)))) (select |#memory_int| (bvadd |v_whiteheat_attach_~#alen~0#1.base_BEFORE_CALL_1| (_ bv1 32)))) (select |#memory_int| |v_whiteheat_attach_~#alen~0#1.base_BEFORE_CALL_1|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8afe89b0_688d96a4_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_5_Pointer~0.base", "~var_1_8_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_80 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~var_1_8_Pointer~0.base v_ArrVal_80) ~var_1_1_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~var_1_8_Pointer~0.base v_ArrVal_80) ~var_1_5_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_49 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~var_1_8_Pointer~0.base v_ArrVal_49))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~var_1_1_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~var_1_5_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8b7c411_6fdca227_Treesizes_24_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_round_float_~w~0#1"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_#StackAllocations_8| (_ BitVec 32))) (and (= |ULTIMATE.start_round_float_~w~0#1| (bvand (select |#memory_int| |v_#StackAllocations_8|) (_ bv2147483648 32))) (= (_ +zero 8 24) (fp ((_ extract 31 31) (select |#memory_int| |v_#StackAllocations_8|)) ((_ extract 30 23) (select |#memory_int| |v_#StackAllocations_8|)) ((_ extract 22 0) (select |#memory_int| |v_#StackAllocations_8|))))))";
		final String expectedResultAsString = "(exists ((|v_#StackAllocations_8| (_ BitVec 32))) (let ((.cse0 (select |#memory_int| |v_#StackAllocations_8|))) (and (= |ULTIMATE.start_round_float_~w~0#1| .cse0) (= (_ +zero 8 24) (fp ((_ extract 31 31) .cse0) ((_ extract 30 23) .cse0) ((_ extract 22 0) .cse0))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8c33ff2f_25cf5519_Treesizes_37_28() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#Ultimate.C_memset_#ptr.base", "#Ultimate.C_memset_#amount", "#Ultimate.C_memset_#value"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd (_ bv1 32) |#Ultimate.C_memset_#ptr.base|))) (= (select |#memory_int| (bvadd (_ bv3 32) |#Ultimate.C_memset_#ptr.base|)) ((_ extract 7 0) |#Ultimate.C_memset_#value|)) (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd (_ bv2 32) |#Ultimate.C_memset_#ptr.base|))) (bvult (_ bv1 32) |#Ultimate.C_memset_#amount|) (exists ((|v_#Ultimate.C_memset_#t~loopctr676_67| (_ BitVec 32))) (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd |#Ultimate.C_memset_#ptr.base| |v_#Ultimate.C_memset_#t~loopctr676_67|)))))";
		final String expectedResultAsString = "(let ((.cse0 ((_ extract 7 0) |#Ultimate.C_memset_#value|))) (and (= .cse0 (select |#memory_int| (bvadd (_ bv1 32) |#Ultimate.C_memset_#ptr.base|))) (= (select |#memory_int| (bvadd (_ bv3 32) |#Ultimate.C_memset_#ptr.base|)) .cse0) (= .cse0 (select |#memory_int| (bvadd (_ bv2 32) |#Ultimate.C_memset_#ptr.base|))) (bvult (_ bv1 32) |#Ultimate.C_memset_#amount|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8c814f0f_7e21469a_Treesizes_23_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#t~ret4", "sum_#in~m"),
		};
		final String formulaAsString = "(and (not (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967294 32)) (_ bv0 32))) (= |sum_#t~ret4| (bvadd |sum_#in~m| |sum_#in~n|)) (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967293 32)) (_ bv0 32)))";
		final String expectedResultAsString = "(and (not (bvsle (bvadd |sum_#in~n| (_ bv4294967294 32)) (_ bv0 32))) (bvsle (bvadd |sum_#in~n| (_ bv4294967293 32)) (_ bv0 32)) (= |sum_#t~ret4| (bvadd |sum_#in~m| |sum_#in~n|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8d0e9601_721e2e16_Treesizes_13_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_17_Pointer~0.base", "~WrapperStruct00_var_1_13_Pointer~0.base", "~WrapperStruct00_var_1_10_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_45 (_ BitVec 32)) (v_ArrVal_71 (_ BitVec 32))) (= ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_71) ~WrapperStruct00_var_1_17_Pointer~0.base v_ArrVal_45) ~WrapperStruct00_var_1_13_Pointer~0.base)) (_ bv0 8)))";
		final String expectedResultAsString = "(forall ((v_ArrVal_44 (_ BitVec 32)) (v_ArrVal_45 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_44) ~WrapperStruct00_var_1_17_Pointer~0.base v_ArrVal_45) ~WrapperStruct00_var_1_13_Pointer~0.base))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8d867d25_6060a60a_Treesizes_27_27() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#float_Array_0~0.base", "~#signed_short_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_141 (_ BitVec 32))) (not (bvsgt ((_ sign_extend 16) ((_ extract 15 0) (select (store |#memory_int| (bvadd |~#float_Array_0~0.base| (_ bv4 32)) v_ArrVal_141) (bvadd (_ bv6 32) |~#signed_short_int_Array_0~0.base|)))) ((_ sign_extend 16) ((_ extract 15 0) (select (store |#memory_int| (bvadd |~#float_Array_0~0.base| (_ bv4 32)) v_ArrVal_141) (bvadd (_ bv4 32) |~#signed_short_int_Array_0~0.base|)))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_123 (_ BitVec 32))) (not (let ((.cse0 (store |#memory_int| (bvadd |~#float_Array_0~0.base| (_ bv4 32)) v_ArrVal_123))) (bvsgt ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 (bvadd (_ bv6 32) |~#signed_short_int_Array_0~0.base|)))) ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 (bvadd (_ bv4 32) |~#signed_short_int_Array_0~0.base|))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8e56bbc4_c3a7d137_Treesizes_16_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~g2v_new~0", "~g1v_new~0", "~nomsg~0"),
		};
		final String formulaAsString = "(and (= (bvadd ~g2v_new~0 (_ bv1 8)) (_ bv0 8)) (= ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8))) ~g1v_new~0) (= (_ bv0 8) (bvadd (_ bv1 8) ~nomsg~0)))";
		final String expectedResultAsString = "(and (= (bvadd ~g2v_new~0 (_ bv1 8)) (_ bv0 8)) (= (_ bv0 8) (bvadd (_ bv1 8) ~nomsg~0)) (= (_ bv0 8) (bvadd (_ bv1 8) ~g1v_new~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8f211c3a_7de36167_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~signed_char_Array_0_arraysigned_char_Array_0Var4_Pointer~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var5_Pointer~0.base", "~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_80 (_ BitVec 32)) (v_ArrVal_58 (_ BitVec 32)) (v_ArrVal_59 (_ BitVec 32))) (not (bvslt ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~signed_char_Array_0_arraysigned_char_Array_0Var5_Pointer~0.base v_ArrVal_80) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base v_ArrVal_58) (bvadd (_ bv4 32) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base) v_ArrVal_59) ~signed_char_Array_0_arraysigned_char_Array_0Var4_Pointer~0.base))) (_ bv0 32))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_57 (_ BitVec 32)) (v_ArrVal_58 (_ BitVec 32)) (v_ArrVal_59 (_ BitVec 32))) (not (bvslt ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~signed_char_Array_0_arraysigned_char_Array_0Var5_Pointer~0.base v_ArrVal_57) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base v_ArrVal_58) (bvadd (_ bv4 32) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base) v_ArrVal_59) ~signed_char_Array_0_arraysigned_char_Array_0Var4_Pointer~0.base))) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_8fc3fdbd_47d53b5e_Treesizes_31_31() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_30| (_ BitVec 32))) (and (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_30|) (_ bv2147483647 32)) (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_30|) (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_30|)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv68 32)) (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_30|) |#StackHeapBarrier|))) (= (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_30|)) |v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_30|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_36| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_36|))) (and (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_36|) (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_36|)) (= |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_36| (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_aws_linked_list_rbegin_harness_~#list~0#1.base_BEFORE_CALL_36|))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv68 32)))) (bvult .cse0 (_ bv2147483647 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_90318809_77657594_Treesizes_6_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_9| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_9|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_5|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_90cb2756_c4f955a0_Treesizes_119_70() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "~ARR_SIZE~0", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| (_ BitVec 32)) (|v_#StackHeapBarrier_4| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) ~ARR_SIZE~0) ((_ extract 31 0) ~ARR_SIZE~0)))) (_ bv2147483647 32)) (bvugt |v_#StackHeapBarrier_4| (_ bv33 32)) (bvugt (bvadd |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) ~ARR_SIZE~0) ((_ extract 31 0) ~ARR_SIZE~0)))) |v_#StackHeapBarrier_4|))) (= ((_ sign_extend 32) (_ bv1 32)) |ULTIMATE.start_main_~sum~0#1|) (not (bvslt ((_ sign_extend 32) (_ bv1 32)) ~ARR_SIZE~0)) (exists ((|v_ULTIMATE.start_main_~index1~0#1_8| (_ BitVec 16))) (and (bvsge ((_ sign_extend 16) |v_ULTIMATE.start_main_~index1~0#1_8|) (_ bv0 32)) (bvslt ((_ sign_extend 32) ((_ sign_extend 16) |v_ULTIMATE.start_main_~index1~0#1_8|)) ~ARR_SIZE~0))) (exists ((|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_3| (_ BitVec 32)) (|v_#StackHeapBarrier_3| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_3| (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) ~ARR_SIZE~0) ((_ extract 31 0) ~ARR_SIZE~0)))) (_ bv2147483647 32)) (bvugt |v_#StackHeapBarrier_3| (_ bv33 32)) (bvugt (bvadd |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_3| (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) ~ARR_SIZE~0) ((_ extract 31 0) ~ARR_SIZE~0)))) |v_#StackHeapBarrier_3|))) (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|ULTIMATE.start_main_~#array~0#1.base| (_ BitVec 32))) (and (bvult (bvadd |ULTIMATE.start_main_~#array~0#1.base| (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) ~ARR_SIZE~0) ((_ extract 31 0) ~ARR_SIZE~0)))) (_ bv2147483647 32)) (bvugt (bvadd |ULTIMATE.start_main_~#array~0#1.base| (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) ~ARR_SIZE~0) ((_ extract 31 0) ~ARR_SIZE~0)))) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv33 32)))) (exists ((|v_ULTIMATE.start_main_~column~0#1_18| (_ BitVec 32))) (not (bvslt ((_ sign_extend 32) |v_ULTIMATE.start_main_~column~0#1_18|) ~ARR_SIZE~0))) (exists ((|v_ULTIMATE.start_main_~index2~0#1_8| (_ BitVec 16))) (and (bvslt ((_ sign_extend 32) ((_ sign_extend 16) |v_ULTIMATE.start_main_~index2~0#1_8|)) ~ARR_SIZE~0) (bvsge ((_ sign_extend 16) |v_ULTIMATE.start_main_~index2~0#1_8|) (_ bv0 32)))))";
		final String expectedResultAsString = "(let ((.cse0 ((_ sign_extend 32) (_ bv1 32)))) (and (= .cse0 |ULTIMATE.start_main_~sum~0#1|) (not (bvslt .cse0 ~ARR_SIZE~0)) (exists ((|v_ULTIMATE.start_main_~index2~0#1_11| (_ BitVec 16))) (let ((.cse1 ((_ sign_extend 16) |v_ULTIMATE.start_main_~index2~0#1_11|))) (and (bvsge .cse1 (_ bv0 32)) (bvslt ((_ sign_extend 32) .cse1) ~ARR_SIZE~0)))) (exists ((|v_ULTIMATE.start_main_~index1~0#1_9| (_ BitVec 16))) (let ((.cse2 ((_ sign_extend 16) |v_ULTIMATE.start_main_~index1~0#1_9|))) (and (bvslt ((_ sign_extend 32) .cse2) ~ARR_SIZE~0) (bvsge .cse2 (_ bv0 32))))) (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| (_ BitVec 32))) (let ((.cse3 (bvadd |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| (bvmul (_ bv4 32) (let ((.cse4 ((_ extract 31 0) ~ARR_SIZE~0))) (bvmul .cse4 .cse4)))))) (and (bvult .cse3 (_ bv2147483647 32)) (bvugt .cse3 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv33 32))))) (exists ((|v_ULTIMATE.start_main_~column~0#1_18| (_ BitVec 32))) (not (bvslt ((_ sign_extend 32) |v_ULTIMATE.start_main_~column~0#1_18|) ~ARR_SIZE~0))) (exists ((|v_ULTIMATE.start_main_#t~nondet4#1_11| (_ BitVec 16))) (= ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet4#1_11|) ~ARR_SIZE~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_91668e13_6c43bdd6_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_13 (_ BitVec 32))) (and (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_13) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv67 32)))) (bvult (bvadd (_ bv16 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_13) (_ bv2147483647 32)) (= (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_13)) (_ bv0 32))))";
		final String expectedResultAsString = "(exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_11 (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_11))) (and (bvult .cse0 (_ bv2147483647 32)) (= (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_11)) (_ bv0 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv67 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_92058cda_b0796058_Treesizes_22_15() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start___ieee754_hypotf_~ha~0#1"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start___ieee754_hypotf_~ha~0#1_26| (_ BitVec 32))) (and (= |ULTIMATE.start___ieee754_hypotf_~ha~0#1| (bvand |v_ULTIMATE.start___ieee754_hypotf_~ha~0#1_26| (_ bv2147483647 32))) (exists ((currentRoundingMode RoundingMode)) (= (fp ((_ extract 31 31) |v_ULTIMATE.start___ieee754_hypotf_~ha~0#1_26|) ((_ extract 30 23) |v_ULTIMATE.start___ieee754_hypotf_~ha~0#1_26|) ((_ extract 22 0) |v_ULTIMATE.start___ieee754_hypotf_~ha~0#1_26|)) (fp.div currentRoundingMode ((_ to_fp 8 24) currentRoundingMode 1.0) (_ +zero 8 24))))))";
		final String expectedResultAsString = "(exists ((currentRoundingMode RoundingMode)) (= (fp.div currentRoundingMode ((_ to_fp 8 24) currentRoundingMode 1.0) (_ +zero 8 24)) (fp ((_ extract 31 31) |ULTIMATE.start___ieee754_hypotf_~ha~0#1|) ((_ extract 30 23) |ULTIMATE.start___ieee754_hypotf_~ha~0#1|) ((_ extract 22 0) |ULTIMATE.start___ieee754_hypotf_~ha~0#1|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_92a3a11b_999dbcb4_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_16_Pointer~0.base", "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_12_Pointer~0.base", "~WrapperStruct00_var_1_10_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_279 (_ BitVec 32)) (v_ArrVal_255 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_279) ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_255) ~WrapperStruct00_var_1_8_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_279) ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_255) ~WrapperStruct00_var_1_10_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_255 (_ BitVec 32)) (v_ArrVal_254 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_254) ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_255))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_8_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_10_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9361c341_d69ea2a4_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#unsigned_short_int_Array_0~0.base", "~#float_Array_0~0.base", "~#signed_char_Array_0~0.base", "~#BOOL_unsigned_char_Array_0~0.base", "~#signed_short_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_272 (_ BitVec 32)) (v_ArrVal_271 (_ BitVec 32)) (v_ArrVal_270 (_ BitVec 32)) (v_ArrVal_242 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store (store (store |#memory_int| |~#unsigned_short_int_Array_0~0.base| v_ArrVal_270) |~#float_Array_0~0.base| v_ArrVal_272) (bvadd (_ bv4 32) |~#signed_short_int_Array_0~0.base|) v_ArrVal_271) (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32)) v_ArrVal_242) |~#BOOL_unsigned_char_Array_0~0.base|)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_239 (_ BitVec 32)) (v_ArrVal_242 (_ BitVec 32)) (v_ArrVal_241 (_ BitVec 32)) (v_ArrVal_240 (_ BitVec 32))) (not (= ((_ extract 7 0) (select (store (store (store (store |#memory_int| |~#unsigned_short_int_Array_0~0.base| v_ArrVal_239) |~#float_Array_0~0.base| v_ArrVal_241) (bvadd (_ bv4 32) |~#signed_short_int_Array_0~0.base|) v_ArrVal_240) (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32)) v_ArrVal_242) |~#BOOL_unsigned_char_Array_0~0.base|)) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9453171e_e4973d2f_Treesizes_34_30() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_6~0", "~var_1_7~0", "~var_1_5~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (or (not (bvsgt ((_ sign_extend 24) ~var_1_5~0) ((_ sign_extend 24) ~var_1_6~0))) (= ((_ sign_extend 24) ~var_1_1~0) ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ~var_1_5~0) ((_ sign_extend 24) ~var_1_7~0)))))) (or (= ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ~var_1_6~0) ((_ sign_extend 24) ~var_1_7~0)))) ((_ sign_extend 24) ~var_1_1~0)) (bvsgt ((_ sign_extend 24) ~var_1_5~0) ((_ sign_extend 24) ~var_1_6~0))))";
		final String expectedResultAsString = "(let ((.cse3 ((_ sign_extend 24) ~var_1_5~0)) (.cse0 ((_ sign_extend 24) ~var_1_6~0))) (let ((.cse2 (bvsgt .cse3 .cse0)) (.cse1 ((_ sign_extend 24) ~var_1_7~0))) (or (and (= ~var_1_1~0 ((_ extract 7 0) (bvadd .cse0 .cse1))) (not .cse2)) (and .cse2 (= ~var_1_1~0 ((_ extract 7 0) (bvadd .cse3 .cse1)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_94b6171b_6bc19013_Treesizes_54_42() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "~ARR_SIZE~0"),
		};
		final String formulaAsString = "(and (not (bvslt ((_ sign_extend 32) (_ bv1 32)) ~ARR_SIZE~0)) (exists ((|v_ULTIMATE.start_main_#t~nondet7#1_10| (_ BitVec 16))) (and (bvsge ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet7#1_10|) (_ bv0 64)) (bvslt ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet7#1_10|) ~ARR_SIZE~0))) (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) ~ARR_SIZE~0) ((_ extract 31 0) ~ARR_SIZE~0)))) (_ bv2147483647 32)) (bvugt (bvadd |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| (bvmul (_ bv4 32) (bvmul ((_ extract 31 0) ~ARR_SIZE~0) ((_ extract 31 0) ~ARR_SIZE~0)))) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv33 32)))) (exists ((|v_ULTIMATE.start_main_~column~0#1_18| (_ BitVec 32))) (not (bvslt ((_ sign_extend 32) |v_ULTIMATE.start_main_~column~0#1_18|) ~ARR_SIZE~0))) (exists ((|v_ULTIMATE.start_main_#t~nondet4#1_11| (_ BitVec 16))) (= ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet4#1_11|) ~ARR_SIZE~0)))";
		final String expectedResultAsString = "(and (bvsgt ~ARR_SIZE~0 (_ bv0 64)) (not (bvslt ((_ sign_extend 32) (_ bv1 32)) ~ARR_SIZE~0)) (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| (_ BitVec 32))) (let ((.cse0 (bvadd |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| (bvmul (_ bv4 32) (let ((.cse1 ((_ extract 31 0) ~ARR_SIZE~0))) (bvmul .cse1 .cse1)))))) (and (bvult .cse0 (_ bv2147483647 32)) (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv33 32))))) (exists ((|v_ULTIMATE.start_main_~column~0#1_18| (_ BitVec 32))) (not (bvslt ((_ sign_extend 32) |v_ULTIMATE.start_main_~column~0#1_18|) ~ARR_SIZE~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_958fe7e_ce843877_Treesizes_26_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#BOOL_unsigned_char_Array_0~0.base", "~#unsigned_long_int_Array_0~0.base", "~#unsigned_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_127 (_ BitVec 32)) (v_ArrVal_96 (_ BitVec 32)) (v_ArrVal_126 (_ BitVec 32)) (v_ArrVal_125 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store (store (store |#memory_int| (bvadd (_ bv1 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_127) |~#unsigned_long_int_Array_0~0.base| v_ArrVal_125) (bvadd (_ bv4 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_126) (bvadd (_ bv2 32) |~#unsigned_char_Array_0~0.base|) v_ArrVal_96) |~#BOOL_unsigned_char_Array_0~0.base|)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_93 (_ BitVec 32)) (v_ArrVal_94 (_ BitVec 32)) (v_ArrVal_95 (_ BitVec 32)) (v_ArrVal_96 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store (store (store |#memory_int| (bvadd (_ bv1 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_94) |~#unsigned_long_int_Array_0~0.base| v_ArrVal_93) (bvadd (_ bv4 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_95) (bvadd (_ bv2 32) |~#unsigned_char_Array_0~0.base|) v_ArrVal_96) |~#BOOL_unsigned_char_Array_0~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_96353a82_ad3a3447_Treesizes_19_19() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_c_str_~buf#1.base_BEFORE_CALL_4| (_ BitVec 32))) (and (bvugt (bvadd |v_ULTIMATE.start_aws_byte_buf_eq_c_str_~buf#1.base_BEFORE_CALL_4| (_ bv16 32)) (_ bv8680 32)) (bvult (bvadd |v_ULTIMATE.start_aws_byte_buf_eq_c_str_~buf#1.base_BEFORE_CALL_4| (_ bv16 32)) (_ bv2147483647 32)) (bvugt (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_byte_buf_eq_c_str_~buf#1.base_BEFORE_CALL_4| (_ bv4 32))) (_ bv0 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_c_str_~buf#1.base_BEFORE_CALL_2| (_ BitVec 32))) (let ((.cse0 (bvadd |v_ULTIMATE.start_aws_byte_buf_eq_c_str_~buf#1.base_BEFORE_CALL_2| (_ bv16 32)))) (and (bvult .cse0 (_ bv2147483647 32)) (bvugt .cse0 (_ bv8680 32)) (bvugt (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_byte_buf_eq_c_str_~buf#1.base_BEFORE_CALL_2| (_ bv4 32))) (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_96967c9c_b9fd12a2_Treesizes_82_82() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~signed_char_Array_0_arraysigned_char_Array_0Var0_Pointer~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base", "~float_Array_0_arrayfloat_Array_0arrayVar1_Pointer~0.base", "~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_94 (_ BitVec 32)) (v_ArrVal_68 (_ BitVec 32)) (v_ArrVal_69 (_ BitVec 32))) (fp.eq (fp ((_ extract 31 31) (select (store (store (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base v_ArrVal_94) ~signed_char_Array_0_arraysigned_char_Array_0Var0_Pointer~0.base v_ArrVal_68) ~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base v_ArrVal_69) ~float_Array_0_arrayfloat_Array_0arrayVar1_Pointer~0.base)) ((_ extract 30 23) (select (store (store (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base v_ArrVal_94) ~signed_char_Array_0_arraysigned_char_Array_0Var0_Pointer~0.base v_ArrVal_68) ~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base v_ArrVal_69) ~float_Array_0_arrayfloat_Array_0arrayVar1_Pointer~0.base)) ((_ extract 22 0) (select (store (store (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base v_ArrVal_94) ~signed_char_Array_0_arraysigned_char_Array_0Var0_Pointer~0.base v_ArrVal_68) ~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base v_ArrVal_69) ~float_Array_0_arrayfloat_Array_0arrayVar1_Pointer~0.base))) (fp ((_ extract 31 31) (select (store (store (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base v_ArrVal_94) ~signed_char_Array_0_arraysigned_char_Array_0Var0_Pointer~0.base v_ArrVal_68) ~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base v_ArrVal_69) ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base)) ((_ extract 30 23) (select (store (store (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base v_ArrVal_94) ~signed_char_Array_0_arraysigned_char_Array_0Var0_Pointer~0.base v_ArrVal_68) ~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base v_ArrVal_69) ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base)) ((_ extract 22 0) (select (store (store (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base v_ArrVal_94) ~signed_char_Array_0_arraysigned_char_Array_0Var0_Pointer~0.base v_ArrVal_68) ~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base v_ArrVal_69) ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_67 (_ BitVec 32)) (v_ArrVal_68 (_ BitVec 32)) (v_ArrVal_69 (_ BitVec 32))) (let ((.cse1 (store (store (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base v_ArrVal_67) ~signed_char_Array_0_arraysigned_char_Array_0Var0_Pointer~0.base v_ArrVal_68) ~signed_char_Array_0_arraysigned_char_Array_0Var2_Pointer~0.base v_ArrVal_69))) (fp.eq (let ((.cse0 (select .cse1 ~float_Array_0_arrayfloat_Array_0arrayVar1_Pointer~0.base))) (fp ((_ extract 31 31) .cse0) ((_ extract 30 23) .cse0) ((_ extract 22 0) .cse0))) (let ((.cse2 (select .cse1 ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base))) (fp ((_ extract 31 31) .cse2) ((_ extract 30 23) .cse2) ((_ extract 22 0) .cse2))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_96d108ce_fad29d84_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_10| (_ BitVec 32))) (and (not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_10|)))) (bvult (bvadd (_ bv16 32) |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_10|) (_ bv2147483647 32)) (bvugt (bvadd (_ bv16 32) |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_10|) (_ bv8690 32))))";
		final String expectedResultAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_7| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_7|))) (and (bvugt .cse0 (_ bv8690 32)) (bvult .cse0 (_ bv2147483647 32)) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_7|)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_973e6864_5a801bad_Treesizes_17_5() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_property_#t~mem87#1", "ULTIMATE.start_property_#t~mem86#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_9 (_ BitVec 32)) (v_arrayElimCell_8 (_ BitVec 32))) (and (bvsgt ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_8)) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_9))) (= |ULTIMATE.start_property_#t~mem86#1| ((_ extract 15 0) v_arrayElimCell_8)) (= |ULTIMATE.start_property_#t~mem87#1| ((_ extract 15 0) v_arrayElimCell_9))))";
		final String expectedResultAsString = "(bvsgt ((_ sign_extend 16) |ULTIMATE.start_property_#t~mem86#1|) ((_ sign_extend 16) |ULTIMATE.start_property_#t~mem87#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_97a90da_6504a5ec_Treesizes_19_19() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_433 (_ BitVec 32))) (or (not (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_ArrVal_433)) (_ bv31 32))) (bvsgt ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv2 32) |~#WrapperStruct00~0.base|)))) ((_ zero_extend 24) ((_ extract 7 0) v_ArrVal_433)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_400 (_ BitVec 32))) (let ((.cse0 ((_ zero_extend 24) ((_ extract 7 0) v_ArrVal_400)))) (or (not (bvsle .cse0 (_ bv31 32))) (bvsgt ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv2 32) |~#WrapperStruct00~0.base|)))) .cse0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_984cf2a5_f8a593d7_Treesizes_68_66() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3| (_ BitVec 32))) (and (= (_ bv0 8) (select |#memory_int| (bvadd (_ bv11 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|))) (bvult (bvadd (_ bv26 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|) (_ bv2147483647 32)) (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|))) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|))) (bvugt (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|) (_ bv8677 32)) (= (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|)) (_ bv0 32)) (bvult (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|) (_ bv2147483647 32)) (= (_ bv0 8) (select |#memory_int| (bvadd (_ bv9 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|))) (= (select |#memory_int| (bvadd (_ bv10 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|)) (_ bv0 8))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| (_ BitVec 32))) (and (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| (_ bv4294967291 32))) (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| (_ bv4294967290 32)))) (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| (_ bv4294967289 32)))) (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| (_ bv4294967288 32))))) (= (_ bv0 8) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4|))) (bvugt |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| (_ bv8677 32)) (= (_ bv0 8) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4|))) (= (_ bv0 8) (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4|))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4|))) (bvult (bvadd (_ bv18 32) |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4|) (_ bv2147483647 32)) (bvult |v_ULTIMATE.start_aws_byte_cursor_eq_~b#1.base_BEFORE_CALL_4| (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_98e8c8eb_df4f2ea1_Treesizes_10_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_9_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_274 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_274) ~WrapperStruct00_var_1_8_Pointer~0.base))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_245 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_245) ~WrapperStruct00_var_1_8_Pointer~0.base))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_99577528_a617f647_Treesizes_40_40() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_11| (_ BitVec 32))) (and (= (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_11|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_11|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_11|))) (select |#memory_int| |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_11|)) (_ bv0 32)) (bvult (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_11|) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_11|) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8836 32))))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7|))) (and (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8836 32)) (bvugt .cse0 |#StackHeapBarrier|))) (= (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7|))) (select |#memory_int| |v_ULTIMATE.start_aws_string_eq_byte_cursor_ignore_case_harness_~#cursor~2#1.base_BEFORE_CALL_7|)) (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9a25e199_e50348b5_Treesizes_72_72() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_8_Pointer~0.base", "~var_1_11_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_99 (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_65| (_ BitVec 32))) (or (fp.eq (fp ((_ extract 31 31) |v_skolemized_q#valueAsBitvector_65|) ((_ extract 30 23) |v_skolemized_q#valueAsBitvector_65|) ((_ extract 22 0) |v_skolemized_q#valueAsBitvector_65|)) (fp ((_ extract 31 31) (select (store (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_99) ~var_1_1_Pointer~0.base |v_skolemized_q#valueAsBitvector_65|) ~var_1_8_Pointer~0.base)) ((_ extract 30 23) (select (store (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_99) ~var_1_1_Pointer~0.base |v_skolemized_q#valueAsBitvector_65|) ~var_1_8_Pointer~0.base)) ((_ extract 22 0) (select (store (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_99) ~var_1_1_Pointer~0.base |v_skolemized_q#valueAsBitvector_65|) ~var_1_8_Pointer~0.base)))) (not (= (fp ((_ extract 31 31) (select (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_99) ~var_1_8_Pointer~0.base)) ((_ extract 30 23) (select (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_99) ~var_1_8_Pointer~0.base)) ((_ extract 22 0) (select (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_99) ~var_1_8_Pointer~0.base))) (fp ((_ extract 31 31) |v_skolemized_q#valueAsBitvector_65|) ((_ extract 30 23) |v_skolemized_q#valueAsBitvector_65|) ((_ extract 22 0) |v_skolemized_q#valueAsBitvector_65|))))))";
		final String expectedResultAsString = "(forall ((|v_skolemized_q#valueAsBitvector_65| (_ BitVec 32)) (v_ArrVal_73 (_ BitVec 32))) (let ((.cse2 (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_73)) (.cse0 (fp ((_ extract 31 31) |v_skolemized_q#valueAsBitvector_65|) ((_ extract 30 23) |v_skolemized_q#valueAsBitvector_65|) ((_ extract 22 0) |v_skolemized_q#valueAsBitvector_65|)))) (or (fp.eq .cse0 (let ((.cse1 (select (store .cse2 ~var_1_1_Pointer~0.base |v_skolemized_q#valueAsBitvector_65|) ~var_1_8_Pointer~0.base))) (fp ((_ extract 31 31) .cse1) ((_ extract 30 23) .cse1) ((_ extract 22 0) .cse1)))) (not (= (let ((.cse3 (select .cse2 ~var_1_8_Pointer~0.base))) (fp ((_ extract 31 31) .cse3) ((_ extract 30 23) .cse3) ((_ extract 22 0) .cse3))) .cse0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9aa82148_dc9ffa94_Treesizes_22_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_2_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~WrapperStruct00_var_1_10_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_82 (_ BitVec 32))) (= (bvadd (select (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_82) ~WrapperStruct00_var_1_2_Pointer~0.base) (bvneg (select (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_82) ~WrapperStruct00_var_1_3_Pointer~0.base))) (select (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_82) ~WrapperStruct00_var_1_1_Pointer~0.base)))";
		final String expectedResultAsString = "(forall ((v_ArrVal_56 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_56))) (= (bvadd (bvneg (select .cse0 ~WrapperStruct00_var_1_3_Pointer~0.base)) (select .cse0 ~WrapperStruct00_var_1_2_Pointer~0.base)) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9ba4bac7_6fb0e95a_Treesizes_37_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~DEFAULTVAL~0#1", "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|))) (or (exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_3| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_3|)))) (not (= (_ bv0 32) (select |#memory_int| (_ bv2 32))))) (= |ULTIMATE.start_main_~i~0#1| (_ bv1 32)) (or (= ((_ sign_extend 24) (_ bv0 8)) (select |#memory_int| (_ bv2 32))) (= |ULTIMATE.start_main_~a~0#1.base| (_ bv2 32))) (= (_ bv0 32) |ULTIMATE.start_main_~DEFAULTVAL~0#1|))";
		final String expectedResultAsString = "(and (not (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|))) (= |ULTIMATE.start_main_~i~0#1| (_ bv1 32)) (or (= ((_ sign_extend 24) (_ bv0 8)) (select |#memory_int| (_ bv2 32))) (= |ULTIMATE.start_main_~a~0#1.base| (_ bv2 32))) (= (_ bv0 32) |ULTIMATE.start_main_~DEFAULTVAL~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9c3c1aec_160e0da8_Treesizes_4_4() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_16~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_16~0))";
		final String expectedResultAsString = "(bvsge ((_ zero_extend 24) ~var_1_16~0) (_ bv1 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9c9afd5d_636558ea_Treesizes_15_15() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem5#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(or (forall ((v_ArrVal_138 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_138) ~var_1_4_Pointer~0.base)))) (not (= (_ bv0 8) |ULTIMATE.start_step_#t~mem5#1|)))";
		final String expectedResultAsString = "(or (forall ((v_ArrVal_116 (_ BitVec 32))) (= ((_ extract 7 0) (select (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_116) ~var_1_4_Pointer~0.base)) (_ bv0 8))) (not (= (_ bv0 8) |ULTIMATE.start_step_#t~mem5#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9d4a6310_4cdb18b0_Treesizes_14_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_linked_list_is_valid_aws_linked_list_is_valid_deep_~temp~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |aws_linked_list_is_valid_aws_linked_list_is_valid_deep_~temp~0#1.base|))) (exists ((|v_aws_linked_list_is_valid_aws_linked_list_is_valid_deep_~temp~0#1.base_BEFORE_CALL_4| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_aws_linked_list_is_valid_aws_linked_list_is_valid_deep_~temp~0#1.base_BEFORE_CALL_4|)))))";
		final String expectedResultAsString = "(not (= (_ bv0 32) (select |#memory_$Pointer$.base| |aws_linked_list_is_valid_aws_linked_list_is_valid_deep_~temp~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9defea77_bdd8b392_Treesizes_31_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~MINVAL~0#1", "~CELLCOUNT~0", "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#volArray~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(or (bvsle (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv1 32)) (bvsdiv ~CELLCOUNT~0 (_ bv3 32))) (forall ((|ULTIMATE.start_main_~j~0#1| (_ BitVec 32))) (or (= (_ bv0 32) (select (store |#memory_int| (bvadd (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv12 32)) (bvmul (bvneg |ULTIMATE.start_main_~j~0#1|) (_ bv4 32)) |ULTIMATE.start_main_~#volArray~0#1.base|) (_ bv0 32)) |ULTIMATE.start_main_~#volArray~0#1.base|)) (bvsge (select |#memory_int| |ULTIMATE.start_main_~#volArray~0#1.base|) |ULTIMATE.start_main_~MINVAL~0#1|))))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| |ULTIMATE.start_main_~#volArray~0#1.base|))) (or (bvsle (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv1 32)) (bvsdiv ~CELLCOUNT~0 (_ bv3 32))) (bvsge .cse0 |ULTIMATE.start_main_~MINVAL~0#1|) (= .cse0 (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9e46b0eb_a8c590f4_Treesizes_6_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_7| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_7|)))";
		final String expectedResultAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_2| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_2|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9e8ecb5_5ce9afc4_Treesizes_160_154() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_15_Pointer~0.base", "~WrapperStruct00_var_1_9_Pointer~0.base", "~WrapperStruct00_var_1_2_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ~WrapperStruct00_var_1_2_Pointer~0.base (_ bv54 32)) (= (_ bv62 32) ~WrapperStruct00_var_1_3_Pointer~0.base) (= ~WrapperStruct00_var_1_15_Pointer~0.base (_ bv97 32)) (exists ((|v_skolemized_q#valueAsBitvector_39| (_ BitVec 64))) (and (= ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_39|) (select |#memory_int| (_ bv62 32))) (= ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_39|) (select |#memory_int| (_ bv66 32))))) (= (_ bv88 32) ~WrapperStruct00_var_1_9_Pointer~0.base) (= (_ bv46 32) |~#WrapperStruct00~0.base|) (fp.geq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854776000.0)))) (exists ((|v_skolemized_q#valueAsBitvector_38| (_ BitVec 64))) (and (fp.leq (fp ((_ extract 63 63) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32)))) ((_ extract 62 52) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32)))) ((_ extract 51 0) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))) (fp.geq (fp ((_ extract 63 63) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32)))) ((_ extract 62 52) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32)))) ((_ extract 51 0) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854776000.0)))) (= (select |#memory_int| (_ bv58 32)) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|)))) (fp.leq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))))";
		final String expectedResultAsString = "(let ((.cse3 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))) (.cse4 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854776000.0))))) (and (= ~WrapperStruct00_var_1_2_Pointer~0.base (_ bv54 32)) (= (_ bv62 32) ~WrapperStruct00_var_1_3_Pointer~0.base) (exists ((|v_skolemized_q#valueAsBitvector_39| (_ BitVec 64))) (let ((.cse1 ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_39|)) (.cse0 (select |#memory_int| (_ bv62 32)))) (let ((.cse2 (let ((.cse5 (concat .cse1 .cse0))) (fp ((_ extract 63 63) .cse5) ((_ extract 62 52) .cse5) ((_ extract 51 0) .cse5))))) (and (= ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_39|) .cse0) (= .cse1 (select |#memory_int| (_ bv66 32))) (fp.leq .cse2 .cse3) (fp.geq .cse2 .cse4))))) (= ~WrapperStruct00_var_1_15_Pointer~0.base (_ bv97 32)) (= (_ bv88 32) ~WrapperStruct00_var_1_9_Pointer~0.base) (= (_ bv46 32) |~#WrapperStruct00~0.base|) (exists ((|v_skolemized_q#valueAsBitvector_38| (_ BitVec 64))) (let ((.cse7 ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|))) (let ((.cse6 (let ((.cse8 (concat .cse7 (select |#memory_int| (_ bv54 32))))) (fp ((_ extract 63 63) .cse8) ((_ extract 62 52) .cse8) ((_ extract 51 0) .cse8))))) (and (fp.leq .cse6 .cse3) (fp.geq .cse6 .cse4) (= (select |#memory_int| (_ bv58 32)) .cse7)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9f2c91c0_48e3288a_Treesizes_13_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#float_Array_0~0.base", "~#BOOL_unsigned_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_133 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| |~#float_Array_0~0.base| v_ArrVal_133) (bvadd (_ bv1 32) |~#BOOL_unsigned_char_Array_0~0.base|))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_95 (_ BitVec 32))) (not (= ((_ extract 7 0) (select (store |#memory_int| |~#float_Array_0~0.base| v_ArrVal_95) (bvadd (_ bv1 32) |~#BOOL_unsigned_char_Array_0~0.base|))) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_9fe22007_bca085b7_Treesizes_4_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_6~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_6~0) (_ bv0 32))";
		final String expectedResultAsString = "(= ~var_1_6~0 (_ bv0 8))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a0b11645_e1154179_Treesizes_33_33() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var3_Pointer~0.base", "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base", "~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base", "~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_172 (_ BitVec 32))) (= ((_ zero_extend 16) ((_ extract 15 0) (bvadd (bvneg (bvadd (_ bv32 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base v_ArrVal_172) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var3_Pointer~0.base))))) (_ bv23103 32) ((_ zero_extend 16) ((_ extract 15 0) (select (store |#memory_int| ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base v_ArrVal_172) ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var1_Pointer~0.base)))))) ((_ zero_extend 16) ((_ extract 15 0) (select (store |#memory_int| ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base v_ArrVal_172) ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_148 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base v_ArrVal_148))) (= ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var0_Pointer~0.base))) ((_ zero_extend 16) ((_ extract 15 0) (bvadd (bvneg (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var3_Pointer~0.base))) (_ bv32 32))) (_ bv23103 32) ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 ~unsigned_short_int_Array_0_arrayunsigned_short_int_Array_0Var1_Pointer~0.base)))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a1654f5f_ea4a2e1d_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_18_Pointer~0.base", "~WrapperStruct00_var_1_20_Pointer~0.base", "~WrapperStruct00_var_1_13_Pointer~0.base", "~WrapperStruct00_var_1_22_Pointer~0.base", "~WrapperStruct00_var_1_10_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_236 (_ BitVec 32)) (v_ArrVal_235 (_ BitVec 32)) (v_ArrVal_234 (_ BitVec 32)) (v_ArrVal_211 (_ BitVec 32))) (not (= ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_18_Pointer~0.base v_ArrVal_236) ~WrapperStruct00_var_1_20_Pointer~0.base v_ArrVal_234) ~WrapperStruct00_var_1_22_Pointer~0.base v_ArrVal_235) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_211) ~WrapperStruct00_var_1_13_Pointer~0.base)) (_ bv0 8))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_209 (_ BitVec 32)) (v_ArrVal_208 (_ BitVec 32)) (v_ArrVal_211 (_ BitVec 32)) (v_ArrVal_210 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_18_Pointer~0.base v_ArrVal_210) ~WrapperStruct00_var_1_20_Pointer~0.base v_ArrVal_209) ~WrapperStruct00_var_1_22_Pointer~0.base v_ArrVal_208) ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_211) ~WrapperStruct00_var_1_13_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a2687770_29054e43_Treesizes_60_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_8~0", "~var_1_1~0"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4~0", "~var_1_5~0", "~var_1_2~0", "~var_1_3~0", "~var_1_6~0"),
		};
		final String formulaAsString = "(and (or (= ((_ zero_extend 24) ~var_1_1~0) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ~var_1_8~0)))) (bvsge (bvmul (bvmul ~var_1_2~0 ~var_1_3~0) (bvadd ~var_1_5~0 ~var_1_4~0)) ~var_1_6~0) (forall ((~var_1_7~0 (_ BitVec 8))) (not (= ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) ~var_1_7~0) ((_ zero_extend 24) ~var_1_8~0)))) ((_ zero_extend 24) ~var_1_1~0))))) (or (forall ((~var_1_7~0 (_ BitVec 8))) (= ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) ~var_1_7~0) ((_ zero_extend 24) ~var_1_8~0)))) ((_ zero_extend 24) ~var_1_1~0))) (and (= ((_ zero_extend 24) ~var_1_1~0) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ~var_1_8~0)))) (not (bvsge (bvmul (bvmul ~var_1_2~0 ~var_1_3~0) (bvadd ~var_1_5~0 ~var_1_4~0)) ~var_1_6~0)))))";
		final String expectedResultAsString = "(and (= ~var_1_1~0 ((_ extract 7 0) ((_ zero_extend 24) ~var_1_8~0))) (not (bvsge (bvmul (bvmul ~var_1_2~0 ~var_1_3~0) (bvadd ~var_1_5~0 ~var_1_4~0)) ~var_1_6~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a34d754c_375f44b5_Treesizes_24_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_36| (_ BitVec 32))) (and (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_36|) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv66 32)))) (= (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_36|) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_36|)) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_36|) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|#StackHeapBarrier| (_ BitVec 32)) (|v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_36| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_36|))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv66 32)) (= (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_36|) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_36|)) (bvult .cse0 (_ bv2147483647 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a3d31330_11791260_Treesizes_82_76() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (fp.geq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv60 32)) (select |#memory_int| (_ bv56 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv60 32)) (select |#memory_int| (_ bv56 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv60 32)) (select |#memory_int| (_ bv56 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 4611686018427383000.0)))) (= (_ bv46 32) |~#WrapperStruct00~0.base|) (exists ((|v_skolemized_q#valueAsBitvector_54| (_ BitVec 64))) (and (= (select |#memory_int| (_ bv60 32)) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_54|)) (= ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_54|) (select |#memory_int| (_ bv56 32))))) (fp.leq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv60 32)) (select |#memory_int| (_ bv56 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv60 32)) (select |#memory_int| (_ bv56 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv60 32)) (select |#memory_int| (_ bv56 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))))";
		final String expectedResultAsString = "(and (exists ((|v_skolemized_q#valueAsBitvector_54| (_ BitVec 64))) (let ((.cse0 (select |#memory_int| (_ bv60 32))) (.cse1 ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_54|))) (let ((.cse2 (let ((.cse3 (concat .cse0 .cse1))) (fp ((_ extract 63 63) .cse3) ((_ extract 62 52) .cse3) ((_ extract 51 0) .cse3))))) (and (= .cse0 ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_54|)) (= .cse1 (select |#memory_int| (_ bv56 32))) (fp.leq .cse2 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))) (fp.geq .cse2 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 4611686018427383000.0)))))))) (= (_ bv46 32) |~#WrapperStruct00~0.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a45a8bcf_901651b2_Treesizes_13_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~M~0"),
		};
		final String formulaAsString = "(and (bvsge ~M~0 (_ bv0 32)) (exists ((~N~0 (_ BitVec 32))) (and (bvslt ~M~0 ~N~0) (not (bvslt (_ bv1 32) ~N~0)))))";
		final String expectedResultAsString = "(and (bvsge ~M~0 (_ bv0 32)) (bvslt ~M~0 (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a4a7080a_bfcbd615_Treesizes_23_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_step_#t~mem35#1", "ULTIMATE.start_step_#t~mem36#1"),
		};
		final String formulaAsString = "(and (exists ((v_arrayElimCell_88 (_ BitVec 32))) (and (bvsge ((_ zero_extend 16) ((_ extract 15 0) v_arrayElimCell_88)) (_ bv32767 32)) (= ((_ extract 15 0) v_arrayElimCell_88) |ULTIMATE.start_step_#t~mem35#1|))) (exists ((v_arrayElimCell_87 (_ BitVec 32))) (and (= ((_ extract 15 0) v_arrayElimCell_87) |ULTIMATE.start_step_#t~mem36#1|) (bvsle ((_ zero_extend 16) ((_ extract 15 0) v_arrayElimCell_87)) (_ bv32767 32)))))";
		final String expectedResultAsString = "(and (exists ((v_arrayElimCell_64 (_ BitVec 32))) (let ((.cse0 ((_ extract 15 0) v_arrayElimCell_64))) (and (= |ULTIMATE.start_step_#t~mem36#1| .cse0) (bvsle ((_ zero_extend 16) .cse0) (_ bv32767 32))))) (exists ((v_arrayElimCell_65 (_ BitVec 32))) (let ((.cse1 ((_ extract 15 0) v_arrayElimCell_65))) (and (bvsge ((_ zero_extend 16) .cse1) (_ bv32767 32)) (= |ULTIMATE.start_step_#t~mem35#1| .cse1)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a567c492_5ecf9c66_Treesizes_4_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_50~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_50~0) (_ bv0 32))";
		final String expectedResultAsString = "(= (_ bv0 8) ~var_1_50~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a64d3ec5_cf6b7bf1_Treesizes_80_74() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (fp.geq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32))))) ((_ to_fp 11 53) roundNearestTiesToEven ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0)))) (= (_ bv46 32) |~#WrapperStruct00~0.base|) (exists ((|v_skolemized_q#valueAsBitvector_52| (_ BitVec 64))) (and (= ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_52|) (select |#memory_int| (_ bv74 32))) (= (select |#memory_int| (_ bv70 32)) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_52|)))) (fp.leq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv74 32)) (select |#memory_int| (_ bv70 32))))) ((_ to_fp 11 53) roundNearestTiesToEven ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854766000.0))))";
		final String expectedResultAsString = "(and (exists ((|v_skolemized_q#valueAsBitvector_52| (_ BitVec 64))) (let ((.cse0 ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_52|)) (.cse2 (select |#memory_int| (_ bv70 32)))) (let ((.cse1 (let ((.cse3 (concat .cse0 .cse2))) (fp ((_ extract 63 63) .cse3) ((_ extract 62 52) .cse3) ((_ extract 51 0) .cse3))))) (and (= .cse0 (select |#memory_int| (_ bv74 32))) (fp.leq .cse1 ((_ to_fp 11 53) roundNearestTiesToEven ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854766000.0))) (= .cse2 ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_52|)) (fp.geq .cse1 ((_ to_fp 11 53) roundNearestTiesToEven ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0)))))))) (= (_ bv46 32) |~#WrapperStruct00~0.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a6f6b096_9a0f3cba_Treesizes_20_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "##fun~$Pointer$~TO~VOID_#in~10#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "old(#memory_$Pointer$.base)"),
		};
		final String formulaAsString = "(exists ((|v_dll_insert_master_alloc_or_die_master_~ptr~1#1.base_30| (_ BitVec 32))) (not (= (_ bv0 32) (select (store (store (store |old(#memory_$Pointer$.base)| |v_dll_insert_master_alloc_or_die_master_~ptr~1#1.base_30| (_ bv0 32)) (bvadd (_ bv4 32) |v_dll_insert_master_alloc_or_die_master_~ptr~1#1.base_30|) (_ bv0 32)) (bvadd (_ bv8 32) |v_dll_insert_master_alloc_or_die_master_~ptr~1#1.base_30|) (_ bv0 32)) |##fun~$Pointer$~TO~VOID_#in~10#1.base|))))";
		final String expectedResultAsString = "(not (= (select |old(#memory_$Pointer$.base)| |##fun~$Pointer$~TO~VOID_#in~10#1.base|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a75c54c4_4d75bd4c_Treesizes_19_19() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_addflt_~ma~0#1", "ULTIMATE.start_addflt_~mb~0#1"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_addflt_~b#1_49| (_ BitVec 32)) (|v_ULTIMATE.start_addflt_~delta~0#1_33| (_ BitVec 32))) (= |ULTIMATE.start_addflt_~mb~0#1| (bvlshr (bvor (_ bv16777216 32) (bvand (_ bv16777215 32) |v_ULTIMATE.start_addflt_~b#1_49|)) |v_ULTIMATE.start_addflt_~delta~0#1_33|))) (exists ((|ULTIMATE.start_addflt_~a#1| (_ BitVec 32))) (= |ULTIMATE.start_addflt_~ma~0#1| (bvor (_ bv16777216 32) (bvand (_ bv16777215 32) |ULTIMATE.start_addflt_~a#1|)))))";
		final String expectedResultAsString = "(and (exists ((|v_ULTIMATE.start_addflt_~delta~0#1_31| (_ BitVec 32)) (|v_ULTIMATE.start_addflt_~b#1_49| (_ BitVec 32))) (= |ULTIMATE.start_addflt_~mb~0#1| (bvlshr (bvor (_ bv16777216 32) (bvand (_ bv16777215 32) |v_ULTIMATE.start_addflt_~b#1_49|)) |v_ULTIMATE.start_addflt_~delta~0#1_31|))) (exists ((|ULTIMATE.start_addflt_~a#1| (_ BitVec 32))) (= |ULTIMATE.start_addflt_~ma~0#1| (bvor (_ bv16777216 32) (bvand (_ bv16777215 32) |ULTIMATE.start_addflt_~a#1|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a78d99d3_3d0e809_Treesizes_9_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_31~0", "~var_1_30~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_31~0)) (not (= (_ bv0 8) ~var_1_30~0)))";
		final String expectedResultAsString = "(and (bvsge ((_ zero_extend 24) ~var_1_30~0) (_ bv1 32)) (bvsge ((_ zero_extend 24) ~var_1_31~0) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a89d4ea6_d1b9aca6_Treesizes_31_27() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_cursor_eq_harness_~#lhs~0#1.base", "ULTIMATE.start_aws_byte_cursor_eq_harness_~#rhs~0#1.base", "#StackAllocations"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (= (bvadd (_ bv8 32) |ULTIMATE.start_aws_byte_cursor_eq_harness_~#rhs~0#1.base|) |#StackAllocations|) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |ULTIMATE.start_aws_byte_cursor_eq_harness_~#lhs~0#1.base| (_ bv4 32)))) (bvugt (bvadd |#StackAllocations| (_ bv4294967288 32)) (_ bv8677 32)) (bvult |#StackAllocations| (_ bv2147483647 32)) (= (bvadd |ULTIMATE.start_aws_byte_cursor_eq_harness_~#lhs~0#1.base| (_ bv8 32)) |ULTIMATE.start_aws_byte_cursor_eq_harness_~#rhs~0#1.base|) (bvult (bvadd |#StackAllocations| (_ bv4294967288 32)) (_ bv2147483647 32)))";
		final String expectedResultAsString = "(and (= (bvadd (_ bv8 32) |ULTIMATE.start_aws_byte_cursor_eq_harness_~#rhs~0#1.base|) |#StackAllocations|) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |ULTIMATE.start_aws_byte_cursor_eq_harness_~#lhs~0#1.base| (_ bv4 32)))) (bvugt |ULTIMATE.start_aws_byte_cursor_eq_harness_~#rhs~0#1.base| (_ bv8677 32)) (bvult |#StackAllocations| (_ bv2147483647 32)) (bvult |ULTIMATE.start_aws_byte_cursor_eq_harness_~#rhs~0#1.base| (_ bv2147483647 32)) (= (bvadd |ULTIMATE.start_aws_byte_cursor_eq_harness_~#lhs~0#1.base| (_ bv8 32)) |ULTIMATE.start_aws_byte_cursor_eq_harness_~#rhs~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_a97d4198_5d2ef3f9_Treesizes_64_31() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) ((_ zero_extend 24) (select |#memory_int| (bvadd (concat (concat (concat (select |#memory_int| (bvadd (_ bv7 32) |ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base|)) (select |#memory_int| (bvadd (_ bv6 32) |ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base|))) (select |#memory_int| (bvadd (_ bv5 32) |ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base|))) (select |#memory_int| (bvadd (_ bv4 32) |ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base|))) (_ bv8 32) |ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base|)))) (exists ((|v_ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base_BEFORE_CALL_3| (_ BitVec 32))) (= (_ bv0 32) ((_ zero_extend 24) (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base_BEFORE_CALL_3| (_ bv8 32) (concat (concat (concat (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base_BEFORE_CALL_3| (_ bv7 32))) (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base_BEFORE_CALL_3| (_ bv6 32)))) (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base_BEFORE_CALL_3| (_ bv5 32)))) (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base_BEFORE_CALL_3| (_ bv4 32))))))))))";
		final String expectedResultAsString = "(= (_ bv0 32) ((_ zero_extend 24) (select |#memory_int| (bvadd (concat (concat (concat (select |#memory_int| (bvadd (_ bv7 32) |ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base|)) (select |#memory_int| (bvadd (_ bv6 32) |ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base|))) (select |#memory_int| (bvadd (_ bv5 32) |ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base|))) (select |#memory_int| (bvadd (_ bv4 32) |ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base|))) (_ bv8 32) |ULTIMATE.start_aws_string_bytes_harness_~str~3#1.base|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_aa079ad2_ba4a97ad_Treesizes_126_124() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#signed_long_int_Array_0~0.base", "~#BOOL_unsigned_char_Array_0~0.base", "~#signed_short_int_Array_0~0.base", "~#unsigned_long_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (not (= (_ bv67 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv64 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv70 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv63 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv71 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (= (_ bv63 32) |~#signed_short_int_Array_0~0.base|) (not (= (_ bv51 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (bvsge (select |#memory_int| (_ bv51 32)) (_ bv0 32)) (not (= (_ bv66 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (= ((_ sign_extend 16) (_ bv200 16)) (select |#memory_int| (_ bv65 32))) (not (= (_ bv54 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv55 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv62 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (bvsge (bvadd (select |#memory_int| (_ bv59 32)) (bvmul (bvneg (select |#memory_int| (_ bv51 32))) (_ bv4294967295 32))) (_ bv4294967295 32)) (not (= (_ bv75 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv61 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (= (_ bv67 32) |~#unsigned_long_int_Array_0~0.base|) (not (= (_ bv74 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv47 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv58 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (= (_ bv51 32) |~#signed_long_int_Array_0~0.base|) (bvsle (select |#memory_int| (_ bv59 32)) ((_ sign_extend 16) ((_ extract 15 0) (select |#memory_int| (_ bv65 32))))) (not (= (_ bv50 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (= (select |#memory_int| (_ bv59 32)) (bvadd (bvneg (select |#memory_int| (_ bv51 32))) (select |#memory_int| (_ bv55 32)))) (not (= (_ bv59 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv78 32) |~#BOOL_unsigned_char_Array_0~0.base|)))";
		final String expectedResultAsString = "(let ((.cse2 (select |#memory_int| (_ bv51 32))) (.cse3 (select |#memory_int| (_ bv55 32)))) (let ((.cse1 (select |#memory_int| (_ bv65 32))) (.cse0 (bvadd (bvneg .cse2) .cse3))) (and (not (= (_ bv67 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv64 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (bvsle .cse0 ((_ sign_extend 16) ((_ extract 15 0) .cse1))) (not (= (_ bv70 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv63 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv71 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (= (_ bv63 32) |~#signed_short_int_Array_0~0.base|) (not (= (_ bv51 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (bvsge .cse2 (_ bv0 32)) (not (= (_ bv66 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (= ((_ sign_extend 16) (_ bv200 16)) .cse1) (not (= (_ bv54 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv55 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv62 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv75 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv61 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (= (_ bv67 32) |~#unsigned_long_int_Array_0~0.base|) (not (= (_ bv74 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv47 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv58 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (bvsge .cse3 (_ bv4294967295 32)) (= (_ bv51 32) |~#signed_long_int_Array_0~0.base|) (not (= (_ bv50 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (= (select |#memory_int| (_ bv59 32)) .cse0) (not (= (_ bv59 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (not (= (_ bv78 32) |~#BOOL_unsigned_char_Array_0~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_aaa7a144_a44ab968_Treesizes_25_25() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_9_Pointer~0.base", "~WrapperStruct00_var_1_6_Pointer~0.base", "~WrapperStruct00_var_1_5_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_53 (_ BitVec 32)) (v_ArrVal_76 (_ BitVec 32))) (not (bvslt ((_ zero_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_76) ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_53) ~WrapperStruct00_var_1_4_Pointer~0.base))) ((_ zero_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_76) ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_53) ~WrapperStruct00_var_1_5_Pointer~0.base))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_53 (_ BitVec 32)) (v_ArrVal_52 (_ BitVec 32))) (not (let ((.cse0 (store (store |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_52) ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_53))) (bvslt ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 ~WrapperStruct00_var_1_4_Pointer~0.base))) ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 ~WrapperStruct00_var_1_5_Pointer~0.base)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_aabe3ef5_816525dc_Treesizes_32_27() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "~ARR_SIZE~0"),
		};
		final String formulaAsString = "(or (forall ((|ULTIMATE.start_main_~count~0#1| (_ BitVec 32))) (bvslt ((_ sign_extend 32) |ULTIMATE.start_main_~count~0#1|) ~ARR_SIZE~0)) (forall ((|v_ULTIMATE.start_main_#t~nondet6#1_16| (_ BitVec 16)) (|v_ULTIMATE.start_main_#t~nondet7#1_17| (_ BitVec 16))) (or (not (bvsgt ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet7#1_17|) (_ bv0 64))) (not (bvsge ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet6#1_16|) ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet7#1_17|))) (not (bvslt ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet6#1_16|) (bvadd (bvneg ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet7#1_17|)) ~ARR_SIZE~0))))) (bvslt ((_ sign_extend 32) (_ bv2 32)) ~ARR_SIZE~0))";
		final String expectedResultAsString = "(or (forall ((|v_ULTIMATE.start_main_#t~nondet6#1_16| (_ BitVec 16)) (|v_ULTIMATE.start_main_#t~nondet7#1_17| (_ BitVec 16))) (let ((.cse1 ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet6#1_16|)) (.cse0 ((_ sign_extend 48) |v_ULTIMATE.start_main_#t~nondet7#1_17|))) (or (not (bvsgt .cse0 (_ bv0 64))) (not (bvsge .cse1 .cse0)) (not (bvslt .cse1 (bvadd (bvneg .cse0) ~ARR_SIZE~0)))))) (bvslt ((_ sign_extend 32) (_ bv2 32)) ~ARR_SIZE~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ab2c5fcf_77130560_Treesizes_52_36() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (bvadd (select |#memory_int| (bvadd (_ bv37 32) |~#WrapperStruct00~0.base|)) (select |#memory_int| (bvadd (_ bv41 32) |~#WrapperStruct00~0.base|))) (select |#memory_int| (bvadd (_ bv33 32) |~#WrapperStruct00~0.base|))) (bvugt (bvadd (bvmul (select |#memory_int| (bvadd (_ bv37 32) |~#WrapperStruct00~0.base|)) (_ bv4294967295 32)) (select |#memory_int| (bvadd (_ bv33 32) |~#WrapperStruct00~0.base|))) (select |#memory_int| (bvadd (_ bv37 32) |~#WrapperStruct00~0.base|))) (bvule (bvadd (bvmul (select |#memory_int| (bvadd (_ bv37 32) |~#WrapperStruct00~0.base|)) (_ bv4294967295 32)) (select |#memory_int| (bvadd (_ bv33 32) |~#WrapperStruct00~0.base|))) (_ bv2147483647 32)))";
		final String expectedResultAsString = "(let ((.cse0 (select |#memory_int| (bvadd (_ bv41 32) |~#WrapperStruct00~0.base|))) (.cse1 (select |#memory_int| (bvadd (_ bv37 32) |~#WrapperStruct00~0.base|)))) (and (bvule .cse0 (_ bv2147483647 32)) (= (bvadd .cse1 .cse0) (select |#memory_int| (bvadd (_ bv33 32) |~#WrapperStruct00~0.base|))) (bvugt .cse0 .cse1)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ac6e62a_5f096885_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~j~0#1"),
		};
		final String formulaAsString = "(and (not (bvslt (_ bv1 32) |ULTIMATE.start_main_~j~0#1|)) (bvsgt |ULTIMATE.start_main_~j~0#1| (_ bv0 32)))";
		final String expectedResultAsString = "(and (not (bvslt (_ bv1 32) |ULTIMATE.start_main_~j~0#1|)) (bvslt (_ bv0 32) |ULTIMATE.start_main_~j~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_acae863a_f4b479f6_Treesizes_11_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#var_1_21~0.base", "~var_1_15_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_187 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| |~#var_1_21~0.base| v_ArrVal_187) ~var_1_15_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_166 (_ BitVec 32))) (not (= ((_ extract 7 0) (select (store |#memory_int| |~#var_1_21~0.base| v_ArrVal_166) ~var_1_15_Pointer~0.base)) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ae713a1e_eacff8cc_Treesizes_19_19() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#signed_long_int_Array_0~0.base", "~#unsigned_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_147 (_ BitVec 32))) (not (bvsgt (select (store |#memory_int| |~#unsigned_char_Array_0~0.base| v_ArrVal_147) (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|)) (select (store |#memory_int| |~#unsigned_char_Array_0~0.base| v_ArrVal_147) (bvadd (_ bv16 32) |~#signed_long_int_Array_0~0.base|)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_128 (_ BitVec 32))) (not (let ((.cse0 (store |#memory_int| |~#unsigned_char_Array_0~0.base| v_ArrVal_128))) (bvsgt (select .cse0 (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|)) (select .cse0 (bvadd (_ bv16 32) |~#signed_long_int_Array_0~0.base|))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_af48dd7e_cfdbe43e_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base", "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var5_Pointer~0.base", "~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base", "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var6_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_75 (_ BitVec 32)) (v_ArrVal_54 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base v_ArrVal_75) ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base v_ArrVal_54) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var5_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base v_ArrVal_75) ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base v_ArrVal_54) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var6_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_53 (_ BitVec 32)) (v_ArrVal_54 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base v_ArrVal_53) ~float_Array_0_arrayfloat_Array_0arrayVar0_Pointer~0.base v_ArrVal_54))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var6_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var5_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b0159946_4537dd7d_Treesizes_30_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#in~n", "fibonacci_#res"),
		};
		final String formulaAsString = "(and (or (= (_ bv2 32) |fibonacci_#in~n|) (forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_13| (_ BitVec 32)) (|v_fibonacci_#in~n_BEFORE_CALL_32| (_ BitVec 32))) (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_13| |fibonacci_#res|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_32| (_ bv4294967295 32))))) (forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_13| (_ BitVec 32)) (|v_fibonacci_#in~n_BEFORE_CALL_32| (_ BitVec 32))) (or (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_13| |fibonacci_#res|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_32| (_ bv4294967295 32))) (not (bvsge (bvadd (_ bv1 32) |v_fibonacci_#t~ret4_BEFORE_CALL_13|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_32| (_ bv4294967295 32)))))))";
		final String expectedResultAsString = "(and (= (_ bv2 32) |fibonacci_#in~n|) (= (_ bv1 32) |fibonacci_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b06749e1_e5dbff4f_Treesizes_11_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem58#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_15 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_15) |ULTIMATE.start_step_#t~mem58#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_15)) (_ bv0 32))))";
		final String expectedResultAsString = "(exists ((v_arrayElimCell_11 (_ BitVec 32))) (let ((.cse0 ((_ extract 7 0) v_arrayElimCell_11))) (and (= .cse0 |ULTIMATE.start_step_#t~mem58#1|) (bvsle ((_ zero_extend 24) .cse0) (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b0bf240d_afdcf203_Treesizes_14_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (= (_ bv3 32) |isEven_#in~n|) (forall ((|v_isOdd_#in~n_BEFORE_CALL_13| (_ BitVec 32))) (= (_ bv0 32) (bvsrem |v_isOdd_#in~n_BEFORE_CALL_13| (_ bv2 32))))) (= (_ bv0 32) |isEven_#res|))";
		final String expectedResultAsString = "(and (= (_ bv3 32) |isEven_#in~n|) (= (_ bv0 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b1589ab1_1b02f83f_Treesizes_104_53() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_ibmpex_query_sensor_count_~data#1.base", "ULTIMATE.start_ibmpex_find_sensors_~data#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (_ bv6 32) (concat (concat (concat (select |#memory_int| (bvadd |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| (_ bv766 32))) (select |#memory_int| (bvadd |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| (_ bv765 32)))) (select |#memory_int| (bvadd |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| (_ bv764 32)))) (select |#memory_int| (bvadd |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| (_ bv763 32))))) (bvugt |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| (_ bv705 32)) (not (bvugt |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| (_ bv2012 32))) (= |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| |ULTIMATE.start_ibmpex_query_sensor_count_~data#1.base|) (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|v_ldv_malloc_~res~0#1.base_BEFORE_CALL_1| (_ BitVec 32)) (|#StackAllocations| (_ BitVec 32))) (and (bvult |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| |#StackHeapBarrier|) (bvult |v_ldv_malloc_~res~0#1.base_BEFORE_CALL_1| |#StackHeapBarrier|) (bvult |#StackAllocations| (_ bv2147483647 32)) (bvugt |#StackAllocations| |#StackHeapBarrier|) (bvugt |v_ldv_malloc_~res~0#1.base_BEFORE_CALL_1| (_ bv705 32)))) (exists ((|v_ULTIMATE.start_ibmpex_register_bmc_~data~2#1.base_BEFORE_CALL_3| (_ BitVec 32))) (and (bvugt |v_ULTIMATE.start_ibmpex_register_bmc_~data~2#1.base_BEFORE_CALL_3| (_ bv705 32)) (not (bvugt |v_ULTIMATE.start_ibmpex_register_bmc_~data~2#1.base_BEFORE_CALL_3| (_ bv2012 32))) (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|v_ldv_malloc_~res~0#1.base_BEFORE_CALL_1| (_ BitVec 32)) (|#StackAllocations| (_ BitVec 32))) (and (bvult |v_ULTIMATE.start_ibmpex_register_bmc_~data~2#1.base_BEFORE_CALL_3| |#StackHeapBarrier|) (bvult |v_ldv_malloc_~res~0#1.base_BEFORE_CALL_1| |#StackHeapBarrier|) (bvult |#StackAllocations| (_ bv2147483647 32)) (bvugt |#StackAllocations| |#StackHeapBarrier|) (bvugt |v_ldv_malloc_~res~0#1.base_BEFORE_CALL_1| (_ bv705 32)))) (= (_ bv6 32) (concat (concat (concat (select |#memory_int| (bvadd |v_ULTIMATE.start_ibmpex_register_bmc_~data~2#1.base_BEFORE_CALL_3| (_ bv766 32))) (select |#memory_int| (bvadd |v_ULTIMATE.start_ibmpex_register_bmc_~data~2#1.base_BEFORE_CALL_3| (_ bv765 32)))) (select |#memory_int| (bvadd |v_ULTIMATE.start_ibmpex_register_bmc_~data~2#1.base_BEFORE_CALL_3| (_ bv764 32)))) (select |#memory_int| (bvadd |v_ULTIMATE.start_ibmpex_register_bmc_~data~2#1.base_BEFORE_CALL_3| (_ bv763 32))))))))";
		final String expectedResultAsString = "(and (= (_ bv6 32) (concat (concat (concat (select |#memory_int| (bvadd |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| (_ bv766 32))) (select |#memory_int| (bvadd |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| (_ bv765 32)))) (select |#memory_int| (bvadd |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| (_ bv764 32)))) (select |#memory_int| (bvadd |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| (_ bv763 32))))) (bvugt |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| (_ bv705 32)) (not (bvugt |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| (_ bv2012 32))) (= |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| |ULTIMATE.start_ibmpex_query_sensor_count_~data#1.base|) (exists ((|#StackHeapBarrier| (_ BitVec 32)) (|v_ldv_malloc_~res~0#1.base_BEFORE_CALL_1| (_ BitVec 32)) (|#StackAllocations| (_ BitVec 32))) (and (bvult |ULTIMATE.start_ibmpex_find_sensors_~data#1.base| |#StackHeapBarrier|) (bvult |v_ldv_malloc_~res~0#1.base_BEFORE_CALL_1| |#StackHeapBarrier|) (bvult |#StackAllocations| (_ bv2147483647 32)) (bvugt |#StackAllocations| |#StackHeapBarrier|) (bvugt |v_ldv_malloc_~res~0#1.base_BEFORE_CALL_1| (_ bv705 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b226e3f5_c0d5288d_Treesizes_13_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(and (exists ((~n~0 (_ BitVec 32))) (and (not (bvslt (_ bv1 32) ~n~0)) (bvslt ~counter~0 ~n~0))) (bvsge ~counter~0 (_ bv0 32)))";
		final String expectedResultAsString = "(and (bvsge ~counter~0 (_ bv0 32)) (bvslt ~counter~0 (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b2abc0_46783c5c_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_5_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_153 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_153) ~WrapperStruct00_var_1_5_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_153) ~WrapperStruct00_var_1_1_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_131 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_131))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_5_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b3461db0_92fe6cc6_Treesizes_9_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_47~0", "~var_1_22~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_47~0)) (not (= (_ bv0 8) ~var_1_22~0)))";
		final String expectedResultAsString = "(and (bvsge ((_ zero_extend 24) ~var_1_47~0) (_ bv1 32)) (bvsge ((_ zero_extend 24) ~var_1_22~0) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b3d0e909_9d236630_Treesizes_19_19() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_201 (_ BitVec 32))) (not (bvsge (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_201) ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv4294967291 32)) (select (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_201) ~WrapperStruct00_var_1_4_Pointer~0.base))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_177 (_ BitVec 32))) (not (let ((.cse0 (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_177))) (bvsge (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv4294967291 32)) (select .cse0 ~WrapperStruct00_var_1_4_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b406024c_137c2035_Treesizes_16_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#Ultimate.C_memset_#ptr.base", "#Ultimate.C_memset_#value"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| |#Ultimate.C_memset_#ptr.base|) ((_ extract 7 0) |#Ultimate.C_memset_#value|)) (exists ((|v_#Ultimate.C_memset_#t~loopctr672_36| (_ BitVec 32))) (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd |#Ultimate.C_memset_#ptr.base| |v_#Ultimate.C_memset_#t~loopctr672_36|)))))";
		final String expectedResultAsString = "(= (select |#memory_int| |#Ultimate.C_memset_#ptr.base|) ((_ extract 7 0) |#Ultimate.C_memset_#value|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b406024c_52188443_Treesizes_16_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#Ultimate.C_memset_#ptr.base", "#Ultimate.C_memset_#value"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| |#Ultimate.C_memset_#ptr.base|) ((_ extract 7 0) |#Ultimate.C_memset_#value|)) (exists ((|v_#Ultimate.C_memset_#t~loopctr676_44| (_ BitVec 32))) (= (select |#memory_int| (bvadd |#Ultimate.C_memset_#ptr.base| |v_#Ultimate.C_memset_#t~loopctr676_44|)) ((_ extract 7 0) |#Ultimate.C_memset_#value|))))";
		final String expectedResultAsString = "(= (select |#memory_int| |#Ultimate.C_memset_#ptr.base|) ((_ extract 7 0) |#Ultimate.C_memset_#value|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b406024c_99f10b4d_Treesizes_16_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#Ultimate.C_memset_#ptr.base", "#Ultimate.C_memset_#value"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| |#Ultimate.C_memset_#ptr.base|) ((_ extract 7 0) |#Ultimate.C_memset_#value|)) (exists ((|v_#Ultimate.C_memset_#t~loopctr672_40| (_ BitVec 32))) (= ((_ extract 7 0) |#Ultimate.C_memset_#value|) (select |#memory_int| (bvadd |#Ultimate.C_memset_#ptr.base| |v_#Ultimate.C_memset_#t~loopctr672_40|)))))";
		final String expectedResultAsString = "(= (select |#memory_int| |#Ultimate.C_memset_#ptr.base|) ((_ extract 7 0) |#Ultimate.C_memset_#value|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b406024c_ee321109_Treesizes_16_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#Ultimate.C_memset_#ptr.base", "#Ultimate.C_memset_#value"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| |#Ultimate.C_memset_#ptr.base|) ((_ extract 7 0) |#Ultimate.C_memset_#value|)) (exists ((|v_#Ultimate.C_memset_#t~loopctr726_98| (_ BitVec 32))) (= (select |#memory_int| (bvadd |#Ultimate.C_memset_#ptr.base| |v_#Ultimate.C_memset_#t~loopctr726_98|)) ((_ extract 7 0) |#Ultimate.C_memset_#value|))))";
		final String expectedResultAsString = "(= (select |#memory_int| |#Ultimate.C_memset_#ptr.base|) ((_ extract 7 0) |#Ultimate.C_memset_#value|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b49de9e9_d784848a_Treesizes_21_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~this_expect~0#1", "ULTIMATE.start_main_~this_buffer_empty~0#1"),
		};
		final String formulaAsString = "(and (= (bvneg (bvadd (_ bv1 32) (bvneg (bvadd (bvneg (bvadd (_ bv1 32) (bvneg |ULTIMATE.start_main_~this_buffer_empty~0#1|))) (_ bv1 32))))) (_ bv0 32)) (= (_ bv0 32) (bvurem (bvadd |ULTIMATE.start_main_~this_expect~0#1| (_ bv2 32)) (_ bv2 32))))";
		final String expectedResultAsString = "(and (= (_ bv1 32) |ULTIMATE.start_main_~this_buffer_empty~0#1|) (= (_ bv0 32) (bvurem |ULTIMATE.start_main_~this_expect~0#1| (_ bv2 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b553bcad_754c92df_Treesizes_15_15() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4_Pointer~0.base", "~var_1_6_Pointer~0.base", "~var_1_12_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_194 (_ BitVec 32))) (not (bvsle (select (store |#memory_int| ~var_1_12_Pointer~0.base v_ArrVal_194) ~var_1_4_Pointer~0.base) (select (store |#memory_int| ~var_1_12_Pointer~0.base v_ArrVal_194) ~var_1_6_Pointer~0.base))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_167 (_ BitVec 32))) (not (let ((.cse0 (store |#memory_int| ~var_1_12_Pointer~0.base v_ArrVal_167))) (bvsle (select .cse0 ~var_1_4_Pointer~0.base) (select .cse0 ~var_1_6_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b5dcd6a_a3bbe595_Treesizes_47_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_linked_list_front_~list.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (bvult (bvadd aws_linked_list_front_~list.base (_ bv16 32)) (_ bv2147483647 32)) (= (select |#memory_$Pointer$.base| aws_linked_list_front_~list.base) (bvadd aws_linked_list_front_~list.base (_ bv8 32))) (exists ((|v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14| (_ bv16 32)) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv67 32)) (bvugt (bvadd |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14| (_ bv16 32)) |#StackHeapBarrier|))) (= (bvadd |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14| (_ bv8 32)) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_front_harness_~#list~0#1.base_BEFORE_CALL_14|)))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd aws_linked_list_front_~list.base (_ bv16 32)) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv67 32)))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd aws_linked_list_front_~list.base (_ bv16 32)))) (and (bvult .cse0 (_ bv2147483647 32)) (= (select |#memory_$Pointer$.base| aws_linked_list_front_~list.base) (bvadd aws_linked_list_front_~list.base (_ bv8 32))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv67 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b62bac99_da96d275_Treesizes_6_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_29| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_29|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_23| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_23|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b73ed9e2_d92e5097_Treesizes_14_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_end_~list#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_27| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_end_harness_~#list~0#1.base_BEFORE_CALL_27|)))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_end_~list#1.base|))))";
		final String expectedResultAsString = "(not (= (_ bv0 32) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_end_~list#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b7c841f6_865a12da_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_14| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_14| (_ bv8 32)))))";
		final String expectedResultAsString = "(exists ((|v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_11| (_ BitVec 32))) (= (select |#memory_$Pointer$.base| (bvadd |v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_11| (_ bv8 32))) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b8633ee1_8c345ef5_Treesizes_17_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_6_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_5_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_126 (_ BitVec 32))) (= (bvadd (_ bv32 32) (bvneg (select (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_126) ~WrapperStruct00_var_1_6_Pointer~0.base))) (select (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_126) ~WrapperStruct00_var_1_5_Pointer~0.base)))";
		final String expectedResultAsString = "(forall ((v_ArrVal_94 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_94))) (= (select .cse0 ~WrapperStruct00_var_1_5_Pointer~0.base) (bvadd (bvneg (select .cse0 ~WrapperStruct00_var_1_6_Pointer~0.base)) (_ bv32 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b8e6543d_fd498f48_Treesizes_29_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_buf_reset_harness_~#buf~3#1.base", "ULTIMATE.start_aws_byte_buf_reset_harness_~#old~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_buf_reset_harness_~#old~0#1.base_BEFORE_CALL_1| (_ BitVec 32))) (= (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_aws_byte_buf_reset_harness_~#old~0#1.base_BEFORE_CALL_1|)) (select |#memory_$Pointer$.base| (bvadd (_ bv4294967292 32) |v_ULTIMATE.start_aws_byte_buf_reset_harness_~#old~0#1.base_BEFORE_CALL_1|)))) (= (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |ULTIMATE.start_aws_byte_buf_reset_harness_~#buf~3#1.base|)) (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |ULTIMATE.start_aws_byte_buf_reset_harness_~#old~0#1.base|))) (= (bvadd (_ bv16 32) |ULTIMATE.start_aws_byte_buf_reset_harness_~#buf~3#1.base|) |ULTIMATE.start_aws_byte_buf_reset_harness_~#old~0#1.base|))";
		final String expectedResultAsString = "(and (= (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |ULTIMATE.start_aws_byte_buf_reset_harness_~#buf~3#1.base|)) (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |ULTIMATE.start_aws_byte_buf_reset_harness_~#old~0#1.base|))) (= (bvadd (_ bv16 32) |ULTIMATE.start_aws_byte_buf_reset_harness_~#buf~3#1.base|) |ULTIMATE.start_aws_byte_buf_reset_harness_~#old~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_b9c8efde_9ea36564_Treesizes_16_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo2_#in~n"),
		};
		final String formulaAsString = "(and (not (= (_ bv5 32) |fibo2_#in~n|)) (bvslt (bvadd |fibo2_#in~n| (_ bv4294967290 32)) (_ bv1 32)) (not (bvslt (bvadd |fibo2_#in~n| (_ bv4294967292 32)) (_ bv1 32))))";
		final String expectedResultAsString = "(= (_ bv6 32) |fibo2_#in~n|)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ba0d1d88_f2cfa0bb_Treesizes_14_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#BOOL_unsigned_char_Array_0~0.base", "~#signed_short_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_289 (_ BitVec 32))) (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_289) (bvadd (_ bv1 32) |~#BOOL_unsigned_char_Array_0~0.base|))))) (_ bv0 8)))";
		final String expectedResultAsString = "(forall ((v_ArrVal_264 (_ BitVec 32))) (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| |~#signed_short_int_Array_0~0.base| v_ArrVal_264) (bvadd (_ bv1 32) |~#BOOL_unsigned_char_Array_0~0.base|))))) (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_babb93f5_e68659d5_Treesizes_42_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base", "ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~b#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~b#1.base|))) (= (bvadd |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base| (_ bv8 32)) |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~b#1.base|) (bvugt (bvadd (_ bv16 32) |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~b#1.base|) (_ bv8698 32)) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~b#1.base|) (_ bv2147483647 32)) (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_5| (_ BitVec 32))) (and (bvult (bvadd (_ bv24 32) |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_5|) (_ bv2147483647 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_5|))) (bvugt (bvadd (_ bv24 32) |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_5|) (_ bv8698 32)))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv16 32) |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~b#1.base|))) (and (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~b#1.base|))) (= (bvadd |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base| (_ bv8 32)) |ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~b#1.base|) (bvugt .cse0 (_ bv8698 32)) (bvult .cse0 (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bb9282c2_cd2ec711_Treesizes_27_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_rend_~list#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_4| (_ BitVec 32))) (and (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_4|))) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_4|) (_ bv2147483647 32)))) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_rend_~list#1.base|) (_ bv2147483647 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_rend_~list#1.base|))))";
		final String expectedResultAsString = "(and (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_rend_~list#1.base|) (_ bv2147483647 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_rend_~list#1.base|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bc312fd2_5eb297e2_Treesizes_42_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_insert_after_~after#1.base", "ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_insert_after_~after#1.base_BEFORE_CALL_3| (_ BitVec 32))) (and (bvult (bvadd (_ bv24 32) |v_ULTIMATE.start_aws_linked_list_insert_after_~after#1.base_BEFORE_CALL_3|) (_ bv2147483647 32)) (bvult (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_insert_after_~after#1.base_BEFORE_CALL_3|) (_ bv2147483647 32)) (= (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_insert_after_~after#1.base_BEFORE_CALL_3|) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_insert_after_~after#1.base_BEFORE_CALL_3|)))) (bvult (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_insert_after_~after#1.base|) (_ bv2147483647 32)) (= (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_insert_after_~after#1.base|) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_insert_after_~after#1.base|)) (= (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_insert_after_~after#1.base|) |ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base|) (bvult (bvadd (_ bv24 32) |ULTIMATE.start_aws_linked_list_insert_after_~after#1.base|) (_ bv2147483647 32)))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_insert_after_~after#1.base|))) (and (bvult .cse0 (_ bv2147483647 32)) (= .cse0 (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_insert_after_~after#1.base|)) (= (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_insert_after_~after#1.base|) |ULTIMATE.start_aws_linked_list_insert_after_~to_add#1.base|) (bvult (bvadd (_ bv24 32) |ULTIMATE.start_aws_linked_list_insert_after_~after#1.base|) (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bcc26ed0_c24da860_Treesizes_14_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (not (= (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base|) (_ bv0 32))) (exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_27| (_ BitVec 32))) (not (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_27|) (_ bv0 32)))))";
		final String expectedResultAsString = "(not (= (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bd1cb05_ef83caa7_Treesizes_168_161() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_skolemized_q#valueAsBitvector_78| (_ BitVec 64)) (|v_skolemized_q#valueAsBitvector_77| (_ BitVec 64))) (and (= (select |#memory_int| (_ bv68 32)) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_78|)) (= (select |#memory_int| (_ bv72 32)) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_78|)) (= (fp ((_ extract 63 63) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_77|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_77|))) ((_ extract 62 52) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_77|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_77|))) ((_ extract 51 0) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_77|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_77|)))) (fp ((_ extract 63 63) |v_skolemized_q#valueAsBitvector_78|) ((_ extract 62 52) |v_skolemized_q#valueAsBitvector_78|) ((_ extract 51 0) |v_skolemized_q#valueAsBitvector_78|))) (= ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_77|) (select |#memory_int| (_ bv88 32))) (fp.leq (fp ((_ extract 63 63) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_77|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_77|))) ((_ extract 62 52) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_77|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_77|))) ((_ extract 51 0) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_77|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_77|)))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))) (not (fp.gt (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv80 32)) (select |#memory_int| (_ bv76 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv80 32)) (select |#memory_int| (_ bv76 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv80 32)) (select |#memory_int| (_ bv76 32))))) (fp ((_ extract 63 63) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_77|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_77|))) ((_ extract 62 52) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_77|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_77|))) ((_ extract 51 0) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_77|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_77|)))))) (= (select |#memory_int| (_ bv84 32)) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_77|)))) (fp.geq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv80 32)) (select |#memory_int| (_ bv76 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv80 32)) (select |#memory_int| (_ bv76 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv80 32)) (select |#memory_int| (_ bv76 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854766000.0)))) (= (_ bv46 32) |~#WrapperStruct00~0.base|) (exists ((|v_skolemized_q#valueAsBitvector_76| (_ BitVec 64))) (= (select |#memory_int| (_ bv80 32)) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_76|))))";
		final String expectedResultAsString = "(and (exists ((|v_skolemized_q#valueAsBitvector_78| (_ BitVec 64)) (|v_skolemized_q#valueAsBitvector_76| (_ BitVec 64)) (|v_skolemized_q#valueAsBitvector_77| (_ BitVec 64))) (let ((.cse3 ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_77|)) (.cse4 ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_77|)) (.cse1 ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_76|))) (let ((.cse0 (let ((.cse6 (concat .cse1 (select |#memory_int| (_ bv76 32))))) (fp ((_ extract 63 63) .cse6) ((_ extract 62 52) .cse6) ((_ extract 51 0) .cse6)))) (.cse2 (let ((.cse5 (concat .cse3 .cse4))) (fp ((_ extract 63 63) .cse5) ((_ extract 62 52) .cse5) ((_ extract 51 0) .cse5))))) (and (= (select |#memory_int| (_ bv68 32)) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_78|)) (= (select |#memory_int| (_ bv72 32)) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_78|)) (fp.geq .cse0 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854766000.0)))) (= (select |#memory_int| (_ bv80 32)) .cse1) (= .cse2 (fp ((_ extract 63 63) |v_skolemized_q#valueAsBitvector_78|) ((_ extract 62 52) |v_skolemized_q#valueAsBitvector_78|) ((_ extract 51 0) |v_skolemized_q#valueAsBitvector_78|))) (not (fp.gt .cse0 .cse2)) (= .cse3 (select |#memory_int| (_ bv88 32))) (fp.leq .cse2 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))) (= (select |#memory_int| (_ bv84 32)) .cse4))))) (= (_ bv46 32) |~#WrapperStruct00~0.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bdf05b34_f37185cf_Treesizes_62_62() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base", "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var1_Pointer~0.base", "~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base", "~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base", "~signed_long_int_Array_0_arraysigned_long_int_Array_0Var1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_250 (_ BitVec 32)) (v_ArrVal_248 (_ BitVec 32)) (v_ArrVal_269 (_ BitVec 32)) (v_ArrVal_247 (_ BitVec 32))) (or (bvsgt (_ bv10 32) (bvadd (_ bv5 32) (select (store (store (store (store (store |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base v_ArrVal_269) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base v_ArrVal_248) (bvadd (_ bv4 32) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base) v_ArrVal_247) ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var1_Pointer~0.base ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base v_ArrVal_269) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base v_ArrVal_248) (bvadd (_ bv4 32) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base) v_ArrVal_247) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var1_Pointer~0.base)))) ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base v_ArrVal_250) ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var1_Pointer~0.base))) (not (bvsgt (_ bv10 32) (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base v_ArrVal_269) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base v_ArrVal_248) (bvadd (_ bv4 32) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base) v_ArrVal_247) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var1_Pointer~0.base))) (_ bv5 32))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_250 (_ BitVec 32)) (v_ArrVal_248 (_ BitVec 32)) (v_ArrVal_247 (_ BitVec 32)) (v_ArrVal_246 (_ BitVec 32))) (let ((.cse0 (store (store (store |#memory_int| ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base v_ArrVal_246) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base v_ArrVal_248) (bvadd (_ bv4 32) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base) v_ArrVal_247))) (let ((.cse1 ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var1_Pointer~0.base))))) (or (bvsgt (_ bv10 32) (bvadd (_ bv5 32) (select (store (store .cse0 ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var1_Pointer~0.base .cse1) ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base v_ArrVal_250) ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var1_Pointer~0.base))) (not (bvsgt (_ bv10 32) (bvadd (_ bv5 32) .cse1)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_be701a12_246d9832_Treesizes_26_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base", "~signed_char_Array_0_arraysigned_char_Array_0Var0_Pointer~0.base", "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var5_Pointer~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_75 (_ BitVec 32)) (v_ArrVal_47 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base v_ArrVal_75) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base v_ArrVal_47) ~signed_char_Array_0_arraysigned_char_Array_0Var0_Pointer~0.base))))) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base v_ArrVal_75) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base v_ArrVal_47) ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var5_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_46 (_ BitVec 32)) (v_ArrVal_47 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var2_Pointer~0.base v_ArrVal_46) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base v_ArrVal_47))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var5_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 ~signed_char_Array_0_arraysigned_char_Array_0Var0_Pointer~0.base))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_bf0ced58_3fcc98a0_Treesizes_12_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_1~0", "stopRequestedInDirection__wrappee__weight_~tmp___3~2"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ~calls_1~0)) (= (_ bv0 32) stopRequestedInDirection__wrappee__weight_~tmp___3~2)) (= (_ bv0 32) ~calls_1~0))";
		final String expectedResultAsString = "(and (= (_ bv0 32) stopRequestedInDirection__wrappee__weight_~tmp___3~2) (= (_ bv0 32) ~calls_1~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c0114e3c_ace476b5_Treesizes_15_15() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_property_#t~mem111#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_property_#t~ite110#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_27 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem111#1| ((_ extract 15 0) ((_ sign_extend 16) ((_ extract 15 0) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_27)))))) (= |ULTIMATE.start_property_#t~ite110#1| ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_27)))))";
		final String expectedResultAsString = "(exists ((v_arrayElimCell_23 (_ BitVec 32))) (let ((.cse0 ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_23)))) (and (= |ULTIMATE.start_property_#t~ite110#1| .cse0) (= ((_ extract 15 0) ((_ sign_extend 16) ((_ extract 15 0) .cse0))) |ULTIMATE.start_property_#t~mem111#1|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c0a8ef14_ea5b1926_Treesizes_92_92() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_property_#t~mem112#1", "ULTIMATE.start_property_#t~mem105#1", "ULTIMATE.start_property_#t~mem111#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_property_#t~ite110#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_58 (_ BitVec 32)) (v_arrayElimCell_57 (_ BitVec 32)) (v_arrayElimCell_61 (_ BitVec 32)) (v_arrayElimCell_62 (_ BitVec 32))) (and (= ((_ extract 15 0) v_arrayElimCell_62) |ULTIMATE.start_property_#t~mem111#1|) (bvsle ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_58)) (_ bv16383 32)) (= ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_57)) |ULTIMATE.start_property_#t~ite110#1|) (bvsle ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_62)) (_ bv16383 32)) (= ((_ extract 15 0) ((_ sign_extend 16) ((_ extract 15 0) (bvadd (_ bv16 32) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_61)) (bvneg (bvadd ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_57)) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_62)))))))) |ULTIMATE.start_property_#t~mem112#1|) (bvslt ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_57)) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_58))) (bvsge ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_62)) (_ bv0 32)) (= ((_ extract 15 0) v_arrayElimCell_61) |ULTIMATE.start_property_#t~mem105#1|) (not (bvsge ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_61)) ((_ sign_extend 16) ((_ extract 15 0) ((_ sign_extend 16) ((_ extract 15 0) (bvadd (_ bv16 32) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_61)) (bvneg (bvadd ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_57)) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_62))))))))))) (= (bvadd ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_57)) (bvshl ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_57)) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_61)))) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_58)))))";
		final String expectedResultAsString = "(exists ((v_arrayElimCell_27 (_ BitVec 32)) (v_arrayElimCell_26 (_ BitVec 32)) (v_arrayElimCell_31 (_ BitVec 32)) (v_arrayElimCell_30 (_ BitVec 32))) (let ((.cse6 ((_ extract 15 0) v_arrayElimCell_31)) (.cse0 ((_ extract 15 0) v_arrayElimCell_30))) (let ((.cse5 ((_ sign_extend 16) .cse0)) (.cse4 ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_26))) (.cse1 ((_ sign_extend 16) .cse6))) (let ((.cse2 ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_27))) (.cse3 ((_ extract 15 0) ((_ sign_extend 16) ((_ extract 15 0) (bvadd (_ bv16 32) .cse5 (bvneg (bvadd .cse4 .cse1)))))))) (and (= .cse0 |ULTIMATE.start_property_#t~mem105#1|) (bvsle .cse1 (_ bv16383 32)) (bvsle .cse2 (_ bv16383 32)) (= .cse3 |ULTIMATE.start_property_#t~mem112#1|) (bvslt .cse4 .cse2) (= (bvadd .cse4 (bvshl .cse4 .cse5)) .cse2) (= .cse6 |ULTIMATE.start_property_#t~mem111#1|) (not (bvsge .cse5 ((_ sign_extend 16) .cse3))) (bvsge .cse1 (_ bv0 32)) (= |ULTIMATE.start_property_#t~ite110#1| .cse4))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c11a3da5_6fe1c2_Treesizes_14_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base|))) (exists ((|v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_23| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_23|)))))";
		final String expectedResultAsString = "(not (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c19a1c84_b6a098ec_Treesizes_56_44() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_6_Pointer~0.base", "~WrapperStruct00_var_1_12_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_183 (_ BitVec 32)) (v_ArrVal_186 (_ BitVec 32))) (= ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_183) ~WrapperStruct00_var_1_1_Pointer~0.base ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_183) ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv4294967264 32))))) ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_186) ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_183) ~WrapperStruct00_var_1_1_Pointer~0.base ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_183) ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv4294967264 32))))) ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_186) ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv4294967264 32))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_186 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv4294967264 32))))) ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_186))) (= ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv4294967264 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c2801d82_3dc0af4_Treesizes_49_40() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (bvsle (select |#memory_int| (bvadd (_ bv8 32) |~#WrapperStruct00~0.base|)) (_ bv1073741823 32)) (bvsge (select |#memory_int| (bvadd (_ bv8 32) |~#WrapperStruct00~0.base|)) (_ bv0 32)) (= (bvadd (select |#memory_int| (bvadd (_ bv26 32) |~#WrapperStruct00~0.base|)) (bvneg (select |#memory_int| (bvadd (_ bv8 32) |~#WrapperStruct00~0.base|)))) (select |#memory_int| (bvadd (_ bv20 32) |~#WrapperStruct00~0.base|))) (bvuge (bvadd (select |#memory_int| (bvadd (_ bv20 32) |~#WrapperStruct00~0.base|)) (bvmul (bvneg (select |#memory_int| (bvadd (_ bv8 32) |~#WrapperStruct00~0.base|))) (_ bv4294967295 32))) (_ bv2147483647 32)))";
		final String expectedResultAsString = "(let ((.cse1 (select |#memory_int| (bvadd (_ bv26 32) |~#WrapperStruct00~0.base|))) (.cse0 (select |#memory_int| (bvadd (_ bv8 32) |~#WrapperStruct00~0.base|)))) (and (bvsle .cse0 (_ bv1073741823 32)) (bvsge .cse0 (_ bv0 32)) (bvuge .cse1 (_ bv2147483647 32)) (= (bvadd .cse1 (bvneg .cse0)) (select |#memory_int| (bvadd (_ bv20 32) |~#WrapperStruct00~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c3238357_f9ed4d56_Treesizes_103_103() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~input_10~0#1", "ULTIMATE.start_main_~var_556~0#1", "ULTIMATE.start_main_~var_149~0#1", "ULTIMATE.start_main_~mask_SORT_15~0#1", "ULTIMATE.start_main_~var_159~0#1", "ULTIMATE.start_main_~var_141~0#1", "ULTIMATE.start_main_~state_138~0#1", "ULTIMATE.start_main_~mask_SORT_57~0#1", "ULTIMATE.start_main_~state_158~0#1", "ULTIMATE.start_main_~state_134~0#1", "ULTIMATE.start_main_~var_113~0#1", "ULTIMATE.start_main_~var_148~0#1", "ULTIMATE.start_main_~var_200~0#1", "ULTIMATE.start_main_~var_45~0#1", "ULTIMATE.start_main_~mask_SORT_1~0#1"),
		};
		final String formulaAsString = "(and (= (_ bv31 8) |ULTIMATE.start_main_~mask_SORT_57~0#1|) (or (and (exists ((|v_ULTIMATE.start_main_~var_149_arg_1~0#1_21| (_ BitVec 8))) (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_149_arg_1~0#1_21|))) (_ bv31 32))) |ULTIMATE.start_main_~var_149~0#1|)) (not (= (_ bv0 8) |ULTIMATE.start_main_~input_10~0#1|))) (and (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvadd (bvneg ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) |ULTIMATE.start_main_~var_113~0#1|) (_ bv1 32))))) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv255 32) ((_ zero_extend 24) |ULTIMATE.start_main_~var_141~0#1|)))))))))))))) (_ bv31 32))) |ULTIMATE.start_main_~var_149~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~input_10~0#1|))) (= (_ bv0 8) |ULTIMATE.start_main_~var_159~0#1|) (= (_ bv9 8) |ULTIMATE.start_main_~var_556~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~state_138~0#1|) (not (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor (_ bv254 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor (_ bv254 32) ((_ zero_extend 24) ((_ extract 7 0) (bvnot ((_ zero_extend 24) |ULTIMATE.start_main_~var_113~0#1|))))))))))))))) (= (_ bv15 8) |ULTIMATE.start_main_~mask_SORT_15~0#1|) (= (_ bv9 8) |ULTIMATE.start_main_~state_158~0#1|) (= (_ bv1 8) |ULTIMATE.start_main_~mask_SORT_1~0#1|) (= (_ bv8 8) |ULTIMATE.start_main_~var_200~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~state_134~0#1|) (= (_ bv1 8) |ULTIMATE.start_main_~var_45~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~var_148~0#1|))";
		final String expectedResultAsString = "(let ((.cse0 ((_ zero_extend 24) |ULTIMATE.start_main_~var_113~0#1|))) (and (= (_ bv31 8) |ULTIMATE.start_main_~mask_SORT_57~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~var_159~0#1|) (= (_ bv9 8) |ULTIMATE.start_main_~var_556~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~state_138~0#1|) (not (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor (_ bv254 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor (_ bv254 32) ((_ zero_extend 24) ((_ extract 7 0) (bvnot .cse0)))))))))))))) (= (_ bv15 8) |ULTIMATE.start_main_~mask_SORT_15~0#1|) (= (_ bv9 8) |ULTIMATE.start_main_~state_158~0#1|) (= (_ bv1 8) |ULTIMATE.start_main_~mask_SORT_1~0#1|) (let ((.cse1 (= (_ bv0 8) |ULTIMATE.start_main_~input_10~0#1|))) (or (and (not .cse1) (exists ((|v_ULTIMATE.start_main_~var_149_arg_1~0#1_16| (_ BitVec 8))) (= |ULTIMATE.start_main_~var_149~0#1| ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_149_arg_1~0#1_16|))) (_ bv31 32)))))) (and (= ((_ extract 7 0) (bvand ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvadd (bvneg ((_ zero_extend 24) ((_ extract 7 0) (bvand .cse0 (_ bv1 32))))) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv255 32) ((_ zero_extend 24) |ULTIMATE.start_main_~var_141~0#1|)))))))))))))) (_ bv31 32))) |ULTIMATE.start_main_~var_149~0#1|) .cse1))) (= (_ bv8 8) |ULTIMATE.start_main_~var_200~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~state_134~0#1|) (= (_ bv1 8) |ULTIMATE.start_main_~var_45~0#1|) (= (_ bv0 8) |ULTIMATE.start_main_~var_148~0#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c37896d5_4ee7bbde_Treesizes_25_25() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_12_Pointer~0.base", "~WrapperStruct00_var_1_2_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_10_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_82 (_ BitVec 32)) (v_ArrVal_59 (_ BitVec 32))) (= ((_ sign_extend 16) ((_ zero_extend 8) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_82) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_59) ~WrapperStruct00_var_1_2_Pointer~0.base)))) ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_82) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_59) ~WrapperStruct00_var_1_1_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_58 (_ BitVec 32)) (v_ArrVal_59 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_58) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_59))) (= ((_ sign_extend 16) ((_ zero_extend 8) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_2_Pointer~0.base)))) ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c46e710b_be9f0af4_Treesizes_9_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~i~0#1"),
		};
		final String formulaAsString = "(and (bvsge (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv4294967295 32)) (_ bv0 32)) (bvsge |ULTIMATE.start_main_~i~0#1| (_ bv0 32)))";
		final String expectedResultAsString = "(bvsgt |ULTIMATE.start_main_~i~0#1| (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c4edbea4_33b87dc2_Treesizes_249_249() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#double_Array_0~0.base", "~#float_Array_0~0.base", "~#signed_long_int_Array_0~0.base", "~#BOOL_unsigned_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_224 (_ BitVec 32)) (v_ArrVal_187 (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_66| (_ BitVec 64)) (v_ArrVal_186 (_ BitVec 32))) (or (not (= (fp ((_ extract 63 63) (concat (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_224) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187) (bvadd (_ bv4 32) |~#double_Array_0~0.base|)) (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_224) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187) |~#double_Array_0~0.base|))) ((_ extract 62 52) (concat (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_224) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187) (bvadd (_ bv4 32) |~#double_Array_0~0.base|)) (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_224) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187) |~#double_Array_0~0.base|))) ((_ extract 51 0) (concat (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_224) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187) (bvadd (_ bv4 32) |~#double_Array_0~0.base|)) (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_224) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187) |~#double_Array_0~0.base|)))) (fp ((_ extract 63 63) |v_skolemized_q#valueAsBitvector_66|) ((_ extract 62 52) |v_skolemized_q#valueAsBitvector_66|) ((_ extract 51 0) |v_skolemized_q#valueAsBitvector_66|)))) (fp.eq (fp ((_ extract 63 63) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_66|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_66|))) ((_ extract 62 52) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_66|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_66|))) ((_ extract 51 0) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_66|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_66|)))) (fp ((_ extract 63 63) (concat (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_224) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187) (bvadd (_ bv4 32) |~#double_Array_0~0.base|)) (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_224) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187) |~#double_Array_0~0.base|))) ((_ extract 62 52) (concat (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_224) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187) (bvadd (_ bv4 32) |~#double_Array_0~0.base|)) (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_224) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187) |~#double_Array_0~0.base|))) ((_ extract 51 0) (concat (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_224) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187) (bvadd (_ bv4 32) |~#double_Array_0~0.base|)) (select (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_224) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187) |~#double_Array_0~0.base|)))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_187 (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_66| (_ BitVec 64)) (v_ArrVal_186 (_ BitVec 32)) (v_ArrVal_185 (_ BitVec 32))) (let ((.cse1 (let ((.cse2 (let ((.cse3 (store (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_long_int_Array_0~0.base|) v_ArrVal_185) |~#float_Array_0~0.base| v_ArrVal_186) (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_187))) (concat (select .cse3 (bvadd (_ bv4 32) |~#double_Array_0~0.base|)) (select .cse3 |~#double_Array_0~0.base|))))) (fp ((_ extract 63 63) .cse2) ((_ extract 62 52) .cse2) ((_ extract 51 0) .cse2))))) (or (fp.eq (let ((.cse0 (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_66|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_66|)))) (fp ((_ extract 63 63) .cse0) ((_ extract 62 52) .cse0) ((_ extract 51 0) .cse0))) .cse1) (not (= .cse1 (fp ((_ extract 63 63) |v_skolemized_q#valueAsBitvector_66|) ((_ extract 62 52) |v_skolemized_q#valueAsBitvector_66|) ((_ extract 51 0) |v_skolemized_q#valueAsBitvector_66|)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c5667c9f_4c049535_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_12 (_ BitVec 32))) (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_12)) (select |#memory_int| (bvadd (_ bv2 32) v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_12))) (select |#memory_int| (bvadd (_ bv1 32) v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_12))) (select |#memory_int| v_aws_byte_cursor_left_trim_pred_~source.base_BEFORE_CALL_12))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_16| (_ BitVec 32))) (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_byte_cursor_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_16|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_byte_cursor_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_16|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_byte_cursor_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_16|))) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_16|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c5af061d_93a11b29_Treesizes_24_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_ring_buffer_clean_up_~ring_buf#1.base_BEFORE_CALL_4| (_ BitVec 32))) (and (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv20 32) |v_ULTIMATE.start_aws_ring_buffer_clean_up_~ring_buf#1.base_BEFORE_CALL_4|) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8683 32)))) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_ring_buffer_clean_up_~ring_buf#1.base_BEFORE_CALL_4|)) (_ bv0 32)) (bvult (bvadd (_ bv20 32) |v_ULTIMATE.start_aws_ring_buffer_clean_up_~ring_buf#1.base_BEFORE_CALL_4|) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|#StackHeapBarrier| (_ BitVec 32)) (|v_ULTIMATE.start_aws_ring_buffer_clean_up_harness_~#ring_buf~0#1.base_BEFORE_CALL_36| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv20 32) |v_ULTIMATE.start_aws_ring_buffer_clean_up_harness_~#ring_buf~0#1.base_BEFORE_CALL_36|))) (and (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_ring_buffer_clean_up_harness_~#ring_buf~0#1.base_BEFORE_CALL_36|)) (_ bv0 32)) (bvugt .cse0 |#StackHeapBarrier|) (bvult .cse0 (_ bv2147483647 32)) (bvugt |#StackHeapBarrier| (_ bv8683 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c5ccae38_229d52bf_Treesizes_26_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var3_Pointer~0.base", "~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base", "~double_Array_0_arraydouble_Array_0arrayVar1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_183 (_ BitVec 32)) (v_ArrVal_182 (_ BitVec 32))) (= ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~double_Array_0_arraydouble_Array_0arrayVar1_Pointer~0.base v_ArrVal_182) (bvadd ~double_Array_0_arraydouble_Array_0arrayVar1_Pointer~0.base (_ bv4 32)) v_ArrVal_183) ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var3_Pointer~0.base))) (select (store (store |#memory_int| ~double_Array_0_arraydouble_Array_0arrayVar1_Pointer~0.base v_ArrVal_182) (bvadd ~double_Array_0_arraydouble_Array_0arrayVar1_Pointer~0.base (_ bv4 32)) v_ArrVal_183) ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base)))";
		final String expectedResultAsString = "(forall ((v_ArrVal_154 (_ BitVec 32)) (v_ArrVal_153 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~double_Array_0_arraydouble_Array_0arrayVar1_Pointer~0.base v_ArrVal_154) (bvadd ~double_Array_0_arraydouble_Array_0arrayVar1_Pointer~0.base (_ bv4 32)) v_ArrVal_153))) (= ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var3_Pointer~0.base))) (select .cse0 ~signed_long_int_Array_0_arraysigned_long_int_Array_0Var3_Pointer~0.base))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c67568e_f32bc7e9_Treesizes_150_150() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_9_Pointer~0.base", "~var_1_10_Pointer~0.base", "~var_1_15_Pointer~0.base", "~var_1_8_Pointer~0.base", "~var_1_1_Pointer~0.base", "~var_1_12_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_64 (_ BitVec 32)) (v_ArrVal_65 (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_21| (_ BitVec 32)) (v_ArrVal_84 (_ BitVec 32)) (v_ArrVal_63 (_ BitVec 32))) (or (not (= (fp ((_ extract 31 31) (select (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_84) ~var_1_9_Pointer~0.base)) ((_ extract 30 23) (select (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_84) ~var_1_9_Pointer~0.base)) ((_ extract 22 0) (select (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_84) ~var_1_9_Pointer~0.base))) (fp ((_ extract 31 31) |v_skolemized_q#valueAsBitvector_21|) ((_ extract 30 23) |v_skolemized_q#valueAsBitvector_21|) ((_ extract 22 0) |v_skolemized_q#valueAsBitvector_21|)))) (fp.eq (fp ((_ extract 31 31) (select (store (store (store (store (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_84) ~var_1_8_Pointer~0.base |v_skolemized_q#valueAsBitvector_21|) ~var_1_10_Pointer~0.base v_ArrVal_63) ~var_1_12_Pointer~0.base v_ArrVal_64) ~var_1_15_Pointer~0.base v_ArrVal_65) ~var_1_8_Pointer~0.base)) ((_ extract 30 23) (select (store (store (store (store (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_84) ~var_1_8_Pointer~0.base |v_skolemized_q#valueAsBitvector_21|) ~var_1_10_Pointer~0.base v_ArrVal_63) ~var_1_12_Pointer~0.base v_ArrVal_64) ~var_1_15_Pointer~0.base v_ArrVal_65) ~var_1_8_Pointer~0.base)) ((_ extract 22 0) (select (store (store (store (store (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_84) ~var_1_8_Pointer~0.base |v_skolemized_q#valueAsBitvector_21|) ~var_1_10_Pointer~0.base v_ArrVal_63) ~var_1_12_Pointer~0.base v_ArrVal_64) ~var_1_15_Pointer~0.base v_ArrVal_65) ~var_1_8_Pointer~0.base))) (fp ((_ extract 31 31) (select (store (store (store (store (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_84) ~var_1_8_Pointer~0.base |v_skolemized_q#valueAsBitvector_21|) ~var_1_10_Pointer~0.base v_ArrVal_63) ~var_1_12_Pointer~0.base v_ArrVal_64) ~var_1_15_Pointer~0.base v_ArrVal_65) ~var_1_9_Pointer~0.base)) ((_ extract 30 23) (select (store (store (store (store (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_84) ~var_1_8_Pointer~0.base |v_skolemized_q#valueAsBitvector_21|) ~var_1_10_Pointer~0.base v_ArrVal_63) ~var_1_12_Pointer~0.base v_ArrVal_64) ~var_1_15_Pointer~0.base v_ArrVal_65) ~var_1_9_Pointer~0.base)) ((_ extract 22 0) (select (store (store (store (store (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_84) ~var_1_8_Pointer~0.base |v_skolemized_q#valueAsBitvector_21|) ~var_1_10_Pointer~0.base v_ArrVal_63) ~var_1_12_Pointer~0.base v_ArrVal_64) ~var_1_15_Pointer~0.base v_ArrVal_65) ~var_1_9_Pointer~0.base))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_64 (_ BitVec 32)) (v_ArrVal_65 (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_21| (_ BitVec 32)) (v_ArrVal_61 (_ BitVec 32)) (v_ArrVal_63 (_ BitVec 32))) (let ((.cse1 (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_61))) (or (not (= (let ((.cse0 (select .cse1 ~var_1_9_Pointer~0.base))) (fp ((_ extract 31 31) .cse0) ((_ extract 30 23) .cse0) ((_ extract 22 0) .cse0))) (fp ((_ extract 31 31) |v_skolemized_q#valueAsBitvector_21|) ((_ extract 30 23) |v_skolemized_q#valueAsBitvector_21|) ((_ extract 22 0) |v_skolemized_q#valueAsBitvector_21|)))) (let ((.cse3 (store (store (store (store .cse1 ~var_1_8_Pointer~0.base |v_skolemized_q#valueAsBitvector_21|) ~var_1_10_Pointer~0.base v_ArrVal_63) ~var_1_12_Pointer~0.base v_ArrVal_64) ~var_1_15_Pointer~0.base v_ArrVal_65))) (fp.eq (let ((.cse2 (select .cse3 ~var_1_8_Pointer~0.base))) (fp ((_ extract 31 31) .cse2) ((_ extract 30 23) .cse2) ((_ extract 22 0) .cse2))) (let ((.cse4 (select .cse3 ~var_1_9_Pointer~0.base))) (fp ((_ extract 31 31) .cse4) ((_ extract 30 23) .cse4) ((_ extract 22 0) .cse4))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c725bdaa_dcef82eb_Treesizes_52_30() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_linked_list_insert_before_~before.base", "aws_linked_list_insert_before_~to_add.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (= (bvadd (_ bv8 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) aws_linked_list_insert_before_~before.base))) aws_linked_list_insert_before_~before.base) (= aws_linked_list_insert_before_~to_add.base (bvadd (_ bv8 32) aws_linked_list_insert_before_~before.base)) (bvugt (bvadd (_ bv8 32) aws_linked_list_insert_before_~before.base) (_ bv71 32)) (bvult (bvadd (_ bv8 32) aws_linked_list_insert_before_~before.base) (_ bv2147483647 32)) (bvult (bvadd (_ bv16 32) aws_linked_list_insert_before_~before.base) (_ bv2147483647 32)) (exists ((|v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_1| (_ BitVec 32))) (and (= |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_1| (bvadd (_ bv16 32) (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_1| (_ bv4294967292 32))))) (bvugt |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_1| (_ bv71 32)) (bvult |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_1| (_ bv2147483647 32)) (bvult (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_push_back_~node#1.base_BEFORE_CALL_1|) (_ bv2147483647 32)))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv8 32) aws_linked_list_insert_before_~before.base))) (and (= (bvadd (_ bv8 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) aws_linked_list_insert_before_~before.base))) aws_linked_list_insert_before_~before.base) (= aws_linked_list_insert_before_~to_add.base .cse0) (bvugt .cse0 (_ bv71 32)) (bvult .cse0 (_ bv2147483647 32)) (bvult (bvadd (_ bv16 32) aws_linked_list_insert_before_~before.base) (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c7946445_376bc5b6_Treesizes_28_28() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_3_Pointer~0.base", "~var_1_2_Pointer~0.base", "~var_1_7_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_293 (_ BitVec 32)) (v_ArrVal_292 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~var_1_7_Pointer~0.base v_ArrVal_292) (bvadd ~var_1_7_Pointer~0.base (_ bv4 32)) v_ArrVal_293) ~var_1_3_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~var_1_7_Pointer~0.base v_ArrVal_292) (bvadd ~var_1_7_Pointer~0.base (_ bv4 32)) v_ArrVal_293) ~var_1_2_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_257 (_ BitVec 32)) (v_ArrVal_256 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~var_1_7_Pointer~0.base v_ArrVal_256) (bvadd ~var_1_7_Pointer~0.base (_ bv4 32)) v_ArrVal_257))) (= ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~var_1_3_Pointer~0.base))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~var_1_2_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c8259b4e_a93232ff_Treesizes_8_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_11~0"),
		};
		final String formulaAsString = "(forall ((v_functionized3_~functionized3_localFunctionVar0_25 (_ BitVec 8))) (not (bvsgt (bvnot ((_ zero_extend 24) v_functionized3_~functionized3_localFunctionVar0_25)) ((_ sign_extend 24) ~var_1_11~0))))";
		final String expectedResultAsString = "(forall ((v_functionized3_~functionized3_localFunctionVar0_19 (_ BitVec 8))) (not (bvsgt (bvnot ((_ zero_extend 24) v_functionized3_~functionized3_localFunctionVar0_19)) ((_ sign_extend 24) ~var_1_11~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c918fdd5_7c428a7d_Treesizes_15_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (_ bv0 32) (select (store |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32))) (_ bv0 32)) (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv24 32)))))";
		final String expectedResultAsString = "(= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv24 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c95b8bbc_cdaff590_Treesizes_17_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_property_#t~ite142#1"),
		};
		final String formulaAsString = "(and (bvsle (_ bv128 32) |ULTIMATE.start_property_#t~ite142#1|) (exists ((v_arrayElimCell_80 (_ BitVec 32))) (and (bvsge v_arrayElimCell_80 (_ bv0 32)) (bvsge (bvadd |ULTIMATE.start_property_#t~ite142#1| (bvmul (bvneg v_arrayElimCell_80) (_ bv4294967295 32))) (_ bv4294967295 32)))))";
		final String expectedResultAsString = "(bvsle (_ bv128 32) |ULTIMATE.start_property_#t~ite142#1|)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_c9f91058_3f2d83b4_Treesizes_48_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_byte_cursor_right_trim_pred_~source.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) aws_byte_cursor_right_trim_pred_~source.base)) (select |#memory_int| (bvadd (_ bv2 32) aws_byte_cursor_right_trim_pred_~source.base))) (select |#memory_int| (bvadd (_ bv1 32) aws_byte_cursor_right_trim_pred_~source.base))) (select |#memory_int| aws_byte_cursor_right_trim_pred_~source.base))) (exists ((|v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14| (_ BitVec 32))) (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14|))) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_right_trim_pred_harness_~#cur~3#1.base_BEFORE_CALL_14|)))))";
		final String expectedResultAsString = "(= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) aws_byte_cursor_right_trim_pred_~source.base)) (select |#memory_int| (bvadd (_ bv2 32) aws_byte_cursor_right_trim_pred_~source.base))) (select |#memory_int| (bvadd (_ bv1 32) aws_byte_cursor_right_trim_pred_~source.base))) (select |#memory_int| aws_byte_cursor_right_trim_pred_~source.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ca535d50_48af4ce9_Treesizes_27_27() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_17 (_ BitVec 32))) (and (bvugt v_aws_linked_list_front_~list.base_BEFORE_CALL_17 (_ bv67 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_17))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv67 32)) (bvugt (bvadd (_ bv16 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_17) |#StackHeapBarrier|))) (bvult (bvadd (_ bv16 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_17) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_15 (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_15))) (and (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) v_aws_linked_list_front_~list.base_BEFORE_CALL_15))) (bvult .cse0 (_ bv2147483647 32)) (bvugt v_aws_linked_list_front_~list.base_BEFORE_CALL_15 (_ bv67 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv67 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cacd1c9e_23b282db_Treesizes_30_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~m_BEFORE_CALL_92| (_ BitVec 32))) (or (= (bvadd |mult_#in~n| |mult_#res|) (bvmul (_ bv6 32) |v_mult_#in~m_BEFORE_CALL_92|)) (not (= (bvmul |mult_#in~n| (_ bv6 32)) (bvmul (_ bv6 32) |v_mult_#in~m_BEFORE_CALL_92|))))) (or (= |mult_#in~m| (_ bv5 32)) (forall ((|v_mult_#in~m_BEFORE_CALL_92| (_ BitVec 32))) (= (bvadd |mult_#in~n| |mult_#res|) (bvmul (_ bv6 32) |v_mult_#in~m_BEFORE_CALL_92|)))))";
		final String expectedResultAsString = "(and (= |mult_#in~m| (_ bv5 32)) (= (bvmul |mult_#in~n| (_ bv5 32)) |mult_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cb4682b3_36443791_Treesizes_28_28() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base", "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var2_Pointer~0.base", "~double_Array_0_arraydouble_Array_0arrayVar0_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_211 (_ BitVec 32)) (v_ArrVal_210 (_ BitVec 32))) (= ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~double_Array_0_arraydouble_Array_0arrayVar0_Pointer~0.base v_ArrVal_211) (bvadd ~double_Array_0_arraydouble_Array_0arrayVar0_Pointer~0.base (_ bv4 32)) v_ArrVal_210) ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base))) ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~double_Array_0_arraydouble_Array_0arrayVar0_Pointer~0.base v_ArrVal_211) (bvadd ~double_Array_0_arraydouble_Array_0arrayVar0_Pointer~0.base (_ bv4 32)) v_ArrVal_210) ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var2_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_184 (_ BitVec 32)) (v_ArrVal_183 (_ BitVec 32))) (let ((.cse0 (store (store |#memory_int| ~double_Array_0_arraydouble_Array_0arrayVar0_Pointer~0.base v_ArrVal_183) (bvadd ~double_Array_0_arraydouble_Array_0arrayVar0_Pointer~0.base (_ bv4 32)) v_ArrVal_184))) (= ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var0_Pointer~0.base))) ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var2_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cbbd0017_a9b12eae_Treesizes_21_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (= |mult_#in~m| (_ bv2 32)) (forall ((|v_mult_#in~n_BEFORE_CALL_39| (_ BitVec 32))) (or (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_39|) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_39|) (bvmul |mult_#in~n| (_ bv3 32)))))))";
		final String expectedResultAsString = "(and (= (bvmul |mult_#in~n| (_ bv2 32)) |mult_#res|) (= |mult_#in~m| (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cc34b289_ba71640_Treesizes_22_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_6_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_216 (_ BitVec 32))) (= ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_216) ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv4294967264 32)))) ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_216) ~WrapperStruct00_var_1_1_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_186 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~WrapperStruct00_var_1_6_Pointer~0.base v_ArrVal_186))) (= ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ sign_extend 24) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv4294967264 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cca3fbdd_1561b686_Treesizes_37_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#y~0#1.base", "ULTIMATE.start_main_~#z~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= (bvadd (_ bv1 32) (select (store |#memory_int| |ULTIMATE.start_main_~#y~0#1.base| (bvadd (select |#memory_int| |ULTIMATE.start_main_~#y~0#1.base|) (_ bv1 32))) |ULTIMATE.start_main_~#z~0#1.base|)) (select (store (store |#memory_int| |ULTIMATE.start_main_~#y~0#1.base| (bvadd (select |#memory_int| |ULTIMATE.start_main_~#y~0#1.base|) (_ bv1 32))) |ULTIMATE.start_main_~#z~0#1.base| (bvadd (_ bv1 32) (select (store |#memory_int| |ULTIMATE.start_main_~#y~0#1.base| (bvadd (select |#memory_int| |ULTIMATE.start_main_~#y~0#1.base|) (_ bv1 32))) |ULTIMATE.start_main_~#z~0#1.base|))) |ULTIMATE.start_main_~#y~0#1.base|))";
		final String expectedResultAsString = "(= (select |#memory_int| |ULTIMATE.start_main_~#y~0#1.base|) (select |#memory_int| |ULTIMATE.start_main_~#z~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ccc09cc6_d6d6d67d_Treesizes_14_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_rend_~list#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_rend_~list#1.base|))) (exists ((|v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_27| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rend_harness_~#list~0#1.base_BEFORE_CALL_27|)))))";
		final String expectedResultAsString = "(not (= (_ bv0 32) (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_rend_~list#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cd3f9c40_97aabf0c_Treesizes_23_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_step_#t~mem35#1", "ULTIMATE.start_step_#t~mem36#1"),
		};
		final String formulaAsString = "(and (exists ((v_arrayElimCell_34 (_ BitVec 32))) (and (bvsle ((_ zero_extend 16) ((_ extract 15 0) v_arrayElimCell_34)) (_ bv32767 32)) (= |ULTIMATE.start_step_#t~mem36#1| ((_ extract 15 0) v_arrayElimCell_34)))) (exists ((v_arrayElimCell_33 (_ BitVec 32))) (and (bvsge ((_ zero_extend 16) ((_ extract 15 0) v_arrayElimCell_33)) (_ bv32767 32)) (= ((_ extract 15 0) v_arrayElimCell_33) |ULTIMATE.start_step_#t~mem35#1|))))";
		final String expectedResultAsString = "(and (exists ((v_arrayElimCell_23 (_ BitVec 32))) (let ((.cse0 ((_ extract 15 0) v_arrayElimCell_23))) (and (bvsle ((_ zero_extend 16) .cse0) (_ bv32767 32)) (= .cse0 |ULTIMATE.start_step_#t~mem36#1|)))) (exists ((v_arrayElimCell_22 (_ BitVec 32))) (let ((.cse1 ((_ extract 15 0) v_arrayElimCell_22))) (and (bvsge ((_ zero_extend 16) .cse1) (_ bv32767 32)) (= .cse1 |ULTIMATE.start_step_#t~mem35#1|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cde50bd6_91e6bc35_Treesizes_93_72() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (bvsge ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv13 32) |~#WrapperStruct00~0.base|)))) (_ bv127 32)) (bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv15 32) |~#WrapperStruct00~0.base|)))) (_ bv63 32)) (= ((_ sign_extend 24) ((_ extract 7 0) (bvadd (bvneg (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv14 32) |~#WrapperStruct00~0.base|)))) ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv15 32) |~#WrapperStruct00~0.base|)))))) ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv13 32) |~#WrapperStruct00~0.base|))))))) (select |#memory_int| (bvadd (_ bv10 32) |~#WrapperStruct00~0.base|))) (= (select |#memory_int| |~#WrapperStruct00~0.base|) ((_ sign_extend 16) ((_ zero_extend 8) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (bvadd (bvneg (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv14 32) |~#WrapperStruct00~0.base|)))) ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv15 32) |~#WrapperStruct00~0.base|)))))) ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv13 32) |~#WrapperStruct00~0.base|))))))))))) (bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv14 32) |~#WrapperStruct00~0.base|)))) (_ bv64 32)))";
		final String expectedResultAsString = "(let ((.cse2 ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv15 32) |~#WrapperStruct00~0.base|))))) (.cse1 ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv13 32) |~#WrapperStruct00~0.base|))))) (.cse0 (select |#memory_int| (bvadd (_ bv10 32) |~#WrapperStruct00~0.base|))) (.cse3 ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv14 32) |~#WrapperStruct00~0.base|)))))) (and (= (select |#memory_int| |~#WrapperStruct00~0.base|) ((_ sign_extend 16) ((_ zero_extend 8) ((_ extract 7 0) .cse0)))) (bvsge .cse1 (_ bv127 32)) (bvsle .cse2 (_ bv63 32)) (= ((_ sign_extend 24) ((_ extract 7 0) (bvadd (bvneg (bvadd .cse3 .cse2)) .cse1))) .cse0) (bvsle .cse3 (_ bv64 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ce71a7e8_b0e3b09d_Treesizes_14_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~sn~0#1"),
		};
		final String formulaAsString = "(or (= (_ bv0 32) |ULTIMATE.start_main_~sn~0#1|) (forall ((|ULTIMATE.start_main_~n~0#1| (_ BitVec 32))) (= (bvudiv (bvmul (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv1 32)) |ULTIMATE.start_main_~n~0#1|) (_ bv2 32)) |ULTIMATE.start_main_~sn~0#1|)))";
		final String expectedResultAsString = "(= (_ bv0 32) |ULTIMATE.start_main_~sn~0#1|)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cec390e4_e37273aa_Treesizes_138_97() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#float_Array_0~0.base", "~#BOOL_unsigned_char_Array_0~0.base", "~#unsigned_long_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_204 (_ BitVec 32))) (or (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_204) |~#BOOL_unsigned_char_Array_0~0.base|))) (forall ((v_ArrVal_206 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_204) (bvadd (_ bv3 32) |~#BOOL_unsigned_char_Array_0~0.base|) ((_ sign_extend 24) (_ bv0 8))) (bvadd |~#float_Array_0~0.base| (_ bv12 32)) v_ArrVal_206) |~#BOOL_unsigned_char_Array_0~0.base|))))))) (forall ((v_ArrVal_204 (_ BitVec 32))) (or (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_204) |~#BOOL_unsigned_char_Array_0~0.base|)))) (forall ((v_ArrVal_206 (_ BitVec 32))) (= ((_ extract 7 0) (select (store (store (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_204) (bvadd (_ bv3 32) |~#BOOL_unsigned_char_Array_0~0.base|) ((_ sign_extend 24) (_ bv1 8))) (bvadd |~#float_Array_0~0.base| (_ bv12 32)) v_ArrVal_206) |~#BOOL_unsigned_char_Array_0~0.base|)) (_ bv0 8))))) (forall ((v_ArrVal_204 (_ BitVec 32))) (or (forall ((v_ArrVal_206 (_ BitVec 32))) (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_204) (bvadd (_ bv3 32) |~#BOOL_unsigned_char_Array_0~0.base|) ((_ sign_extend 24) (_ bv0 8))) (bvadd |~#float_Array_0~0.base| (_ bv12 32)) v_ArrVal_206) (bvadd (_ bv3 32) |~#BOOL_unsigned_char_Array_0~0.base|)))))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_204) |~#BOOL_unsigned_char_Array_0~0.base|))))) (forall ((v_ArrVal_204 (_ BitVec 32))) (or (forall ((v_ArrVal_206 (_ BitVec 32))) (= (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_204) (bvadd (_ bv3 32) |~#BOOL_unsigned_char_Array_0~0.base|) ((_ sign_extend 24) (_ bv1 8))) (bvadd |~#float_Array_0~0.base| (_ bv12 32)) v_ArrVal_206) (bvadd (_ bv3 32) |~#BOOL_unsigned_char_Array_0~0.base|)))))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| |~#unsigned_long_int_Array_0~0.base| v_ArrVal_204) |~#BOOL_unsigned_char_Array_0~0.base|)))))))";
		final String expectedResultAsString = "(let ((.cse2 (bvadd |~#float_Array_0~0.base| (_ bv12 32))) (.cse3 (bvadd (_ bv3 32) |~#BOOL_unsigned_char_Array_0~0.base|)) (.cse0 (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| |~#BOOL_unsigned_char_Array_0~0.base|))))) (and (or .cse0 (let ((.cse1 (store |#memory_int| .cse3 ((_ sign_extend 24) (_ bv0 8))))) (and (forall ((v_ArrVal_206 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (select (store .cse1 .cse2 v_ArrVal_206) .cse3))) (_ bv0 32))) (forall ((v_ArrVal_206 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store .cse1 .cse2 v_ArrVal_206) |~#BOOL_unsigned_char_Array_0~0.base|)))))))) (or (let ((.cse4 (store |#memory_int| .cse3 ((_ sign_extend 24) (_ bv1 8))))) (and (forall ((v_ArrVal_206 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store .cse4 .cse2 v_ArrVal_206) |~#BOOL_unsigned_char_Array_0~0.base|)))) (forall ((v_ArrVal_206 (_ BitVec 32))) (= (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store .cse4 .cse2 v_ArrVal_206) .cse3))))))) (not .cse0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cf591bf3_c6d0182e_Treesizes_47_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_array_list_get_at_ptr_~list.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8428 32)) (bvugt (bvadd (_ bv20 32) aws_array_list_get_at_ptr_~list.base) |#StackHeapBarrier|))) (bvult (bvadd (_ bv20 32) aws_array_list_get_at_ptr_~list.base) (_ bv2147483647 32)) (exists ((v_aws_array_list_get_at_ptr_~list.base_BEFORE_CALL_3 (_ BitVec 32))) (and (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8428 32)) (bvugt (bvadd v_aws_array_list_get_at_ptr_~list.base_BEFORE_CALL_3 (_ bv20 32)) |#StackHeapBarrier|))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd v_aws_array_list_get_at_ptr_~list.base_BEFORE_CALL_3 (_ bv16 32)))) (bvult (bvadd v_aws_array_list_get_at_ptr_~list.base_BEFORE_CALL_3 (_ bv20 32)) (_ bv2147483647 32)))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv16 32) aws_array_list_get_at_ptr_~list.base))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv20 32) aws_array_list_get_at_ptr_~list.base))) (and (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8428 32)) (bvugt .cse0 |#StackHeapBarrier|))) (bvult .cse0 (_ bv2147483647 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv16 32) aws_array_list_get_at_ptr_~list.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cfb51705_dec98187_Treesizes_11_4() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem12#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_19 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_19))) (= ((_ extract 7 0) v_arrayElimCell_19) |ULTIMATE.start_step_#t~mem12#1|)))";
		final String expectedResultAsString = "(not (= (_ bv0 8) |ULTIMATE.start_step_#t~mem12#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_cff77705_a58e760a_Treesizes_9_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_array_eq_ignore_case_harness_~#old_byte_from_lhs~0#1.base", "ULTIMATE.start_aws_array_eq_ignore_case_harness_~lhs~0#1.base"),
		};
		final String formulaAsString = "(and (not (= |ULTIMATE.start_aws_array_eq_ignore_case_harness_~#old_byte_from_lhs~0#1.base| (_ bv0 32))) (not (= (_ bv0 32) |ULTIMATE.start_aws_array_eq_ignore_case_harness_~lhs~0#1.base|)))";
		final String expectedResultAsString = "(and (bvugt |ULTIMATE.start_aws_array_eq_ignore_case_harness_~#old_byte_from_lhs~0#1.base| (_ bv0 32)) (bvugt |ULTIMATE.start_aws_array_eq_ignore_case_harness_~lhs~0#1.base| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d0a7aeee_2aa1686e_Treesizes_13_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "ULTIMATE.start_main_~a~0#1", "ULTIMATE.start_main_~r~0#1", "ULTIMATE.start_main_~p~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 64) (bvadd (bvneg |ULTIMATE.start_main_~a~0#1|) (bvmul |ULTIMATE.start_main_~r~0#1| ((_ sign_extend 32) |ULTIMATE.start_main_~y~0#1|)) (bvmul |ULTIMATE.start_main_~p~0#1| ((_ sign_extend 32) |ULTIMATE.start_main_~x~0#1|))))";
		final String expectedResultAsString = "(= |ULTIMATE.start_main_~a~0#1| (bvadd (bvmul |ULTIMATE.start_main_~r~0#1| ((_ sign_extend 32) |ULTIMATE.start_main_~y~0#1|)) (bvmul |ULTIMATE.start_main_~p~0#1| ((_ sign_extend 32) |ULTIMATE.start_main_~x~0#1|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d125d5d5_88374fe7_Treesizes_13_13() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_15_Pointer~0.base", "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_186 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| (bvadd (_ bv30 32) |~#WrapperStruct00~0.base|) v_ArrVal_186) ~WrapperStruct00_var_1_15_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_165 (_ BitVec 32))) (not (= ((_ extract 7 0) (select (store |#memory_int| (bvadd (_ bv30 32) |~#WrapperStruct00~0.base|) v_ArrVal_165) ~WrapperStruct00_var_1_15_Pointer~0.base)) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d1e094df_a09759e0_Treesizes_47_47() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_9_Pointer~0.base", "~WrapperStruct00_var_1_10_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_188 (_ BitVec 32))) (not (fp.gt (fp ((_ extract 31 31) (select (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_188) ~WrapperStruct00_var_1_9_Pointer~0.base)) ((_ extract 30 23) (select (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_188) ~WrapperStruct00_var_1_9_Pointer~0.base)) ((_ extract 22 0) (select (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_188) ~WrapperStruct00_var_1_9_Pointer~0.base))) (fp ((_ extract 31 31) (select (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_188) ~WrapperStruct00_var_1_10_Pointer~0.base)) ((_ extract 30 23) (select (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_188) ~WrapperStruct00_var_1_10_Pointer~0.base)) ((_ extract 22 0) (select (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_188) ~WrapperStruct00_var_1_10_Pointer~0.base))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_162 (_ BitVec 32))) (not (let ((.cse1 (store |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_162))) (fp.gt (let ((.cse0 (select .cse1 ~WrapperStruct00_var_1_9_Pointer~0.base))) (fp ((_ extract 31 31) .cse0) ((_ extract 30 23) .cse0) ((_ extract 22 0) .cse0))) (let ((.cse2 (select .cse1 ~WrapperStruct00_var_1_10_Pointer~0.base))) (fp ((_ extract 31 31) .cse2) ((_ extract 30 23) .cse2) ((_ extract 22 0) .cse2)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d2064600_d27a02b7_Treesizes_11_4() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem91#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_49 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_49))) (= |ULTIMATE.start_property_#t~mem91#1| ((_ extract 7 0) v_arrayElimCell_49))))";
		final String expectedResultAsString = "(not (= |ULTIMATE.start_property_#t~mem91#1| (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d286f7d4_337cd651_Treesizes_60_55() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_maxpool_~window#1", "ULTIMATE.start_maxpool_~j~0#1", "ULTIMATE.start_maxpool_~i~0#1"),
		};
		final String formulaAsString = "(and (exists ((|ULTIMATE.start_maxpool_~stride#1| (_ BitVec 32))) (and (bvslt (bvadd |ULTIMATE.start_maxpool_~i~0#1| (bvmul |ULTIMATE.start_maxpool_~stride#1| (_ bv4294967295 32)) (_ bv3 32)) (bvadd |ULTIMATE.start_maxpool_~i~0#1| (bvmul |ULTIMATE.start_maxpool_~stride#1| (_ bv4294967295 32)) |ULTIMATE.start_maxpool_~window#1|)) (bvslt (bvadd |ULTIMATE.start_maxpool_~i~0#1| (bvmul |ULTIMATE.start_maxpool_~stride#1| (_ bv4294967295 32)) (_ bv1 32)) (bvadd |ULTIMATE.start_maxpool_~i~0#1| (bvmul |ULTIMATE.start_maxpool_~stride#1| (_ bv4294967295 32)) |ULTIMATE.start_maxpool_~window#1|)) (not (bvslt (bvadd |ULTIMATE.start_maxpool_~i~0#1| (bvmul |ULTIMATE.start_maxpool_~stride#1| (_ bv4294967295 32)) (_ bv4 32)) (bvadd |ULTIMATE.start_maxpool_~i~0#1| (bvmul |ULTIMATE.start_maxpool_~stride#1| (_ bv4294967295 32)) |ULTIMATE.start_maxpool_~window#1|))))) (bvslt |ULTIMATE.start_maxpool_~j~0#1| (bvadd |ULTIMATE.start_maxpool_~i~0#1| |ULTIMATE.start_maxpool_~window#1|)) (= |ULTIMATE.start_maxpool_~j~0#1| (bvadd |ULTIMATE.start_maxpool_~i~0#1| (_ bv2 32))) (bvslt (bvadd |ULTIMATE.start_maxpool_~i~0#1| (_ bv1 32)) (bvadd |ULTIMATE.start_maxpool_~i~0#1| |ULTIMATE.start_maxpool_~window#1|)))";
		final String expectedResultAsString = "(and (exists ((|ULTIMATE.start_maxpool_~stride#1| (_ BitVec 32))) (let ((.cse0 (bvmul |ULTIMATE.start_maxpool_~stride#1| (_ bv4294967295 32)))) (let ((.cse1 (bvadd |ULTIMATE.start_maxpool_~i~0#1| .cse0 |ULTIMATE.start_maxpool_~window#1|))) (and (bvslt (bvadd |ULTIMATE.start_maxpool_~i~0#1| .cse0 (_ bv3 32)) .cse1) (bvslt (bvadd |ULTIMATE.start_maxpool_~i~0#1| .cse0 (_ bv1 32)) .cse1) (not (bvslt (bvadd |ULTIMATE.start_maxpool_~i~0#1| .cse0 (_ bv4 32)) .cse1)))))) (= |ULTIMATE.start_maxpool_~j~0#1| (bvadd |ULTIMATE.start_maxpool_~i~0#1| (_ bv2 32))) (bvslt (bvadd |ULTIMATE.start_maxpool_~i~0#1| (_ bv1 32)) (bvadd |ULTIMATE.start_maxpool_~i~0#1| |ULTIMATE.start_maxpool_~window#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d2f7b251_9394f44f_Treesizes_4_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_#t~mem7#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_main_#t~mem7#1.base|))";
		final String expectedResultAsString = "(bvugt |ULTIMATE.start_main_#t~mem7#1.base| (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d3b1efd2_36a4a53e_Treesizes_22_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_14_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_150 (_ BitVec 32))) (= ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_150) ~WrapperStruct00_var_1_4_Pointer~0.base))) (_ bv4294967264 32)))) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_150) ~WrapperStruct00_var_1_1_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_124 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_124))) (= ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_4_Pointer~0.base))) (_ bv4294967264 32)))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d42c567b_3e97362d_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_front_~list#1.base_BEFORE_CALL_18| (_ BitVec 32))) (and (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_pop_front_~list#1.base_BEFORE_CALL_18|) (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_pop_front_~list#1.base_BEFORE_CALL_18|)) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_pop_front_~list#1.base_BEFORE_CALL_18|) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_pop_front_~list#1.base_BEFORE_CALL_18|) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv71 32))))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_pop_front_harness_~#list~0#1.base_BEFORE_CALL_19| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_pop_front_harness_~#list~0#1.base_BEFORE_CALL_19|))) (and (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv71 32)))) (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_pop_front_harness_~#list~0#1.base_BEFORE_CALL_19|) (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_linked_list_pop_front_harness_~#list~0#1.base_BEFORE_CALL_19|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d4c90144_9662a16e_Treesizes_16_8() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#in~n", "fibonacci_~n"),
		};
		final String formulaAsString = "(or (= (_ bv2 32) |fibonacci_#in~n|) (= (_ bv1 32) fibonacci_~n) (bvslt fibonacci_~n (_ bv1 32)) (not (bvslt (bvadd fibonacci_~n (_ bv4294967294 32)) (_ bv1 32))))";
		final String expectedResultAsString = "(or (= (_ bv2 32) |fibonacci_#in~n|) (not (= (_ bv2 32) fibonacci_~n)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d57def88_15896832_Treesizes_23_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem11#1", "ULTIMATE.start_step_#t~mem10#1"),
		};
		final String formulaAsString = "(and (exists ((v_arrayElimCell_11 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_11) |ULTIMATE.start_step_#t~mem11#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_11)) (_ bv127 32)))) (exists ((v_arrayElimCell_12 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_12) |ULTIMATE.start_step_#t~mem10#1|) (bvsge ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_12)) (_ bv127 32)))))";
		final String expectedResultAsString = "(and (exists ((v_arrayElimCell_7 (_ BitVec 32))) (let ((.cse0 ((_ extract 7 0) v_arrayElimCell_7))) (and (bvsge ((_ zero_extend 24) .cse0) (_ bv127 32)) (= |ULTIMATE.start_step_#t~mem10#1| .cse0)))) (exists ((v_arrayElimCell_6 (_ BitVec 32))) (let ((.cse1 ((_ extract 7 0) v_arrayElimCell_6))) (and (= .cse1 |ULTIMATE.start_step_#t~mem11#1|) (bvsle ((_ zero_extend 24) .cse1) (_ bv127 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d65640a9_a2888dc3_Treesizes_29_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#StackHeapBarrier", "ULTIMATE.start_main_~#s~0#1.base"),
		};
		final String formulaAsString = "(and (bvugt |ULTIMATE.start_main_~#s~0#1.base| |#StackHeapBarrier|) (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7| (_ BitVec 32))) (and (bvult (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7|) (_ bv2147483647 32)) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7| |#StackHeapBarrier|) (bvugt (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7|) |#StackHeapBarrier|))) (bvugt (bvadd (_ bv4 32) |ULTIMATE.start_main_~#s~0#1.base|) |#StackHeapBarrier|) (bvult (bvadd (_ bv4 32) |ULTIMATE.start_main_~#s~0#1.base|) (_ bv2147483647 32)))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv4 32) |ULTIMATE.start_main_~#s~0#1.base|))) (and (bvugt |ULTIMATE.start_main_~#s~0#1.base| |#StackHeapBarrier|) (bvugt .cse0 |#StackHeapBarrier|) (bvult .cse0 (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d712457d_32774b62_Treesizes_17_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_8~0", "~var_1_9~0", "~var_1_11~0", "~var_1_10~0"),
		};
		final String formulaAsString = "(and (not (= ~var_1_9~0 (_ bv0 8))) (not (= (_ bv0 8) ~var_1_10~0)) (not (= ~var_1_8~0 (_ bv0 8))) (not (= (_ bv0 8) ~var_1_11~0)))";
		final String expectedResultAsString = "(and (bvsge ((_ zero_extend 24) ~var_1_11~0) (_ bv1 32)) (bvsge ((_ zero_extend 24) ~var_1_10~0) (_ bv1 32)) (bvsge ((_ zero_extend 24) ~var_1_8~0) (_ bv1 32)) (bvsge ((_ zero_extend 24) ~var_1_9~0) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d7e37e6e_5ce9afc4_Treesizes_160_148() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_15_Pointer~0.base", "~WrapperStruct00_var_1_9_Pointer~0.base", "~WrapperStruct00_var_1_2_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ~WrapperStruct00_var_1_2_Pointer~0.base (_ bv54 32)) (= (_ bv62 32) ~WrapperStruct00_var_1_3_Pointer~0.base) (= ~WrapperStruct00_var_1_15_Pointer~0.base (_ bv97 32)) (exists ((|v_skolemized_q#valueAsBitvector_39| (_ BitVec 64))) (and (= ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_39|) (select |#memory_int| (_ bv62 32))) (= ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_39|) (select |#memory_int| (_ bv66 32))))) (= (_ bv88 32) ~WrapperStruct00_var_1_9_Pointer~0.base) (= (_ bv46 32) |~#WrapperStruct00~0.base|) (fp.geq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854776000.0)))) (exists ((|v_skolemized_q#valueAsBitvector_38| (_ BitVec 64))) (and (fp.leq (fp ((_ extract 63 63) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32)))) ((_ extract 62 52) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32)))) ((_ extract 51 0) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))) (fp.geq (fp ((_ extract 63 63) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32)))) ((_ extract 62 52) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32)))) ((_ extract 51 0) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|) (select |#memory_int| (_ bv54 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854776000.0)))) (= (select |#memory_int| (_ bv58 32)) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|)))) (fp.leq (fp ((_ extract 63 63) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)))) ((_ extract 62 52) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32)))) ((_ extract 51 0) (concat (select |#memory_int| (_ bv66 32)) (select |#memory_int| (_ bv62 32))))) ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))))";
		final String expectedResultAsString = "(let ((.cse3 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven (/ 1.0 100000000000000000000.0))))) (.cse4 ((_ to_fp 11 53) roundNearestTiesToEven (fp.neg ((_ to_fp 8 24) roundNearestTiesToEven 9223372036854776000.0))))) (and (exists ((|v_skolemized_q#valueAsBitvector_39| (_ BitVec 64))) (let ((.cse1 ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_39|)) (.cse0 ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_39|))) (let ((.cse2 (let ((.cse5 (concat .cse1 .cse0))) (fp ((_ extract 63 63) .cse5) ((_ extract 62 52) .cse5) ((_ extract 51 0) .cse5))))) (and (= .cse0 (select |#memory_int| (_ bv62 32))) (= .cse1 (select |#memory_int| (_ bv66 32))) (fp.leq .cse2 .cse3) (fp.geq .cse2 .cse4))))) (= ~WrapperStruct00_var_1_2_Pointer~0.base (_ bv54 32)) (= (_ bv62 32) ~WrapperStruct00_var_1_3_Pointer~0.base) (= ~WrapperStruct00_var_1_15_Pointer~0.base (_ bv97 32)) (= (_ bv88 32) ~WrapperStruct00_var_1_9_Pointer~0.base) (= (_ bv46 32) |~#WrapperStruct00~0.base|) (exists ((|v_skolemized_q#valueAsBitvector_38| (_ BitVec 64))) (let ((.cse7 ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_38|))) (let ((.cse6 (let ((.cse8 (concat .cse7 (select |#memory_int| (_ bv54 32))))) (fp ((_ extract 63 63) .cse8) ((_ extract 62 52) .cse8) ((_ extract 51 0) .cse8))))) (and (fp.leq .cse6 .cse3) (fp.geq .cse6 .cse4) (= (select |#memory_int| (_ bv58 32)) .cse7)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d88054d1_bd68a8c4_Treesizes_42_22() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_linked_list_insert_before_~before.base", "aws_linked_list_insert_before_~to_add.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (= aws_linked_list_insert_before_~to_add.base (bvadd (_ bv16 32) aws_linked_list_insert_before_~before.base)) (exists ((v_aws_linked_list_insert_before_~to_add.base_BEFORE_CALL_4 (_ BitVec 32))) (and (= (bvadd (_ bv8 32) (select |#memory_$Pointer$.base| (bvadd v_aws_linked_list_insert_before_~to_add.base_BEFORE_CALL_4 (_ bv4294967284 32)))) v_aws_linked_list_insert_before_~to_add.base_BEFORE_CALL_4) (= v_aws_linked_list_insert_before_~to_add.base_BEFORE_CALL_4 (bvadd (_ bv16 32) (select |#memory_$Pointer$.base| (bvadd v_aws_linked_list_insert_before_~to_add.base_BEFORE_CALL_4 (_ bv4294967288 32))))))) (= (bvadd (_ bv8 32) aws_linked_list_insert_before_~before.base) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) aws_linked_list_insert_before_~before.base))) (= (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) aws_linked_list_insert_before_~before.base)) aws_linked_list_insert_before_~before.base))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv8 32) aws_linked_list_insert_before_~before.base))) (and (= aws_linked_list_insert_before_~to_add.base (bvadd (_ bv16 32) aws_linked_list_insert_before_~before.base)) (= .cse0 (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) aws_linked_list_insert_before_~before.base))) (= (select |#memory_$Pointer$.base| .cse0) aws_linked_list_insert_before_~before.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_d8e11adc_97336b62_Treesizes_36_36() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_9_Pointer~0.base", "~var_1_13_Pointer~0.base", "~var_1_8_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_33 (_ BitVec 32)) (v_ArrVal_52 (_ BitVec 32))) (or (= ((_ sign_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~var_1_9_Pointer~0.base v_ArrVal_52) ~var_1_13_Pointer~0.base v_ArrVal_33) ~var_1_8_Pointer~0.base))) ((_ sign_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~var_1_9_Pointer~0.base v_ArrVal_52) ~var_1_13_Pointer~0.base v_ArrVal_33) ~var_1_1_Pointer~0.base)))) (not (bvslt (_ bv5 32) ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~var_1_9_Pointer~0.base v_ArrVal_52) ~var_1_1_Pointer~0.base)))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_32 (_ BitVec 32)) (v_ArrVal_33 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~var_1_9_Pointer~0.base v_ArrVal_32))) (or (not (bvslt (_ bv5 32) ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 ~var_1_1_Pointer~0.base))))) (let ((.cse1 (store .cse0 ~var_1_13_Pointer~0.base v_ArrVal_33))) (= ((_ sign_extend 24) ((_ extract 7 0) (select .cse1 ~var_1_1_Pointer~0.base))) ((_ sign_extend 24) ((_ extract 7 0) (select .cse1 ~var_1_8_Pointer~0.base))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_da0c24bf_99eb6f70_Treesizes_4_4() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_10~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_10~0))";
		final String expectedResultAsString = "(bvsge ((_ zero_extend 24) ~var_1_10~0) (_ bv1 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dac9142c_5e62b545_Treesizes_26_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_5_Pointer~0.base", "~var_1_3_Pointer~0.base", "~var_1_2_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_164 (_ BitVec 32))) (not (= (select (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_164) ~var_1_5_Pointer~0.base) (bvxor ((_ sign_extend 16) ((_ extract 15 0) (select (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_164) ~var_1_3_Pointer~0.base))) ((_ sign_extend 16) ((_ extract 15 0) (select (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_164) ~var_1_2_Pointer~0.base)))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_137 (_ BitVec 32))) (not (let ((.cse0 (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_137))) (= (bvxor ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 ~var_1_2_Pointer~0.base))) ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 ~var_1_3_Pointer~0.base)))) (select .cse0 ~var_1_5_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dafa7c2e_6b7be8f6_Treesizes_189_189() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_10_Pointer~0.base", "~var_1_8_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_84 (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_33| (_ BitVec 64))) (or (not (= (fp ((_ extract 63 63) |v_skolemized_q#valueAsBitvector_33|) ((_ extract 62 52) |v_skolemized_q#valueAsBitvector_33|) ((_ extract 51 0) |v_skolemized_q#valueAsBitvector_33|)) (fp ((_ extract 63 63) (concat (select (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_84) (bvadd (_ bv4 32) ~var_1_8_Pointer~0.base)) (select (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_84) ~var_1_8_Pointer~0.base))) ((_ extract 62 52) (concat (select (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_84) (bvadd (_ bv4 32) ~var_1_8_Pointer~0.base)) (select (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_84) ~var_1_8_Pointer~0.base))) ((_ extract 51 0) (concat (select (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_84) (bvadd (_ bv4 32) ~var_1_8_Pointer~0.base)) (select (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_84) ~var_1_8_Pointer~0.base)))))) (fp.eq (fp ((_ extract 63 63) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_33|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_33|))) ((_ extract 62 52) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_33|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_33|))) ((_ extract 51 0) (concat ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_33|) ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_33|)))) (fp ((_ extract 63 63) (concat (select (store (store (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_84) ~var_1_1_Pointer~0.base ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_33|)) (bvadd (_ bv4 32) ~var_1_1_Pointer~0.base) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_33|)) (bvadd (_ bv4 32) ~var_1_8_Pointer~0.base)) (select (store (store (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_84) ~var_1_1_Pointer~0.base ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_33|)) (bvadd (_ bv4 32) ~var_1_1_Pointer~0.base) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_33|)) ~var_1_8_Pointer~0.base))) ((_ extract 62 52) (concat (select (store (store (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_84) ~var_1_1_Pointer~0.base ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_33|)) (bvadd (_ bv4 32) ~var_1_1_Pointer~0.base) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_33|)) (bvadd (_ bv4 32) ~var_1_8_Pointer~0.base)) (select (store (store (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_84) ~var_1_1_Pointer~0.base ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_33|)) (bvadd (_ bv4 32) ~var_1_1_Pointer~0.base) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_33|)) ~var_1_8_Pointer~0.base))) ((_ extract 51 0) (concat (select (store (store (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_84) ~var_1_1_Pointer~0.base ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_33|)) (bvadd (_ bv4 32) ~var_1_1_Pointer~0.base) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_33|)) (bvadd (_ bv4 32) ~var_1_8_Pointer~0.base)) (select (store (store (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_84) ~var_1_1_Pointer~0.base ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_33|)) (bvadd (_ bv4 32) ~var_1_1_Pointer~0.base) ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_33|)) ~var_1_8_Pointer~0.base)))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_51 (_ BitVec 32)) (|v_skolemized_q#valueAsBitvector_33| (_ BitVec 64))) (let ((.cse5 (bvadd (_ bv4 32) ~var_1_8_Pointer~0.base)) (.cse6 (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_51))) (or (let ((.cse2 ((_ extract 31 0) |v_skolemized_q#valueAsBitvector_33|)) (.cse1 ((_ extract 63 32) |v_skolemized_q#valueAsBitvector_33|))) (fp.eq (let ((.cse0 (concat .cse1 .cse2))) (fp ((_ extract 63 63) .cse0) ((_ extract 62 52) .cse0) ((_ extract 51 0) .cse0))) (let ((.cse3 (let ((.cse4 (store (store .cse6 ~var_1_1_Pointer~0.base .cse2) (bvadd (_ bv4 32) ~var_1_1_Pointer~0.base) .cse1))) (concat (select .cse4 .cse5) (select .cse4 ~var_1_8_Pointer~0.base))))) (fp ((_ extract 63 63) .cse3) ((_ extract 62 52) .cse3) ((_ extract 51 0) .cse3))))) (not (= (let ((.cse7 (concat (select .cse6 .cse5) (select .cse6 ~var_1_8_Pointer~0.base)))) (fp ((_ extract 63 63) .cse7) ((_ extract 62 52) .cse7) ((_ extract 51 0) .cse7))) (fp ((_ extract 63 63) |v_skolemized_q#valueAsBitvector_33|) ((_ extract 62 52) |v_skolemized_q#valueAsBitvector_33|) ((_ extract 51 0) |v_skolemized_q#valueAsBitvector_33|)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dbe8ceb8_901bb2b6_Treesizes_30_30() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_property_#t~mem87#1", "ULTIMATE.start_property_#t~mem86#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_36 (_ BitVec 32)) (v_arrayElimCell_35 (_ BitVec 32)) (|v_ULTIMATE.start_step_#t~mem13#1_21| (_ BitVec 16))) (and (= |ULTIMATE.start_property_#t~mem87#1| ((_ extract 15 0) v_arrayElimCell_35)) (not (bvslt (bvmul ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_36)) ((_ sign_extend 16) ((_ extract 15 0) ((_ sign_extend 16) (_ bv32 16))))) ((_ sign_extend 16) |v_ULTIMATE.start_step_#t~mem13#1_21|))) (not (bvsgt ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_36)) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_35)))) (= |ULTIMATE.start_property_#t~mem86#1| ((_ extract 15 0) v_arrayElimCell_36))))";
		final String expectedResultAsString = "(exists ((v_arrayElimCell_27 (_ BitVec 32)) (|v_ULTIMATE.start_step_#t~mem13#1_21| (_ BitVec 16)) (v_arrayElimCell_28 (_ BitVec 32))) (let ((.cse2 ((_ extract 15 0) v_arrayElimCell_28))) (let ((.cse1 ((_ sign_extend 16) .cse2)) (.cse0 ((_ extract 15 0) v_arrayElimCell_27))) (and (= |ULTIMATE.start_property_#t~mem87#1| .cse0) (not (bvslt (bvmul .cse1 ((_ sign_extend 16) ((_ extract 15 0) ((_ sign_extend 16) (_ bv32 16))))) ((_ sign_extend 16) |v_ULTIMATE.start_step_#t~mem13#1_21|))) (= |ULTIMATE.start_property_#t~mem86#1| .cse2) (not (bvsgt .cse1 ((_ sign_extend 16) .cse0)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dbebc89_bf51f116_Treesizes_59_37() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var4_Pointer~0.base", "~#BOOL_unsigned_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_37 (_ BitVec 32))) (or (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_37) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)))) (= (_ bv0 8) ((_ extract 7 0) (select (store (store |#memory_int| (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_37) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var4_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base))))) (forall ((v_ArrVal_37 (_ BitVec 32))) (or (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_37) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store |#memory_int| (bvadd (_ bv2 32) |~#BOOL_unsigned_char_Array_0~0.base|) v_ArrVal_37) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var4_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)))))))";
		final String expectedResultAsString = "(let ((.cse0 (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base))))) (and (or (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var4_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base))) (not .cse0)) (or (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var4_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)))) .cse0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dc6f834c_d18c16f3_Treesizes_17_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_property_#t~mem90#1", "ULTIMATE.start_property_#t~mem89#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_31 (_ BitVec 32)) (v_arrayElimCell_30 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem90#1| ((_ extract 15 0) v_arrayElimCell_30)) (bvsgt ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_31)) ((_ sign_extend 16) ((_ extract 15 0) v_arrayElimCell_30))) (= |ULTIMATE.start_property_#t~mem89#1| ((_ extract 15 0) v_arrayElimCell_31))))";
		final String expectedResultAsString = "(exists ((v_arrayElimCell_27 (_ BitVec 32)) (v_arrayElimCell_26 (_ BitVec 32))) (let ((.cse1 ((_ extract 15 0) v_arrayElimCell_27)) (.cse0 ((_ extract 15 0) v_arrayElimCell_26))) (and (= |ULTIMATE.start_property_#t~mem90#1| .cse0) (= |ULTIMATE.start_property_#t~mem89#1| .cse1) (bvsgt ((_ sign_extend 16) .cse1) ((_ sign_extend 16) .cse0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dd286520_92c9370b_Treesizes_36_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#float_Array_0~0.base", "~#signed_short_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_65 (_ BitVec 32)) (v_ArrVal_66 (_ BitVec 32))) (bvsgt ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_short_int_Array_0~0.base|) v_ArrVal_65) (bvadd |~#float_Array_0~0.base| (_ bv4 32)) v_ArrVal_66) (bvadd (_ bv6 32) |~#signed_short_int_Array_0~0.base|)))) ((_ sign_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| (bvadd (_ bv8 32) |~#signed_short_int_Array_0~0.base|) v_ArrVal_65) (bvadd |~#float_Array_0~0.base| (_ bv4 32)) v_ArrVal_66) (bvadd (_ bv4 32) |~#signed_short_int_Array_0~0.base|))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_66 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| (bvadd |~#float_Array_0~0.base| (_ bv4 32)) v_ArrVal_66))) (bvsgt ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 (bvadd (_ bv6 32) |~#signed_short_int_Array_0~0.base|)))) ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 (bvadd (_ bv4 32) |~#signed_short_int_Array_0~0.base|)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_dda4f0ae_c0134332_Treesizes_13_4() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~k~0#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_8 (_ BitVec 32))) (= (_ bv0 32) (bvneg (bvadd (bvmul (_ bv4294967295 32) (bvneg v_arrayElimCell_8)) |ULTIMATE.start_main_~k~0#1| (bvmul v_arrayElimCell_8 (_ bv4294967295 32))))))";
		final String expectedResultAsString = "(= (_ bv0 32) (bvneg |ULTIMATE.start_main_~k~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_de039_1f7737ca_Treesizes_17_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_ring_buffer_acquire_up_to_harness_~#buf~3#1.base_BEFORE_CALL_49| (_ BitVec 32))) (and (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_ring_buffer_acquire_up_to_harness_~#buf~3#1.base_BEFORE_CALL_49|) (_ bv2147483647 32)) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_ring_buffer_acquire_up_to_harness_~#buf~3#1.base_BEFORE_CALL_49|)) (_ bv0 32)) (bvult |v_ULTIMATE.start_aws_ring_buffer_acquire_up_to_harness_~#buf~3#1.base_BEFORE_CALL_49| (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_ring_buffer_acquire_up_to_harness_~#buf~3#1.base_BEFORE_CALL_47| (_ BitVec 32))) (and (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_ring_buffer_acquire_up_to_harness_~#buf~3#1.base_BEFORE_CALL_47|)) (_ bv0 32)) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_ring_buffer_acquire_up_to_harness_~#buf~3#1.base_BEFORE_CALL_47|) (_ bv2147483647 32)) (bvult |v_ULTIMATE.start_aws_ring_buffer_acquire_up_to_harness_~#buf~3#1.base_BEFORE_CALL_47| (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_de549cde_c3e6ab58_Treesizes_47_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_array_list_push_back_~list#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (bvult (bvadd |ULTIMATE.start_aws_array_list_push_back_~list#1.base| (_ bv20 32)) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt (bvadd |ULTIMATE.start_aws_array_list_push_back_~list#1.base| (_ bv20 32)) |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8427 32)))) (= (select |#memory_$Pointer$.base| (bvadd |ULTIMATE.start_aws_array_list_push_back_~list#1.base| (_ bv16 32))) (_ bv0 32)) (exists ((|v_ULTIMATE.start_aws_array_list_push_back_~list#1.base_BEFORE_CALL_7| (_ BitVec 32))) (and (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_array_list_push_back_~list#1.base_BEFORE_CALL_7|))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8427 32)) (bvugt (bvadd (_ bv20 32) |v_ULTIMATE.start_aws_array_list_push_back_~list#1.base_BEFORE_CALL_7|) |#StackHeapBarrier|))) (bvult (bvadd (_ bv20 32) |v_ULTIMATE.start_aws_array_list_push_back_~list#1.base_BEFORE_CALL_7|) (_ bv2147483647 32)))))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd |ULTIMATE.start_aws_array_list_push_back_~list#1.base| (_ bv20 32)))) (and (bvult .cse0 (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8427 32)))) (= (select |#memory_$Pointer$.base| (bvadd |ULTIMATE.start_aws_array_list_push_back_~list#1.base| (_ bv16 32))) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_df2fdbe6_43d884af_Treesizes_35_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#StackHeapBarrier", "ULTIMATE.start_main_~#s~0#1.base", "ULTIMATE.start_sll_create_~data#1", "ULTIMATE.start_main_~data~0#1"),
		};
		final String formulaAsString = "(and (= (_ bv1 32) |ULTIMATE.start_sll_create_~data#1|) (bvugt |ULTIMATE.start_main_~#s~0#1.base| |#StackHeapBarrier|) (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7| (_ BitVec 32))) (and (bvult (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7|) (_ bv2147483647 32)) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7| |#StackHeapBarrier|) (bvugt (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_7|) |#StackHeapBarrier|))) (bvugt (bvadd (_ bv4 32) |ULTIMATE.start_main_~#s~0#1.base|) |#StackHeapBarrier|) (bvult (bvadd (_ bv4 32) |ULTIMATE.start_main_~#s~0#1.base|) (_ bv2147483647 32)) (= |ULTIMATE.start_main_~data~0#1| (_ bv1 32)))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv4 32) |ULTIMATE.start_main_~#s~0#1.base|))) (and (= (_ bv1 32) |ULTIMATE.start_sll_create_~data#1|) (bvugt |ULTIMATE.start_main_~#s~0#1.base| |#StackHeapBarrier|) (bvugt .cse0 |#StackHeapBarrier|) (bvult .cse0 (_ bv2147483647 32)) (= |ULTIMATE.start_main_~data~0#1| (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_df5be27d_5a315c46_Treesizes_4_4() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_5~0"),
		};
		final String formulaAsString = "(not (= ~var_1_5~0 (_ bv0 8)))";
		final String expectedResultAsString = "(bvsge ((_ zero_extend 24) ~var_1_5~0) (_ bv1 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e0000ab7_dddc9184_Treesizes_48_48() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort16, "ULTIMATE.start_step_~stepLocal_0~0#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#unsigned_short_int_Array_0~0.base", "~#float_Array_0~0.base", "~#signed_short_int_Array_0~0.base", "~#unsigned_long_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(or (forall ((v_ArrVal_119 (_ BitVec 32)) (v_ArrVal_148 (_ BitVec 32)) (v_ArrVal_120 (_ BitVec 32))) (= ((_ sign_extend 16) ((_ extract 15 0) (select (store (store (store |#memory_int| (bvadd |~#float_Array_0~0.base| (_ bv12 32)) v_ArrVal_148) |~#unsigned_long_int_Array_0~0.base| v_ArrVal_119) (bvadd (_ bv6 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_120) (bvadd (_ bv8 32) |~#signed_short_int_Array_0~0.base|)))) ((_ sign_extend 16) ((_ extract 15 0) (select (store (store (store |#memory_int| (bvadd |~#float_Array_0~0.base| (_ bv12 32)) v_ArrVal_148) |~#unsigned_long_int_Array_0~0.base| v_ArrVal_119) (bvadd (_ bv6 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_120) (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|)))))) (not (bvsgt ((_ sign_extend 16) |ULTIMATE.start_step_~stepLocal_0~0#1|) (_ bv2 32))))";
		final String expectedResultAsString = "(or (not (bvsgt ((_ sign_extend 16) |ULTIMATE.start_step_~stepLocal_0~0#1|) (_ bv2 32))) (forall ((v_ArrVal_119 (_ BitVec 32)) (v_ArrVal_118 (_ BitVec 32)) (v_ArrVal_120 (_ BitVec 32))) (let ((.cse0 (store (store (store |#memory_int| (bvadd |~#float_Array_0~0.base| (_ bv12 32)) v_ArrVal_118) |~#unsigned_long_int_Array_0~0.base| v_ArrVal_119) (bvadd (_ bv6 32) |~#unsigned_short_int_Array_0~0.base|) v_ArrVal_120))) (= ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 (bvadd (_ bv2 32) |~#signed_short_int_Array_0~0.base|)))) ((_ sign_extend 16) ((_ extract 15 0) (select .cse0 (bvadd (_ bv8 32) |~#signed_short_int_Array_0~0.base|))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e088960e_6e62afd5_Treesizes_21_21() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_15_Pointer~0.base", "~WrapperStruct00_var_1_14_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_238 (_ BitVec 32)) (v_ArrVal_212 (_ BitVec 32)) (v_ArrVal_211 (_ BitVec 32)) (v_ArrVal_210 (_ BitVec 32))) (not (bvslt ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_238) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_211) ~WrapperStruct00_var_1_15_Pointer~0.base v_ArrVal_210) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_212) ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv1 32))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_209 (_ BitVec 32)) (v_ArrVal_212 (_ BitVec 32)) (v_ArrVal_211 (_ BitVec 32)) (v_ArrVal_210 (_ BitVec 32))) (not (bvslt ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_209) ~WrapperStruct00_var_1_14_Pointer~0.base v_ArrVal_211) ~WrapperStruct00_var_1_15_Pointer~0.base v_ArrVal_210) ~WrapperStruct00_var_1_4_Pointer~0.base v_ArrVal_212) ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e116b1b5_cc91df8_Treesizes_15_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~0#1.base", "ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~c_str~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~0#1.base|)) (bvugt |ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~c_str~0#1.base| (_ bv0 32)) (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~0#1.base_BEFORE_CALL_21| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~0#1.base_BEFORE_CALL_21|))))";
		final String expectedResultAsString = "(and (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~0#1.base|)) (bvugt |ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~c_str~0#1.base| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e211589b_c4e401b7_Treesizes_18_18() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_13_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_5_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_131 (_ BitVec 32))) (= ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_131) ~WrapperStruct00_var_1_5_Pointer~0.base))) ((_ sign_extend 24) ((_ extract 7 0) (select (store |#memory_int| ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_131) ~WrapperStruct00_var_1_1_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_101 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_101))) (= ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_5_Pointer~0.base))) ((_ sign_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e2279789_f4b8ac23_Treesizes_51_37() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#var_1_9~0.base", "~var_1_1_Pointer~0.base", "~var_1_7_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_36 (_ BitVec 32))) (or (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store |#memory_int| |~#var_1_9~0.base| v_ArrVal_36) ~var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~var_1_7_Pointer~0.base)))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| |~#var_1_9~0.base| v_ArrVal_36) ~var_1_7_Pointer~0.base))))) (forall ((v_ArrVal_36 (_ BitVec 32))) (or (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| |~#var_1_9~0.base| v_ArrVal_36) ~var_1_7_Pointer~0.base)))) (= ((_ extract 7 0) (select (store (store |#memory_int| |~#var_1_9~0.base| v_ArrVal_36) ~var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~var_1_7_Pointer~0.base)) (_ bv0 8)))))";
		final String expectedResultAsString = "(let ((.cse0 (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| ~var_1_7_Pointer~0.base))))) (and (or (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~var_1_7_Pointer~0.base)))) .cse0) (or (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_1_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~var_1_7_Pointer~0.base))) (not .cse0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e2e86308_e1cfad54_Treesizes_114_59() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_array_list_init_static_~item_size#1", "ULTIMATE.start_aws_array_list_init_static_~list#1.base", "#StackAllocations"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (bvugt |ULTIMATE.start_aws_array_list_init_static_~item_size#1| (_ bv0 32)) (exists ((|ULTIMATE.start_aws_array_list_init_static_~item_count#1| (_ BitVec 32))) (and (= (select |#memory_int| (bvadd (_ bv7 32) |ULTIMATE.start_aws_array_list_init_static_~list#1.base|)) ((_ extract 31 24) (bvmul |ULTIMATE.start_aws_array_list_init_static_~item_size#1| |ULTIMATE.start_aws_array_list_init_static_~item_count#1|))) (= (select |#memory_int| (bvadd (_ bv6 32) |ULTIMATE.start_aws_array_list_init_static_~list#1.base|)) ((_ extract 23 16) (bvmul |ULTIMATE.start_aws_array_list_init_static_~item_size#1| |ULTIMATE.start_aws_array_list_init_static_~item_count#1|))) (bvugt |ULTIMATE.start_aws_array_list_init_static_~item_count#1| (_ bv0 32)) (bvule (bvmul ((_ zero_extend 32) |ULTIMATE.start_aws_array_list_init_static_~item_size#1|) ((_ zero_extend 32) |ULTIMATE.start_aws_array_list_init_static_~item_count#1|)) (_ bv4294967295 64)) (= ((_ extract 7 0) (bvmul |ULTIMATE.start_aws_array_list_init_static_~item_size#1| |ULTIMATE.start_aws_array_list_init_static_~item_count#1|)) (select |#memory_int| (bvadd (_ bv4 32) |ULTIMATE.start_aws_array_list_init_static_~list#1.base|))) (= ((_ extract 15 8) (bvmul |ULTIMATE.start_aws_array_list_init_static_~item_size#1| |ULTIMATE.start_aws_array_list_init_static_~item_count#1|)) (select |#memory_int| (bvadd (_ bv5 32) |ULTIMATE.start_aws_array_list_init_static_~list#1.base|))))) (bvult |#StackAllocations| (_ bv2147483647 32)) (exists ((|v_ULTIMATE.start_aws_array_list_init_static_~list#1.base_BEFORE_CALL_14| (_ BitVec 32)) (|ULTIMATE.start_aws_array_list_init_static_~item_count#1| (_ BitVec 32)) (|v_ULTIMATE.start_aws_array_list_init_static_~item_size#1_BEFORE_CALL_2| (_ BitVec 32))) (and (bvugt |v_ULTIMATE.start_aws_array_list_init_static_~item_size#1_BEFORE_CALL_2| (_ bv0 32)) (= (select |#memory_int| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_array_list_init_static_~list#1.base_BEFORE_CALL_14|)) ((_ extract 7 0) (bvmul |v_ULTIMATE.start_aws_array_list_init_static_~item_size#1_BEFORE_CALL_2| |ULTIMATE.start_aws_array_list_init_static_~item_count#1|))) (bvule (bvmul ((_ zero_extend 32) |ULTIMATE.start_aws_array_list_init_static_~item_count#1|) ((_ zero_extend 32) |v_ULTIMATE.start_aws_array_list_init_static_~item_size#1_BEFORE_CALL_2|)) (_ bv4294967295 64)) (= (select |#memory_int| (bvadd (_ bv7 32) |v_ULTIMATE.start_aws_array_list_init_static_~list#1.base_BEFORE_CALL_14|)) ((_ extract 31 24) (bvmul |v_ULTIMATE.start_aws_array_list_init_static_~item_size#1_BEFORE_CALL_2| |ULTIMATE.start_aws_array_list_init_static_~item_count#1|))) (= (select |#memory_int| (bvadd (_ bv5 32) |v_ULTIMATE.start_aws_array_list_init_static_~list#1.base_BEFORE_CALL_14|)) ((_ extract 15 8) (bvmul |v_ULTIMATE.start_aws_array_list_init_static_~item_size#1_BEFORE_CALL_2| |ULTIMATE.start_aws_array_list_init_static_~item_count#1|))) (bvugt |ULTIMATE.start_aws_array_list_init_static_~item_count#1| (_ bv0 32)) (= ((_ extract 23 16) (bvmul |v_ULTIMATE.start_aws_array_list_init_static_~item_size#1_BEFORE_CALL_2| |ULTIMATE.start_aws_array_list_init_static_~item_count#1|)) (select |#memory_int| (bvadd (_ bv6 32) |v_ULTIMATE.start_aws_array_list_init_static_~list#1.base_BEFORE_CALL_14|))))))";
		final String expectedResultAsString = "(and (bvugt |ULTIMATE.start_aws_array_list_init_static_~item_size#1| (_ bv0 32)) (exists ((|ULTIMATE.start_aws_array_list_init_static_~item_count#1| (_ BitVec 32))) (let ((.cse0 (bvmul |ULTIMATE.start_aws_array_list_init_static_~item_size#1| |ULTIMATE.start_aws_array_list_init_static_~item_count#1|))) (and (= (select |#memory_int| (bvadd (_ bv7 32) |ULTIMATE.start_aws_array_list_init_static_~list#1.base|)) ((_ extract 31 24) .cse0)) (= (select |#memory_int| (bvadd (_ bv6 32) |ULTIMATE.start_aws_array_list_init_static_~list#1.base|)) ((_ extract 23 16) .cse0)) (bvugt |ULTIMATE.start_aws_array_list_init_static_~item_count#1| (_ bv0 32)) (bvule (bvmul ((_ zero_extend 32) |ULTIMATE.start_aws_array_list_init_static_~item_size#1|) ((_ zero_extend 32) |ULTIMATE.start_aws_array_list_init_static_~item_count#1|)) (_ bv4294967295 64)) (= ((_ extract 7 0) .cse0) (select |#memory_int| (bvadd (_ bv4 32) |ULTIMATE.start_aws_array_list_init_static_~list#1.base|))) (= ((_ extract 15 8) .cse0) (select |#memory_int| (bvadd (_ bv5 32) |ULTIMATE.start_aws_array_list_init_static_~list#1.base|)))))) (bvult |#StackAllocations| (_ bv2147483647 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e377dfad_96c934a1_Treesizes_95_95() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_6_Pointer~0.base", "~WrapperStruct00_var_1_12_Pointer~0.base", "~WrapperStruct00_var_1_7_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_5_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base", "~WrapperStruct00_var_1_10_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_53 (_ BitVec 32)) (v_ArrVal_54 (_ BitVec 32)) (v_ArrVal_55 (_ BitVec 32)) (v_ArrVal_73 (_ BitVec 32))) (or (bvsle ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_73) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_53) ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_54) ~WrapperStruct00_var_1_7_Pointer~0.base v_ArrVal_55) ~WrapperStruct00_var_1_4_Pointer~0.base))) (bvadd (bvneg ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_73) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_53) ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_54) ~WrapperStruct00_var_1_7_Pointer~0.base v_ArrVal_55) ~WrapperStruct00_var_1_6_Pointer~0.base)))) (_ bv4294967294 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_73) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_53) ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_54) ~WrapperStruct00_var_1_7_Pointer~0.base v_ArrVal_55) ~WrapperStruct00_var_1_5_Pointer~0.base))))) (not (bvsle ((_ zero_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_73) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_53) ~WrapperStruct00_var_1_4_Pointer~0.base))) (bvadd (bvneg ((_ zero_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_73) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_53) ~WrapperStruct00_var_1_6_Pointer~0.base)))) (_ bv4294967294 32) ((_ zero_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_73) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_53) ~WrapperStruct00_var_1_5_Pointer~0.base))))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_53 (_ BitVec 32)) (v_ArrVal_54 (_ BitVec 32)) (v_ArrVal_55 (_ BitVec 32)) (v_ArrVal_52 (_ BitVec 32))) (let ((.cse1 (store (store |#memory_int| ~WrapperStruct00_var_1_10_Pointer~0.base v_ArrVal_52) ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_53))) (or (let ((.cse0 (store (store .cse1 ~WrapperStruct00_var_1_1_Pointer~0.base v_ArrVal_54) ~WrapperStruct00_var_1_7_Pointer~0.base v_ArrVal_55))) (bvsle ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_4_Pointer~0.base))) (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_5_Pointer~0.base))) (_ bv4294967294 32) (bvneg ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_6_Pointer~0.base))))))) (not (bvsle ((_ zero_extend 24) ((_ extract 7 0) (select .cse1 ~WrapperStruct00_var_1_4_Pointer~0.base))) (bvadd (bvneg ((_ zero_extend 24) ((_ extract 7 0) (select .cse1 ~WrapperStruct00_var_1_6_Pointer~0.base)))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse1 ~WrapperStruct00_var_1_5_Pointer~0.base))) (_ bv4294967294 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e4358cf_662aba8f_Treesizes_80_78() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#StackHeapBarrier", "#HeapAllocations", "node_create_~data#1", "node_create_~temp~0#1.base", "node_create_#in~data#1", "old(#HeapAllocations)"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base", "old(#memory_$Pointer$.base)"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_dll_circular_prepend_~head#1.base_BEFORE_CALL_3| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_dll_circular_prepend_~head#1.base_BEFORE_CALL_3| (_ bv4 32)) (_ bv2147483647 32)) (bvugt (bvadd |v_ULTIMATE.start_dll_circular_prepend_~head#1.base_BEFORE_CALL_3| (_ bv4 32)) |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_dll_circular_prepend_~head#1.base_BEFORE_CALL_3| |#StackHeapBarrier|))) (= (bvadd |old(#HeapAllocations)| (_ bv12 32)) |#HeapAllocations|) (exists ((v_arrayElimIndex_1 (_ BitVec 32))) (and (bvult (bvadd (_ bv8 32) v_arrayElimIndex_1) |#StackHeapBarrier|) (bvult (bvadd v_arrayElimIndex_1 (_ bv4294967292 32)) |#StackHeapBarrier|))) (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_5| (_ BitVec 32))) (and (bvult (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_5|) (_ bv2147483647 32)) (bvugt (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_5|) |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_5| |#StackHeapBarrier|))) (= |#HeapAllocations| (bvadd (_ bv12 32) |node_create_~temp~0#1.base|)) (= |node_create_#in~data#1| |node_create_~data#1|) (bvult |node_create_~temp~0#1.base| |#StackHeapBarrier|) (= |old(#memory_$Pointer$.base)| |#memory_$Pointer$.base|) (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_6| (_ BitVec 32))) (and (bvult (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_6|) (_ bv2147483647 32)) (bvugt (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_6|) |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_6| |#StackHeapBarrier|))) (bvult |#HeapAllocations| |#StackHeapBarrier|))";
		final String expectedResultAsString = "(and (exists ((|v_ULTIMATE.start_dll_circular_prepend_~head#1.base_BEFORE_CALL_3| (_ BitVec 32))) (let ((.cse0 (bvadd |v_ULTIMATE.start_dll_circular_prepend_~head#1.base_BEFORE_CALL_3| (_ bv4 32)))) (and (bvult .cse0 (_ bv2147483647 32)) (bvugt .cse0 |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_dll_circular_prepend_~head#1.base_BEFORE_CALL_3| |#StackHeapBarrier|)))) (= (bvadd |old(#HeapAllocations)| (_ bv12 32)) |#HeapAllocations|) (= |old(#HeapAllocations)| |node_create_~temp~0#1.base|) (exists ((v_arrayElimIndex_1 (_ BitVec 32))) (and (bvult (bvadd (_ bv8 32) v_arrayElimIndex_1) |#StackHeapBarrier|) (bvult (bvadd v_arrayElimIndex_1 (_ bv4294967292 32)) |#StackHeapBarrier|))) (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_5| (_ BitVec 32))) (let ((.cse1 (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_5|))) (and (bvult .cse1 (_ bv2147483647 32)) (bvugt .cse1 |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_5| |#StackHeapBarrier|)))) (= |node_create_#in~data#1| |node_create_~data#1|) (bvult |node_create_~temp~0#1.base| |#StackHeapBarrier|) (= |old(#memory_$Pointer$.base)| |#memory_$Pointer$.base|) (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_6| (_ BitVec 32))) (let ((.cse2 (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_6|))) (and (bvult .cse2 (_ bv2147483647 32)) (bvugt .cse2 |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_6| |#StackHeapBarrier|)))) (bvult |#HeapAllocations| |#StackHeapBarrier|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e4cdf6d_49a4afe2_Treesizes_23_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~s2s1_new~0", "~s1p_new~0", "~s1s1_new~0", "~nomsg~0"),
		};
		final String formulaAsString = "(or (= ((_ sign_extend 24) ~s1p_new~0) (_ bv1 32)) (not (= ((_ sign_extend 24) ~s2s1_new~0) ((_ sign_extend 24) ~s1s1_new~0))) (= ((_ sign_extend 24) ~s1p_new~0) ((_ sign_extend 24) ~nomsg~0)) (forall ((|ULTIMATE.start_Pendulum_prism_task_each_pals_period_~side1~2#1| (_ BitVec 8))) (not (= ((_ sign_extend 24) ~nomsg~0) ((_ sign_extend 24) |ULTIMATE.start_Pendulum_prism_task_each_pals_period_~side1~2#1|)))))";
		final String expectedResultAsString = "(let ((.cse0 ((_ sign_extend 24) ~s1p_new~0))) (or (= .cse0 (_ bv1 32)) (not (= ((_ sign_extend 24) ~s2s1_new~0) ((_ sign_extend 24) ~s1s1_new~0))) (= .cse0 ((_ sign_extend 24) ~nomsg~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e5153240_20d28759_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_dynamic_~to#1.base_BEFORE_CALL_2| (_ BitVec 32))) (and (not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_buf_append_dynamic_~to#1.base_BEFORE_CALL_2|)))) (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_append_dynamic_~to#1.base_BEFORE_CALL_2|) (_ bv8686 32)) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_append_dynamic_~to#1.base_BEFORE_CALL_2|) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#to~0#1.base_BEFORE_CALL_19| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#to~0#1.base_BEFORE_CALL_19|))) (and (bvult .cse0 (_ bv2147483647 32)) (bvugt .cse0 (_ bv8686 32)) (not (= (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#to~0#1.base_BEFORE_CALL_19|)) (_ bv0 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e5a2a9da_d2645228_Treesizes_6_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_19~0"),
		};
		final String formulaAsString = "(forall ((~var_1_33~0 (_ BitVec 16))) (not (bvult ((_ zero_extend 16) ~var_1_33~0) ~var_1_19~0)))";
		final String expectedResultAsString = "(= (_ bv0 32) ~var_1_19~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e5f553c6_55103b5d_Treesizes_116_48() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#a~0#1.base", "ULTIMATE.start_main_~i~0#1"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|ULTIMATE.start_main_~j~0#1| (_ BitVec 32))) (and (bvslt |ULTIMATE.start_main_~j~0#1| (_ bv10000 32)) (bvslt (bvadd (select |#memory_int| (bvadd |ULTIMATE.start_main_~#a~0#1.base| (_ bv4 32))) (_ bv4294967295 32) (bvmul |ULTIMATE.start_main_~j~0#1| (_ bv4294967295 32))) (_ bv10000 32)) (bvsgt (bvadd (select |#memory_int| (bvadd |ULTIMATE.start_main_~#a~0#1.base| (_ bv4 32))) (_ bv4294967295 32) (bvmul |ULTIMATE.start_main_~j~0#1| (_ bv4294967295 32))) (_ bv0 32)) (bvsgt |ULTIMATE.start_main_~j~0#1| (_ bv0 32)))) (or (= ((_ sign_extend 24) (_ bv0 8)) (select |#memory_int| (_ bv2 32))) (= (bvadd |ULTIMATE.start_main_~#a~0#1.base| (_ bv2 32)) (_ bv0 32))) (= |ULTIMATE.start_main_~i~0#1| (_ bv2 32)) (or (and (exists ((|ULTIMATE.start_main_~j~0#1| (_ BitVec 32)) (|v_ULTIMATE.start_main_~#a~0#1.base_BEFORE_CALL_12| (_ BitVec 32))) (and (bvslt |ULTIMATE.start_main_~j~0#1| (_ bv10000 32)) (bvslt (bvadd (select |#memory_int| (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#a~0#1.base_BEFORE_CALL_12|)) (_ bv4294967295 32) (bvmul |ULTIMATE.start_main_~j~0#1| (_ bv4294967295 32))) (_ bv10000 32)) (bvsgt (bvadd (select |#memory_int| (bvadd (_ bv4 32) |v_ULTIMATE.start_main_~#a~0#1.base_BEFORE_CALL_12|)) (_ bv4294967295 32) (bvmul |ULTIMATE.start_main_~j~0#1| (_ bv4294967295 32))) (_ bv0 32)) (bvsgt |ULTIMATE.start_main_~j~0#1| (_ bv0 32)))) (= ((_ sign_extend 24) (_ bv0 8)) (select |#memory_int| (_ bv2 32)))) (exists ((|ULTIMATE.start_main_~j~0#1| (_ BitVec 32))) (and (bvslt |ULTIMATE.start_main_~j~0#1| (_ bv10000 32)) (bvsgt (bvadd (_ bv4294967295 32) (select |#memory_int| (_ bv2 32)) (bvmul |ULTIMATE.start_main_~j~0#1| (_ bv4294967295 32))) (_ bv0 32)) (bvslt (bvadd (_ bv4294967295 32) (select |#memory_int| (_ bv2 32)) (bvmul |ULTIMATE.start_main_~j~0#1| (_ bv4294967295 32))) (_ bv10000 32)) (bvsgt |ULTIMATE.start_main_~j~0#1| (_ bv0 32))))))";
		final String expectedResultAsString = "(and (exists ((|ULTIMATE.start_main_~j~0#1| (_ BitVec 32))) (let ((.cse0 (bvadd (select |#memory_int| (bvadd |ULTIMATE.start_main_~#a~0#1.base| (_ bv4 32))) (_ bv4294967295 32) (bvmul |ULTIMATE.start_main_~j~0#1| (_ bv4294967295 32))))) (and (bvslt |ULTIMATE.start_main_~j~0#1| (_ bv10000 32)) (bvslt .cse0 (_ bv10000 32)) (bvsgt .cse0 (_ bv0 32)) (bvsgt |ULTIMATE.start_main_~j~0#1| (_ bv0 32))))) (or (= ((_ sign_extend 24) (_ bv0 8)) (select |#memory_int| (_ bv2 32))) (= (bvadd |ULTIMATE.start_main_~#a~0#1.base| (_ bv2 32)) (_ bv0 32))) (= |ULTIMATE.start_main_~i~0#1| (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e6851424_b2d392db_Treesizes_33_27() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~z~0#1", "ULTIMATE.start_main_~a~0#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1", "ULTIMATE.start_main_~az~0#1"),
		};
		final String formulaAsString = "(and (= (_ bv1 64) |ULTIMATE.start_main_~y~0#1|) (bvsle |ULTIMATE.start_main_~a~0#1| (_ bv50 32)) (= |ULTIMATE.start_main_~x~0#1| ((_ sign_extend 32) |ULTIMATE.start_main_~a~0#1|)) (bvsge |ULTIMATE.start_main_~a~0#1| (_ bv0 32)) (bvsge |ULTIMATE.start_main_~z~0#1| (_ bv0 32)) (= (_ bv0 64) (bvadd (bvneg |ULTIMATE.start_main_~az~0#1|) (bvmul |ULTIMATE.start_main_~x~0#1| ((_ sign_extend 32) |ULTIMATE.start_main_~z~0#1|)) (bvneg |ULTIMATE.start_main_~x~0#1|) ((_ sign_extend 32) |ULTIMATE.start_main_~a~0#1|))) (bvsle |ULTIMATE.start_main_~z~0#1| (_ bv50 32)))";
		final String expectedResultAsString = "(let ((.cse0 ((_ sign_extend 32) |ULTIMATE.start_main_~a~0#1|))) (and (= (bvmul .cse0 ((_ sign_extend 32) |ULTIMATE.start_main_~z~0#1|)) |ULTIMATE.start_main_~az~0#1|) (= (_ bv1 64) |ULTIMATE.start_main_~y~0#1|) (bvsle |ULTIMATE.start_main_~a~0#1| (_ bv50 32)) (= |ULTIMATE.start_main_~x~0#1| .cse0) (bvsge |ULTIMATE.start_main_~a~0#1| (_ bv0 32)) (bvsge |ULTIMATE.start_main_~z~0#1| (_ bv0 32)) (bvsle |ULTIMATE.start_main_~z~0#1| (_ bv50 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e730d5ff_182b695a_Treesizes_6_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967291 32)) (_ bv0 32)))";
		final String expectedResultAsString = "(= |ULTIMATE.start_main_~n~0#1| (_ bv5 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e7becfe0_7d9ebfc2_Treesizes_41_15() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#res", "sum_#in~m"),
		};
		final String formulaAsString = "(and (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (bvsle (bvadd |sum_#in~n| (_ bv4294967295 32)) (_ bv0 32)) (forall ((|v_sum_#in~n_BEFORE_CALL_19| (_ BitVec 32))) (or (not (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_19| (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967295 32) (bvmul |sum_#in~n| (_ bv4294967295 32))) (_ bv0 32))) (not (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_19| (_ bv4294967294 32)) (_ bv0 32))) (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_19| (_ bv4294967295 32)) (_ bv0 32)))) (not (bvsle |sum_#in~n| (_ bv0 32))))";
		final String expectedResultAsString = "(and (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (bvsle (bvadd |sum_#in~n| (_ bv4294967295 32)) (_ bv0 32)) (not (bvsle |sum_#in~n| (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e81cc094_40ca42b5_Treesizes_68_17() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#res", "sum_#in~m"),
		};
		final String formulaAsString = "(and (not (bvsle (bvadd |sum_#in~n| (_ bv4294967295 32)) (_ bv0 32))) (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (bvsle (bvadd |sum_#in~n| (_ bv4294967294 32)) (_ bv0 32)) (forall ((|v_sum_#in~n_BEFORE_CALL_18| (_ BitVec 32))) (or (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_18| (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967293 32) (bvmul |sum_#in~n| (_ bv4294967295 32))) (_ bv0 32)) (not (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_18| (_ bv4294967293 32)) (_ bv0 32))) (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_18| (_ bv4294967294 32)) (_ bv0 32)))) (forall ((|v_sum_#in~n_BEFORE_CALL_18| (_ BitVec 32))) (or (not (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_18| (_ bv4294967293 32)) (_ bv0 32))) (not (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_18| (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967294 32) (bvmul |sum_#in~n| (_ bv4294967295 32))) (_ bv0 32))) (bvsle (bvadd |v_sum_#in~n_BEFORE_CALL_18| (_ bv4294967294 32)) (_ bv0 32)))))";
		final String expectedResultAsString = "(and (not (bvsle (bvadd |sum_#in~n| (_ bv4294967295 32)) (_ bv0 32))) (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (bvsle (bvadd |sum_#in~n| (_ bv4294967294 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e86b78ef_e47f4ed6_Treesizes_6_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_4| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_4|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base_BEFORE_CALL_5|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e8e7a4c3_3eee6124_Treesizes_19_19() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_buf_write_~buf.base_BEFORE_CALL_8 (_ BitVec 32))) (and (bvult (bvadd (_ bv24 32) v_aws_byte_buf_write_~buf.base_BEFORE_CALL_8) (_ bv2147483647 32)) (bvugt (bvadd (_ bv24 32) v_aws_byte_buf_write_~buf.base_BEFORE_CALL_8) (_ bv8695 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) v_aws_byte_buf_write_~buf.base_BEFORE_CALL_8)))))";
		final String expectedResultAsString = "(exists ((v_aws_byte_buf_write_~buf.base_BEFORE_CALL_6 (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv24 32) v_aws_byte_buf_write_~buf.base_BEFORE_CALL_6))) (and (bvugt .cse0 (_ bv8695 32)) (bvult .cse0 (_ bv2147483647 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) v_aws_byte_buf_write_~buf.base_BEFORE_CALL_6))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_e98c8763_8adf07f9_Treesizes_49_29() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~Y~0#1", "ULTIMATE.start_main_~X~0#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1", "ULTIMATE.start_main_~v~0#1"),
		};
		final String formulaAsString = "(and (= (_ bv0 64) |ULTIMATE.start_main_~x~0#1|) (= (bvadd (bvneg ((_ sign_extend 32) |ULTIMATE.start_main_~X~0#1|)) (bvmul (_ bv2 64) ((_ sign_extend 32) |ULTIMATE.start_main_~Y~0#1|))) |ULTIMATE.start_main_~v~0#1|) (bvsge |ULTIMATE.start_main_~X~0#1| (_ bv0 32)) (exists ((|ULTIMATE.start_main_~xy~0#1| (_ BitVec 64)) (|ULTIMATE.start_main_~yx~0#1| (_ BitVec 64))) (= (_ bv0 64) (bvadd (bvneg |ULTIMATE.start_main_~v~0#1|) (bvmul |ULTIMATE.start_main_~yx~0#1| (_ bv2 64)) (bvneg (bvmul (_ bv2 64) |ULTIMATE.start_main_~xy~0#1|)) (bvneg ((_ sign_extend 32) |ULTIMATE.start_main_~X~0#1|)) (bvmul (_ bv2 64) ((_ sign_extend 32) |ULTIMATE.start_main_~Y~0#1|))))) (bvsle |ULTIMATE.start_main_~X~0#1| (_ bv10 32)) (bvsle |ULTIMATE.start_main_~Y~0#1| (_ bv10 32)) (bvsge |ULTIMATE.start_main_~Y~0#1| (_ bv0 32)) (= (_ bv0 64) |ULTIMATE.start_main_~y~0#1|))";
		final String expectedResultAsString = "(and (= (_ bv0 64) |ULTIMATE.start_main_~x~0#1|) (= (bvadd (bvneg ((_ sign_extend 32) |ULTIMATE.start_main_~X~0#1|)) (bvmul (_ bv2 64) ((_ sign_extend 32) |ULTIMATE.start_main_~Y~0#1|))) |ULTIMATE.start_main_~v~0#1|) (bvsge |ULTIMATE.start_main_~X~0#1| (_ bv0 32)) (bvsle |ULTIMATE.start_main_~X~0#1| (_ bv10 32)) (bvsle |ULTIMATE.start_main_~Y~0#1| (_ bv10 32)) (bvsge |ULTIMATE.start_main_~Y~0#1| (_ bv0 32)) (= (_ bv0 64) |ULTIMATE.start_main_~y~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ea204ef4_98e718e3_Treesizes_33_16() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base|) (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base|)) (bvult |ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base| (_ bv2147483647 32)) (exists ((|v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ BitVec 32))) (and (bvult |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ bv2147483647 32)) (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15|) (bvadd |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ bv8 32))) (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base_BEFORE_CALL_15| (_ bv16 32)) (_ bv2147483647 32)))) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base|) (_ bv2147483647 32)))";
		final String expectedResultAsString = "(and (= (select |#memory_$Pointer$.base| |ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base|) (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base|)) (bvult |ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base| (_ bv2147483647 32)) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_swap_contents_~b#1.base|) (_ bv2147483647 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_eac06e04_7a3f4dfa_Treesizes_4_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_78~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_78~0) (_ bv0 32))";
		final String expectedResultAsString = "(= (_ bv0 8) ~var_1_78~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ebb37d63_d88e04f2_Treesizes_9_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_26~0", "~var_1_25~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_26~0)) (not (= (_ bv0 8) ~var_1_25~0)))";
		final String expectedResultAsString = "(and (bvsge ((_ zero_extend 24) ~var_1_26~0) (_ bv1 32)) (bvsge ((_ zero_extend 24) ~var_1_25~0) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ed32ace3_f4492bc0_Treesizes_76_76() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var4_Pointer~0.base", "~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_330 (_ BitVec 32))) (or (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var4_Pointer~0.base v_ArrVal_330) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base))) (forall ((v_ArrVal_297 (_ BitVec 32)) (v_ArrVal_296 (_ BitVec 32)) (v_ArrVal_295 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store (store (store (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var4_Pointer~0.base v_ArrVal_330) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base v_ArrVal_296) (bvadd (_ bv4 32) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base) v_ArrVal_295) ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base v_ArrVal_297) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base))))))) (forall ((v_ArrVal_330 (_ BitVec 32))) (or (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var4_Pointer~0.base v_ArrVal_330) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base)))) (forall ((v_ArrVal_297 (_ BitVec 32)) (v_ArrVal_296 (_ BitVec 32)) (v_ArrVal_295 (_ BitVec 32))) (not (= ((_ extract 7 0) (select (store (store (store (store (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var4_Pointer~0.base v_ArrVal_330) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base v_ArrVal_296) (bvadd (_ bv4 32) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base) v_ArrVal_295) ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base v_ArrVal_297) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base)) (_ bv0 8)))))))";
		final String expectedResultAsString = "(let ((.cse1 (bvadd (_ bv4 32) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base))) (and (forall ((v_ArrVal_293 (_ BitVec 32))) (let ((.cse0 (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var4_Pointer~0.base v_ArrVal_293))) (or (not (= (_ bv0 8) ((_ extract 7 0) (select .cse0 ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base)))) (forall ((v_ArrVal_297 (_ BitVec 32)) (v_ArrVal_296 (_ BitVec 32)) (v_ArrVal_295 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store (store (store (store .cse0 ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base ((_ sign_extend 24) (_ bv0 8))) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base v_ArrVal_296) .cse1 v_ArrVal_295) ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base v_ArrVal_297) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base)))))))) (forall ((v_ArrVal_293 (_ BitVec 32))) (let ((.cse2 (store |#memory_int| ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var4_Pointer~0.base v_ArrVal_293))) (or (forall ((v_ArrVal_297 (_ BitVec 32)) (v_ArrVal_296 (_ BitVec 32)) (v_ArrVal_295 (_ BitVec 32))) (not (= ((_ extract 7 0) (select (store (store (store (store .cse2 ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base ((_ sign_extend 24) (_ bv1 8))) ~double_Array_0_arraydouble_Array_0arrayVar2_Pointer~0.base v_ArrVal_296) .cse1 v_ArrVal_295) ~signed_short_int_Array_0_arraysigned_short_int_Array_0Var1_Pointer~0.base v_ArrVal_297) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var2_Pointer~0.base)) (_ bv0 8)))) (= (_ bv0 8) ((_ extract 7 0) (select .cse2 ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var3_Pointer~0.base))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_edb44fd2_db269a87_Treesizes_6_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~0#1.base_BEFORE_CALL_30| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~0#1.base_BEFORE_CALL_30|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~0#1.base_BEFORE_CALL_21| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_ignore_case_harness_~#cur~0#1.base_BEFORE_CALL_21|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ee553655_7fa00a44_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(= (bvsrem (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv1 32)) (_ bv2 32)) (_ bv0 32))";
		final String expectedResultAsString = "(= (bvsrem (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv4294967295 32)) (_ bv2 32)) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ee810cb5_d987aa01_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_buf_secure_zero_~buf#1.base_BEFORE_CALL_8| (_ BitVec 32))) (and (bvult (bvadd (_ bv16 32) |v_aws_byte_buf_secure_zero_~buf#1.base_BEFORE_CALL_8|) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv8683 32)) (bvugt (bvadd (_ bv16 32) |v_aws_byte_buf_secure_zero_~buf#1.base_BEFORE_CALL_8|) |#StackHeapBarrier|))) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_aws_byte_buf_secure_zero_~buf#1.base_BEFORE_CALL_8|)) (_ bv0 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_28| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_28|))) (and (bvult .cse0 (_ bv2147483647 32)) (bvugt (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_buf_secure_zero_harness_~#buf~3#1.base_BEFORE_CALL_28|)) (_ bv0 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt .cse0 |#StackHeapBarrier|) (bvugt |#StackHeapBarrier| (_ bv8683 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ef502ca4_4f2445f5_Treesizes_57_57() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|v_skolemized_q#valueAsBitvector_135| (_ BitVec 32))) (or (not (= (fp ((_ extract 31 31) (select |#memory_int| (bvadd (_ bv29 32) |~#WrapperStruct00~0.base|))) ((_ extract 30 23) (select |#memory_int| (bvadd (_ bv29 32) |~#WrapperStruct00~0.base|))) ((_ extract 22 0) (select |#memory_int| (bvadd (_ bv29 32) |~#WrapperStruct00~0.base|)))) (fp ((_ extract 31 31) |v_skolemized_q#valueAsBitvector_135|) ((_ extract 30 23) |v_skolemized_q#valueAsBitvector_135|) ((_ extract 22 0) |v_skolemized_q#valueAsBitvector_135|)))) (fp.eq (fp ((_ extract 31 31) |v_skolemized_q#valueAsBitvector_135|) ((_ extract 30 23) |v_skolemized_q#valueAsBitvector_135|) ((_ extract 22 0) |v_skolemized_q#valueAsBitvector_135|)) (fp ((_ extract 31 31) (select |#memory_int| (bvadd (_ bv29 32) |~#WrapperStruct00~0.base|))) ((_ extract 30 23) (select |#memory_int| (bvadd (_ bv29 32) |~#WrapperStruct00~0.base|))) ((_ extract 22 0) (select |#memory_int| (bvadd (_ bv29 32) |~#WrapperStruct00~0.base|)))))))";
		final String expectedResultAsString = "(forall ((|v_skolemized_q#valueAsBitvector_124| (_ BitVec 32))) (let ((.cse1 (let ((.cse2 (select |#memory_int| (bvadd (_ bv29 32) |~#WrapperStruct00~0.base|)))) (fp ((_ extract 31 31) .cse2) ((_ extract 30 23) .cse2) ((_ extract 22 0) .cse2)))) (.cse0 (fp ((_ extract 31 31) |v_skolemized_q#valueAsBitvector_124|) ((_ extract 30 23) |v_skolemized_q#valueAsBitvector_124|) ((_ extract 22 0) |v_skolemized_q#valueAsBitvector_124|)))) (or (fp.eq .cse0 .cse1) (not (= .cse1 .cse0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_eff14279_8ca4500c_Treesizes_20_20() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_~b#1.base_BEFORE_CALL_6| (_ BitVec 32))) (and (bvugt |v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_~b#1.base_BEFORE_CALL_6| (_ bv8686 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_~b#1.base_BEFORE_CALL_6| (_ bv4294967284 32)))) (bvult |v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_~b#1.base_BEFORE_CALL_6| (_ bv2147483647 32)) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_~b#1.base_BEFORE_CALL_6|) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_~b#1.base_BEFORE_CALL_5| (_ BitVec 32))) (and (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_~b#1.base_BEFORE_CALL_5|) (_ bv2147483647 32)) (bvult |v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_~b#1.base_BEFORE_CALL_5| (_ bv2147483647 32)) (bvugt |v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_~b#1.base_BEFORE_CALL_5| (_ bv8686 32)) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_byte_buf_eq_ignore_case_~b#1.base_BEFORE_CALL_5| (_ bv4294967284 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f094d8fe_ce55ddba_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_begin_~list#1.base_BEFORE_CALL_22| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_begin_~list#1.base_BEFORE_CALL_22|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_27| (_ BitVec 32))) (not (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_begin_harness_~#list~0#1.base_BEFORE_CALL_27|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f1441a74_29043804_Treesizes_108_108() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_16_Pointer~0.base", "~WrapperStruct00_var_1_14_Pointer~0.base", "~WrapperStruct00_var_1_6_Pointer~0.base", "~WrapperStruct00_var_1_12_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_91 (_ BitVec 32)) (v_ArrVal_123 (_ BitVec 32)) (v_ArrVal_122 (_ BitVec 32)) (~WrapperStruct00_var_1_10_Pointer~0.base (_ BitVec 32))) (or (not (bvsle ((_ zero_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_122) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_12_Pointer~0.base) v_ArrVal_123) ~WrapperStruct00_var_1_10_Pointer~0.base))) ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_122) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_12_Pointer~0.base) v_ArrVal_123) ~WrapperStruct00_var_1_14_Pointer~0.base ((_ zero_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_122) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_12_Pointer~0.base) v_ArrVal_123) ~WrapperStruct00_var_1_10_Pointer~0.base)))) ~WrapperStruct00_var_1_1_Pointer~0.base))))) (= ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_122) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_12_Pointer~0.base) v_ArrVal_123) ~WrapperStruct00_var_1_14_Pointer~0.base ((_ zero_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_122) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_12_Pointer~0.base) v_ArrVal_123) ~WrapperStruct00_var_1_10_Pointer~0.base)))) ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_91) ~WrapperStruct00_var_1_1_Pointer~0.base))) ((_ sign_extend 24) ((_ extract 7 0) (select (store (store (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_122) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_12_Pointer~0.base) v_ArrVal_123) ~WrapperStruct00_var_1_14_Pointer~0.base ((_ zero_extend 16) ((_ extract 15 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_122) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_12_Pointer~0.base) v_ArrVal_123) ~WrapperStruct00_var_1_10_Pointer~0.base)))) ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_91) ~WrapperStruct00_var_1_6_Pointer~0.base))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_88 (_ BitVec 32)) (v_ArrVal_89 (_ BitVec 32)) (v_ArrVal_91 (_ BitVec 32)) (~WrapperStruct00_var_1_10_Pointer~0.base (_ BitVec 32))) (let ((.cse3 (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_88) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_12_Pointer~0.base) v_ArrVal_89))) (let ((.cse0 ((_ zero_extend 16) ((_ extract 15 0) (select .cse3 ~WrapperStruct00_var_1_10_Pointer~0.base))))) (let ((.cse1 (store .cse3 ~WrapperStruct00_var_1_14_Pointer~0.base .cse0))) (or (not (bvsle .cse0 ((_ sign_extend 24) ((_ extract 7 0) (select .cse1 ~WrapperStruct00_var_1_1_Pointer~0.base))))) (let ((.cse2 (store .cse1 ~WrapperStruct00_var_1_16_Pointer~0.base v_ArrVal_91))) (= ((_ sign_extend 24) ((_ extract 7 0) (select .cse2 ~WrapperStruct00_var_1_6_Pointer~0.base))) ((_ sign_extend 24) ((_ extract 7 0) (select .cse2 ~WrapperStruct00_var_1_1_Pointer~0.base))))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f21bf71e_5acfcc3b_Treesizes_9_9() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_47~0", "~var_1_48~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_48~0)) (not (= (_ bv0 8) ~var_1_47~0)))";
		final String expectedResultAsString = "(and (bvsge ((_ zero_extend 24) ~var_1_48~0) (_ bv1 32)) (bvsge ((_ zero_extend 24) ~var_1_47~0) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f26d26af_29a94e69_Treesizes_59_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 64) (bvadd (bvneg (bvmul (bvadd (_ bv1 64) |ULTIMATE.start_main_~y~0#1|) (bvadd (_ bv1 64) |ULTIMATE.start_main_~y~0#1|))) (_ bv4 64) (bvmul (_ bv4 64) (bvmul |ULTIMATE.start_main_~y~0#1| |ULTIMATE.start_main_~y~0#1| |ULTIMATE.start_main_~y~0#1|)) (bvneg (bvmul (bvmul (bvmul (bvadd (_ bv1 64) |ULTIMATE.start_main_~y~0#1|) (bvadd (_ bv1 64) |ULTIMATE.start_main_~y~0#1|)) (bvadd (_ bv1 64) |ULTIMATE.start_main_~y~0#1|)) (bvadd (_ bv1 64) |ULTIMATE.start_main_~y~0#1|))) (bvmul (_ bv12 64) (bvmul |ULTIMATE.start_main_~y~0#1| |ULTIMATE.start_main_~y~0#1|)) (bvmul (_ bv4 64) |ULTIMATE.start_main_~x~0#1|) (bvmul (_ bv12 64) |ULTIMATE.start_main_~y~0#1|) (bvneg (bvmul (bvmul (bvadd (_ bv2 64) (bvmul (_ bv2 64) |ULTIMATE.start_main_~y~0#1|)) (bvadd (_ bv1 64) |ULTIMATE.start_main_~y~0#1|)) (bvadd (_ bv1 64) |ULTIMATE.start_main_~y~0#1|)))))";
		final String expectedResultAsString = "(= (_ bv0 64) (let ((.cse0 (bvmul |ULTIMATE.start_main_~y~0#1| |ULTIMATE.start_main_~y~0#1|))) (bvadd (bvneg .cse0) (bvneg (bvmul (bvmul |ULTIMATE.start_main_~y~0#1| (bvmul (_ bv2 64) |ULTIMATE.start_main_~y~0#1|)) |ULTIMATE.start_main_~y~0#1|)) (bvmul (_ bv4 64) |ULTIMATE.start_main_~x~0#1|) (bvneg (bvmul |ULTIMATE.start_main_~y~0#1| (bvmul |ULTIMATE.start_main_~y~0#1| .cse0))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f340daa6_55735dd1_Treesizes_134_100() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_step_#t~mem15#1_11| (_ BitVec 16))) (bvsgt ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv3 32) |~#WrapperStruct00~0.base|)))) (bvshl ((_ zero_extend 16) |v_ULTIMATE.start_step_#t~mem15#1_11|) ((_ zero_extend 16) ((_ extract 15 0) ((_ sign_extend 16) ((_ extract 15 0) (bvadd (_ bv47138 32) (bvneg ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv3 32) |~#WrapperStruct00~0.base|))))) (bvneg ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv7 32) |~#WrapperStruct00~0.base|))))))))))))) (bvsle ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv5 32) |~#WrapperStruct00~0.base|)))) (_ bv32767 32)) (bvslt (_ bv29916 32) ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv5 32) |~#WrapperStruct00~0.base|))))) (not (bvsge ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv5 32) |~#WrapperStruct00~0.base|)))) (bvadd ((_ zero_extend 16) ((_ extract 15 0) ((_ sign_extend 16) ((_ extract 15 0) (bvadd (_ bv47138 32) (bvneg ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv3 32) |~#WrapperStruct00~0.base|))))) (bvneg ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv7 32) |~#WrapperStruct00~0.base|)))))))))) ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv3 32) |~#WrapperStruct00~0.base|))))))) (bvsle ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv7 32) |~#WrapperStruct00~0.base|)))) (_ bv16383 32)) (bvsle ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv3 32) |~#WrapperStruct00~0.base|)))) (_ bv16383 32)) (= (select |#memory_int| |~#WrapperStruct00~0.base|) ((_ sign_extend 16) ((_ extract 15 0) (bvadd (_ bv47138 32) (bvneg ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv3 32) |~#WrapperStruct00~0.base|))))) (bvneg ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv7 32) |~#WrapperStruct00~0.base|))))))))))";
		final String expectedResultAsString = "(let ((.cse4 (select |#memory_int| |~#WrapperStruct00~0.base|))) (let ((.cse1 ((_ zero_extend 16) ((_ extract 15 0) .cse4))) (.cse2 ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv5 32) |~#WrapperStruct00~0.base|))))) (.cse0 ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv3 32) |~#WrapperStruct00~0.base|))))) (.cse3 ((_ zero_extend 16) ((_ extract 15 0) (select |#memory_int| (bvadd (_ bv7 32) |~#WrapperStruct00~0.base|)))))) (and (exists ((|v_ULTIMATE.start_step_#t~mem15#1_11| (_ BitVec 16))) (bvsgt .cse0 (bvshl ((_ zero_extend 16) |v_ULTIMATE.start_step_#t~mem15#1_11|) .cse1))) (not (bvsge .cse2 (bvadd .cse1 .cse0))) (bvsle .cse2 (_ bv32767 32)) (bvslt (_ bv29916 32) .cse2) (bvsle .cse3 (_ bv16383 32)) (bvsle .cse0 (_ bv16383 32)) (= .cse4 ((_ sign_extend 16) ((_ extract 15 0) (bvadd (_ bv47138 32) (bvneg .cse0) (bvneg .cse3))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f3d0b5f9_3ca40b79_Treesizes_33_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id1~0", "~id2~0", "~id3~0", "~nomsg~0", "~send1~0", "~send2~0"),
		};
		final String formulaAsString = "(or (not (= ((_ sign_extend 24) ~send2~0) ((_ sign_extend 24) ~nomsg~0))) (not (bvsgt ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~nomsg~0))) ((_ sign_extend 24) ~id3~0))) (= ((_ sign_extend 24) ~id2~0) ((_ sign_extend 24) ~id1~0)) (forall ((~send3~0 (_ BitVec 8))) (not (= ((_ sign_extend 24) ~id3~0) ((_ sign_extend 24) ~send3~0)))) (not (= ((_ sign_extend 24) ~nomsg~0) ((_ sign_extend 24) ~send1~0))))";
		final String expectedResultAsString = "(let ((.cse0 ((_ sign_extend 24) ~nomsg~0))) (or (not (= ((_ sign_extend 24) ~send2~0) .cse0)) (not (bvsgt ((_ sign_extend 24) ((_ extract 7 0) .cse0)) ((_ sign_extend 24) ~id3~0))) (= ((_ sign_extend 24) ~id2~0) ((_ sign_extend 24) ~id1~0)) (not (= .cse0 ((_ sign_extend 24) ~send1~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f4555cb8_54563449_Treesizes_10_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base", "~unsigned_char_Array_0_arrayunsigned_char_Array_0Var0_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_80 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var0_Pointer~0.base v_ArrVal_80) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_48 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~unsigned_char_Array_0_arrayunsigned_char_Array_0Var0_Pointer~0.base v_ArrVal_48) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f524a408_1dd71b7a_Treesizes_6_6() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_7| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_7|)))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_2|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f5c42428_55b2ad47_Treesizes_26_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_swap_contents_~a#1.base_BEFORE_CALL_23| (_ BitVec 32))) (and (bvugt (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_swap_contents_~a#1.base_BEFORE_CALL_23|) (_ bv0 32)) (bvult (bvadd (_ bv32 32) |v_ULTIMATE.start_aws_linked_list_swap_contents_~a#1.base_BEFORE_CALL_23|) (_ bv2147483647 32)) (= (bvadd (_ bv24 32) |v_ULTIMATE.start_aws_linked_list_swap_contents_~a#1.base_BEFORE_CALL_23|) (select |#memory_$Pointer$.base| (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_swap_contents_~a#1.base_BEFORE_CALL_23|))) (bvult (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_swap_contents_~a#1.base_BEFORE_CALL_23|) (_ bv2147483647 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_swap_contents_~a#1.base_BEFORE_CALL_20| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv16 32) |v_ULTIMATE.start_aws_linked_list_swap_contents_~a#1.base_BEFORE_CALL_20|))) (and (bvugt .cse0 (_ bv0 32)) (= (select |#memory_$Pointer$.base| .cse0) (bvadd (_ bv24 32) |v_ULTIMATE.start_aws_linked_list_swap_contents_~a#1.base_BEFORE_CALL_20|)) (bvult .cse0 (_ bv2147483647 32)) (bvult (bvadd (_ bv32 32) |v_ULTIMATE.start_aws_linked_list_swap_contents_~a#1.base_BEFORE_CALL_20|) (_ bv2147483647 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f6a05053_77610883_Treesizes_47_23() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_linked_list_begin_~list#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_linked_list_begin_~list#1.base_BEFORE_CALL_4| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_aws_linked_list_begin_~list#1.base_BEFORE_CALL_4| (_ bv16 32)) (_ bv2147483647 32)) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv67 32)) (bvugt (bvadd |v_ULTIMATE.start_aws_linked_list_begin_~list#1.base_BEFORE_CALL_4| (_ bv16 32)) |#StackHeapBarrier|))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_ULTIMATE.start_aws_linked_list_begin_~list#1.base_BEFORE_CALL_4| (_ bv8 32)))))) (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv67 32)) (bvugt (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_begin_~list#1.base|) |#StackHeapBarrier|))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_begin_~list#1.base|))) (bvult (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_begin_~list#1.base|) (_ bv2147483647 32)))";
		final String expectedResultAsString = "(let ((.cse0 (bvadd (_ bv16 32) |ULTIMATE.start_aws_linked_list_begin_~list#1.base|))) (and (exists ((|#StackHeapBarrier| (_ BitVec 32))) (and (bvugt |#StackHeapBarrier| (_ bv67 32)) (bvugt .cse0 |#StackHeapBarrier|))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) |ULTIMATE.start_aws_linked_list_begin_~list#1.base|))) (bvult .cse0 (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f6ea4b3_ce86b6ba_Treesizes_42_41() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#StackHeapBarrier", "#HeapAllocations", "chain_node_alloc_node_~ptr~0#1.base", "old(#HeapAllocations)", "chain_node_#in~ppnode#1.base", "chain_node_~ppnode#1.base"),
		};
		final String formulaAsString = "(and (= (bvadd |old(#HeapAllocations)| (_ bv8 32)) |#HeapAllocations|) (not (= (_ bv0 32) |chain_node_alloc_node_~ptr~0#1.base|)) (bvult |old(#HeapAllocations)| |#StackHeapBarrier|) (= |chain_node_#in~ppnode#1.base| |chain_node_~ppnode#1.base|) (= |old(#HeapAllocations)| |chain_node_alloc_node_~ptr~0#1.base|) (exists ((|v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2| (_ BitVec 32))) (and (bvugt (bvadd (_ bv8 32) |v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2|) |#StackHeapBarrier|) (bvugt (bvadd (_ bv12 32) |v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2|) |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2| |#StackHeapBarrier|) (bvult (bvadd (_ bv12 32) |v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2|) (_ bv2147483647 32)))) (bvult |#HeapAllocations| |#StackHeapBarrier|))";
		final String expectedResultAsString = "(and (bvult |chain_node_alloc_node_~ptr~0#1.base| |#StackHeapBarrier|) (= |chain_node_#in~ppnode#1.base| |chain_node_~ppnode#1.base|) (= (bvadd (_ bv8 32) |chain_node_alloc_node_~ptr~0#1.base|) |#HeapAllocations|) (= |old(#HeapAllocations)| |chain_node_alloc_node_~ptr~0#1.base|) (exists ((|v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2| (_ BitVec 32))) (let ((.cse0 (bvadd (_ bv12 32) |v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2|))) (and (bvugt (bvadd (_ bv8 32) |v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2|) |#StackHeapBarrier|) (bvugt .cse0 |#StackHeapBarrier|) (bvugt |v_ULTIMATE.start_main_~#p1~0#1.base_BEFORE_CALL_2| |#StackHeapBarrier|) (bvult .cse0 (_ bv2147483647 32))))) (bvugt |chain_node_alloc_node_~ptr~0#1.base| (_ bv0 32)) (bvult |#HeapAllocations| |#StackHeapBarrier|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f7b0025_87543d3c_Treesizes_8_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_18~0", "~var_1_16~0"),
		};
		final String formulaAsString = "(and (= (_ bv0 8) ~var_1_16~0) (bvsle ((_ zero_extend 24) ~var_1_18~0) (_ bv0 32)))";
		final String expectedResultAsString = "(and (= (_ bv0 8) ~var_1_18~0) (= (_ bv0 8) ~var_1_16~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f7d48c81_97996874_Treesizes_11_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem9#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_41 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_41) |ULTIMATE.start_step_#t~mem9#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_41)) (_ bv0 32))))";
		final String expectedResultAsString = "(= (_ bv0 8) |ULTIMATE.start_step_#t~mem9#1|)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f8ac7092_b76faec7_Treesizes_25_25() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_12_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_200 (_ BitVec 32)) (v_ArrVal_177 (_ BitVec 32))) (not (bvsge (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_200) ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_177) ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv4294967291 32)) (select (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_200) ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_177) ~WrapperStruct00_var_1_4_Pointer~0.base))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_177 (_ BitVec 32)) (v_ArrVal_176 (_ BitVec 32))) (not (let ((.cse0 (store (store |#memory_int| ~WrapperStruct00_var_1_12_Pointer~0.base v_ArrVal_176) ~WrapperStruct00_var_1_8_Pointer~0.base v_ArrVal_177))) (bvsge (bvadd ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_3_Pointer~0.base))) (_ bv4294967291 32)) (select .cse0 ~WrapperStruct00_var_1_4_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f95a58b8_29b541c6_Treesizes_82_43() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~__CS_thread_index~0", "~__THREAD_FINISHED~0", "old(~__CS_round~0)", "~__CS_round~0"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#data1~0.base", "~#__CS_thread_status~0.base", "~#ma~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((v___CS_cs_~k~0_67 (_ BitVec 8)) (v_~__CS_round~0_197 (_ BitVec 8))) (and (= (select |#memory_int| (bvadd (_ bv67 32) ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) v___CS_cs_~k~0_67) ((_ zero_extend 24) v_~__CS_round~0_197)))))) ((_ sign_extend 24) ((_ extract 7 0) (bvadd (_ bv1 32) ((_ zero_extend 24) ~__CS_thread_index~0))))) (bvslt (bvadd ((_ zero_extend 24) v___CS_cs_~k~0_67) ((_ zero_extend 24) v_~__CS_round~0_197)) (_ bv2 32)))) (= |old(~__CS_round~0)| ~__CS_round~0) (= (_ bv71 32) |~#data1~0.base|) (= ~__THREAD_FINISHED~0 (_ bv2 8)) (= (_ bv37 32) |~#__CS_thread_status~0.base|) (= (_ bv67 32) |~#ma~0.base|) (exists ((v_~__CS_round~0_195 (_ BitVec 8)) (v___CS_cs_~k~0_65 (_ BitVec 8)) (v___CS_cs_~k~0_66 (_ BitVec 8))) (and (bvslt (bvadd ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) v___CS_cs_~k~0_65) ((_ zero_extend 24) v_~__CS_round~0_195)))) ((_ zero_extend 24) v___CS_cs_~k~0_66)) (_ bv2 32)) (bvslt (bvadd ((_ zero_extend 24) v___CS_cs_~k~0_65) ((_ zero_extend 24) v_~__CS_round~0_195)) (_ bv2 32)) (= ((_ sign_extend 24) ((_ extract 7 0) (bvadd (_ bv1 32) ((_ zero_extend 24) ~__CS_thread_index~0)))) (select |#memory_int| (bvadd ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) v___CS_cs_~k~0_65) ((_ zero_extend 24) v_~__CS_round~0_195)))) (_ bv67 32)))))))";
		final String expectedResultAsString = "(and (= |old(~__CS_round~0)| ~__CS_round~0) (= (_ bv71 32) |~#data1~0.base|) (= ~__THREAD_FINISHED~0 (_ bv2 8)) (= (_ bv37 32) |~#__CS_thread_status~0.base|) (exists ((v_~__CS_round~0_195 (_ BitVec 8)) (v___CS_cs_~k~0_65 (_ BitVec 8))) (let ((.cse0 (bvadd ((_ zero_extend 24) v___CS_cs_~k~0_65) ((_ zero_extend 24) v_~__CS_round~0_195)))) (and (bvslt .cse0 (_ bv2 32)) (= ((_ sign_extend 24) ((_ extract 7 0) (bvadd (_ bv1 32) ((_ zero_extend 24) ~__CS_thread_index~0)))) (select |#memory_int| (bvadd ((_ zero_extend 24) ((_ extract 7 0) .cse0)) (_ bv67 32))))))) (= (_ bv67 32) |~#ma~0.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_f997cc98_c5863196_Treesizes_7_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_10| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_10|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_36| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_36|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fa50fc0f_ed8e5cb5_Treesizes_17_14() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~z~0#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (bvsge |ULTIMATE.start_main_~z~0#1| (_ bv1 32)) (bvsle |ULTIMATE.start_main_~z~0#1| (_ bv2 32)) (= (_ bv0 64) (bvadd (bvneg |ULTIMATE.start_main_~y~0#1|) ((_ sign_extend 32) |ULTIMATE.start_main_~z~0#1|))) (= (_ bv1 64) |ULTIMATE.start_main_~x~0#1|))";
		final String expectedResultAsString = "(and (= |ULTIMATE.start_main_~y~0#1| ((_ sign_extend 32) |ULTIMATE.start_main_~z~0#1|)) (bvsge |ULTIMATE.start_main_~z~0#1| (_ bv1 32)) (bvsle |ULTIMATE.start_main_~z~0#1| (_ bv2 32)) (= (_ bv1 64) |ULTIMATE.start_main_~x~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_facf63e0_667a2cb6_Treesizes_16_7() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base|))) (exists ((|v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_15| (_ BitVec 32))) (= (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |v_ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base_BEFORE_CALL_15|)) (_ bv0 32))))";
		final String expectedResultAsString = "(= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |ULTIMATE.start_aws_byte_cursor_compare_lexical_harness_~#lhs~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fb680743_ec2248f2_Treesizes_11_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base", "~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_274 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base v_ArrVal_274) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_243 (_ BitVec 32))) (not (= ((_ extract 7 0) (select (store |#memory_int| ~signed_char_Array_0_arraysigned_char_Array_0Var1_Pointer~0.base v_ArrVal_243) ~BOOL_unsigned_char_Array_0_arrayBOOL_unsigned_char_Array_0Var0_Pointer~0.base)) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fbf16a9a_a02853b5_Treesizes_26_26() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_16_Pointer~0.base", "~WrapperStruct00_var_1_17_Pointer~0.base", "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_186 (_ BitVec 32))) (not (bvslt (bvadd (bvneg ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| (bvadd (_ bv36 32) |~#WrapperStruct00~0.base|) v_ArrVal_186) ~WrapperStruct00_var_1_17_Pointer~0.base)))) ((_ zero_extend 24) ((_ extract 7 0) (select (store |#memory_int| (bvadd (_ bv36 32) |~#WrapperStruct00~0.base|) v_ArrVal_186) ~WrapperStruct00_var_1_16_Pointer~0.base)))) (_ bv0 32))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_163 (_ BitVec 32))) (not (bvslt (let ((.cse0 (store |#memory_int| (bvadd (_ bv36 32) |~#WrapperStruct00~0.base|) v_ArrVal_163))) (bvadd (bvneg ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_17_Pointer~0.base)))) ((_ zero_extend 24) ((_ extract 7 0) (select .cse0 ~WrapperStruct00_var_1_16_Pointer~0.base))))) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fc7a0f70_ca842eb2_Treesizes_35_35() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_dynamic_~from#1.base_BEFORE_CALL_5| (_ BitVec 32))) (and (bvult (bvadd |v_ULTIMATE.start_aws_byte_buf_append_dynamic_~from#1.base_BEFORE_CALL_5| (_ bv4294967280 32)) (_ bv2147483647 32)) (bvult (bvadd |v_ULTIMATE.start_aws_byte_buf_append_dynamic_~from#1.base_BEFORE_CALL_5| (_ bv8 32)) (_ bv2147483647 32)) (= (concat (concat (concat (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_byte_buf_append_dynamic_~from#1.base_BEFORE_CALL_5| (_ bv3 32))) (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_byte_buf_append_dynamic_~from#1.base_BEFORE_CALL_5| (_ bv2 32)))) (select |#memory_int| (bvadd |v_ULTIMATE.start_aws_byte_buf_append_dynamic_~from#1.base_BEFORE_CALL_5| (_ bv1 32)))) (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_append_dynamic_~from#1.base_BEFORE_CALL_5|)) (_ bv0 32))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#from~0#1.base_BEFORE_CALL_8| (_ BitVec 32))) (and (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#from~0#1.base_BEFORE_CALL_8|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#from~0#1.base_BEFORE_CALL_8|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#from~0#1.base_BEFORE_CALL_8|))) (select |#memory_int| |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#from~0#1.base_BEFORE_CALL_8|))) (bvult (bvadd (_ bv8 32) |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#from~0#1.base_BEFORE_CALL_8|) (_ bv2147483647 32)) (bvult (bvadd |v_ULTIMATE.start_aws_byte_buf_append_dynamic_harness_~#from~0#1.base_BEFORE_CALL_8| (_ bv4294967280 32)) (_ bv2147483647 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fce99fc5_9d6c9bde_Treesizes_29_25() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~len~0#1", "ULTIMATE.start_main_~s~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int", "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~s~0#1.base| (select |#memory_$Pointer$.base| (bvadd (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~s~0#1.base|) (_ bv4 32)))) (= (_ bv3 32) (select |#memory_int| (bvadd (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~s~0#1.base|) (_ bv8 32)))) (= |ULTIMATE.start_main_~s~0#1.base| (bvadd (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~s~0#1.base|) (_ bv12 32))) (= (_ bv2 32) |ULTIMATE.start_main_~len~0#1|))";
		final String expectedResultAsString = "(and (= (_ bv3 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~s~0#1.base| (_ bv4294967292 32)))) (= |ULTIMATE.start_main_~s~0#1.base| (bvadd (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~s~0#1.base|) (_ bv12 32))) (= (select |#memory_$Pointer$.base| (bvadd |ULTIMATE.start_main_~s~0#1.base| (_ bv4294967288 32))) |ULTIMATE.start_main_~s~0#1.base|) (= (_ bv2 32) |ULTIMATE.start_main_~len~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fd94814_5ccc28d8_Treesizes_24_24() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_14| (_ BitVec 32))) (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_14|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_14|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_14|))) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_14|))))";
		final String expectedResultAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_10| (_ BitVec 32))) (= (_ bv0 32) (concat (concat (concat (select |#memory_int| (bvadd (_ bv3 32) |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_10|)) (select |#memory_int| (bvadd (_ bv2 32) |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_10|))) (select |#memory_int| (bvadd (_ bv1 32) |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_10|))) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_byte_buf_ignore_case_~a#1.base_BEFORE_CALL_10|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fdbb323_f4cdb5ce_Treesizes_27_27() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#unsigned_short_int_Array_0~0.base", "~#signed_char_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_66 (_ BitVec 32))) (not (bvslt ((_ zero_extend 16) ((_ extract 15 0) (select (store |#memory_int| (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32)) v_ArrVal_66) (bvadd (_ bv8 32) |~#unsigned_short_int_Array_0~0.base|)))) ((_ zero_extend 16) ((_ extract 15 0) (select (store |#memory_int| (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32)) v_ArrVal_66) (bvadd (_ bv6 32) |~#unsigned_short_int_Array_0~0.base|)))))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_47 (_ BitVec 32))) (not (let ((.cse0 (store |#memory_int| (bvadd |~#signed_char_Array_0~0.base| (_ bv1 32)) v_ArrVal_47))) (bvslt ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 (bvadd (_ bv8 32) |~#unsigned_short_int_Array_0~0.base|)))) ((_ zero_extend 16) ((_ extract 15 0) (select .cse0 (bvadd (_ bv6 32) |~#unsigned_short_int_Array_0~0.base|))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fe119e50_2a0f66dc_Treesizes_10_10() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base", "~WrapperStruct00_var_1_2_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_property_#t~mem49#1| (_ BitVec 8)) (v_ArrVal_159 (_ BitVec 32))) (bvslt ((_ sign_extend 24) |ULTIMATE.start_property_#t~mem49#1|) (select (store |#memory_int| ~WrapperStruct00_var_1_2_Pointer~0.base v_ArrVal_159) ~WrapperStruct00_var_1_8_Pointer~0.base)))";
		final String expectedResultAsString = "(forall ((|ULTIMATE.start_property_#t~mem49#1| (_ BitVec 8)) (v_ArrVal_144 (_ BitVec 32))) (bvslt ((_ sign_extend 24) |ULTIMATE.start_property_#t~mem49#1|) (select (store |#memory_int| ~WrapperStruct00_var_1_2_Pointer~0.base v_ArrVal_144) ~WrapperStruct00_var_1_8_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fea0eb1_f1adb28_Treesizes_4_3() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_5~0#1"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_5~0#1|) (_ bv0 32))";
		final String expectedResultAsString = "(= |ULTIMATE.start_step_~stepLocal_5~0#1| (_ bv0 8))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_fef71e14_97839985_Treesizes_61_61() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_9_Pointer~0.base", "~WrapperStruct00_var_1_13_Pointer~0.base", "~WrapperStruct00_var_1_1_Pointer~0.base", "~WrapperStruct00_var_1_3_Pointer~0.base", "~WrapperStruct00_var_1_5_Pointer~0.base", "~WrapperStruct00_var_1_4_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_65 (_ BitVec 32)) (v_ArrVal_66 (_ BitVec 32)) (v_ArrVal_40 (_ BitVec 32))) (= (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_66) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_13_Pointer~0.base) v_ArrVal_65) ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_40) ~WrapperStruct00_var_1_1_Pointer~0.base) (bvadd (bvneg (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_66) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_13_Pointer~0.base) v_ArrVal_65) ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_40) ~WrapperStruct00_var_1_5_Pointer~0.base)) (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_66) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_13_Pointer~0.base) v_ArrVal_65) ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_40) ~WrapperStruct00_var_1_3_Pointer~0.base) (bvneg (select (store (store (store |#memory_int| ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_66) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_13_Pointer~0.base) v_ArrVal_65) ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_40) ~WrapperStruct00_var_1_4_Pointer~0.base)))))";
		final String expectedResultAsString = "(forall ((v_ArrVal_40 (_ BitVec 32)) (v_ArrVal_39 (_ BitVec 32)) (v_ArrVal_38 (_ BitVec 32))) (let ((.cse0 (store (store (store |#memory_int| ~WrapperStruct00_var_1_13_Pointer~0.base v_ArrVal_39) (bvadd (_ bv4 32) ~WrapperStruct00_var_1_13_Pointer~0.base) v_ArrVal_38) ~WrapperStruct00_var_1_9_Pointer~0.base v_ArrVal_40))) (= (select .cse0 ~WrapperStruct00_var_1_1_Pointer~0.base) (bvadd (bvneg (select .cse0 ~WrapperStruct00_var_1_5_Pointer~0.base)) (select .cse0 ~WrapperStruct00_var_1_3_Pointer~0.base) (bvneg (select .cse0 ~WrapperStruct00_var_1_4_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	@Test
	public void SimplificationOpportunity_ffa52e20_ef7b3b00_Treesizes_49_11() {
		final FunDecl[] funDecls = {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~z~0#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort64, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (bvule |ULTIMATE.start_main_~z~0#1| (_ bv5 32)) (= (_ bv1 64) |ULTIMATE.start_main_~x~0#1|) (or (= (bvadd (_ bv1 64) (bvneg (bvmul |ULTIMATE.start_main_~y~0#1| ((_ zero_extend 32) |ULTIMATE.start_main_~z~0#1|))) ((_ zero_extend 32) |ULTIMATE.start_main_~z~0#1|) (bvmul |ULTIMATE.start_main_~x~0#1| ((_ zero_extend 32) |ULTIMATE.start_main_~z~0#1|) ((_ zero_extend 32) |ULTIMATE.start_main_~z~0#1|)) (bvneg (bvadd (_ bv1 64) (bvmul |ULTIMATE.start_main_~x~0#1| ((_ zero_extend 32) |ULTIMATE.start_main_~z~0#1|))))) (_ bv0 64)) (not (= (bvadd (_ bv1 64) (bvneg |ULTIMATE.start_main_~x~0#1|) (bvmul |ULTIMATE.start_main_~x~0#1| ((_ zero_extend 32) |ULTIMATE.start_main_~z~0#1|)) (bvneg |ULTIMATE.start_main_~y~0#1|)) (_ bv0 64)))) (= |ULTIMATE.start_main_~y~0#1| ((_ zero_extend 32) |ULTIMATE.start_main_~z~0#1|)))";
		final String expectedResultAsString = "(and (bvule |ULTIMATE.start_main_~z~0#1| (_ bv5 32)) (= (_ bv1 64) |ULTIMATE.start_main_~x~0#1|) (= |ULTIMATE.start_main_~y~0#1| ((_ zero_extend 32) |ULTIMATE.start_main_~z~0#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}



	// @formatter:on
}
