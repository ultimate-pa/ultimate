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
// Contains the 1000 smallest test files (by file size) of the SimplificationOpportunity corpus.
@Category(NoRegression.class)
public class SmallBitvectorSimplificationBenchmark {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY = true;
	private static final long TEST_TIMEOUT_MILLISECONDS = 60_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	// private static final String SOLVER_COMMAND = "cvc4 --incremental --lang smt";
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:12000 -memory:2024 -smt2 -in";
	// private static final String SOLVER_COMMAND = "INTERNAL_SMTINTERPOL:10000";

	private static final SimplificationTechnique SIMPLIFICATION_TECHNIQUE = SimplificationTechnique.POLY_PAC;

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private static QuantifierEliminationTestCsvWriter mCsvWriter;

	@BeforeClass
	public static void beforeAllTests() {
		mCsvWriter = new QuantifierEliminationTestCsvWriter(SmallBitvectorSimplificationBenchmark.class.getSimpleName());
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

	@Test
	public void SimplificationOpportunity_70c3181d_a3e226eb_Treesizes_3_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~N~0"),
		};
		final String formulaAsString = "(bvslt (_ bv1 32) ~N~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ae5518c_f1e3aa41_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r1~0"),
		};
		final String formulaAsString = "(= (_ bv2 32) ((_ zero_extend 24) ~r1~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b2ecbd15_7bacc26f_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r3~0"),
		};
		final String formulaAsString = "(= (_ bv2 32) ((_ zero_extend 24) ~r3~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fa018140_969af5d1_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r2~0"),
		};
		final String formulaAsString = "(= (_ bv2 32) ((_ zero_extend 24) ~r2~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_45e3af5b_d0a53438_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~total~0"),
		};
		final String formulaAsString = "(not (bvsle ~total~0 (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7e8a1bda_e8a261e0_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(not (bvugt ~counter~0 (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7de166b_1456dcbd_Treesizes_3_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_12~0"),
		};
		final String formulaAsString = "(bvsle (_ bv14 32) ~var_1_12~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7af1f4fb_eddb5cbe_Treesizes_3_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~num_nines~0"),
		};
		final String formulaAsString = "(bvult (_ bv0 32) ~num_nines~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ab9d9bef_79a70f96_Treesizes_3_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "addflt_#in~b"),
		};
		final String formulaAsString = "(bvule |addflt_#in~b| (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6565c311_e4540a15_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~head~0.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) ~head~0.base))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bbc13f0b_67e59942_Treesizes_3_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "max_~b~0"),
		};
		final String formulaAsString = "(bvsle max_~b~0 (_ bv2147483648 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_31a0b9c6_becfcb94_Treesizes_3_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "base2flt_#res"),
		};
		final String formulaAsString = "(bvule |base2flt_#res| (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_86a187aa_82fa16e5_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_1~0"),
		};
		final String formulaAsString = "(= ((_ zero_extend 24) ~var_1_1~0) (_ bv1 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_95a8c09c_31dce15c_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_1~0"),
		};
		final String formulaAsString = "(= ((_ zero_extend 24) ~var_1_1~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cfc0447e_10c2e7e3_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_12~0"),
		};
		final String formulaAsString = "(bvult ~var_1_12~0 (bvnot ~var_1_12~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_be225dbb_ed69672f_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_33~0"),
		};
		final String formulaAsString = "(= (_ bv0 32) ((_ zero_extend 24) ~var_1_33~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2e62e25_80798d_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_34~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_34~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_30959c22_c152130d_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_3~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_3~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_361414ba_8fc2a4b7_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_5~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_5~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_711c30b1_221c9da8_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_4~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_4~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7533af93_e371e793_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_8~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_8~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_95a8c09c_1210c4e1_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_1~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_1~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9fe22007_bca085b7_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_6~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_6~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d40a6ef8_9415d8e1_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_7~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_7~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e968dd2e_abd7ca04_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_9~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_9~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3d62193_1adf30ff_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_16~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_16~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4af9d2e_336dce44_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_56~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_56~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_75b19ec_433a108f_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_13~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_13~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bddc9afe_2837a39_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_35~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_35~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c49c2fe9_bd8e7ba_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_18~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_18~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_141417d5_f88fea0b_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_27~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_27~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_23eeba3a_94257938_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_41~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_41~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2c94217c_ad0a0464_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_88~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_88~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2d37cdfa_b2ae4b0a_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_17~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_17~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_36e57d00_9e76afc5_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_10~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_10~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_38baab6d_e020a3de_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_19~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_19~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3a7e4b28_34b18c0b_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_58~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_58~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3fddc78c_2d3989b7_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_37~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_37~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_434e389a_a84be379_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_38~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_38~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4817741a_cb248b13_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_25~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_25~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4b5b6f45_dfb34c91_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_49~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_49~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4c4edc52_8fe10e55_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_42~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_42~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_510d1008_95823968_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_14~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_14~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5437e335_232d5c8e_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_26~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_26~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_624fb21e_6f772e45_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_52~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_52~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_671249d0_cefe3072_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_32~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_32~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_68e58ce0_7e973a3d_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_39~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_39~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6b84a5af_c640a476_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_29~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_29~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_78197402_5511f2ef_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_40~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_40~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_79409010_78df872d_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_28~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_28~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7f215d71_f1c44bb8_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_24~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_24~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_92518843_537d9c22_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_76~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_76~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_92806c50_7c093b58_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_43~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_43~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9b716f8a_fd379e51_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_46~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_46~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9c1f99ba_ba133736_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_23~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_23~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9df67c3e_cfec620f_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_31~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_31~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a25276d9_cada6c43_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_30~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_30~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a567c492_5ecf9c66_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_50~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_50~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a7a13b21_ad0e5002_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_99~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_99~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_accf9b7a_35354f5a_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_73~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_73~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b2e07140_794bd3f4_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_60~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_60~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c69ae8a2_f3bd3f4e_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_22~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_22~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ca842223_6d84a46a_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_44~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_44~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ccd206bb_4ac7155d_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_11~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_11~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cd8903f4_f3b6e5c6_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_57~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_57~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_daa2bedd_71e2189a_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_20~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_20~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e2755ea6_2a27a1ae_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_54~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_54~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e7fb3774_a94fe190_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_15~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_15~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_eac06e04_7a3f4dfa_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_78~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_78~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ef52327f_1a827b92_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_21~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_21~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fd8ff600_f54aff4a_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_12~0"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ~var_1_12~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8670a6a8_e02d13_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_4~0"),
		};
		final String formulaAsString = "(not (= ~var_1_4~0 (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_383d82ea_6198b491_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_6~0"),
		};
		final String formulaAsString = "(not (= ~var_1_6~0 (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_43af37f1_3642c1eb_Treesizes_3_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_32~0"),
		};
		final String formulaAsString = "(bvule (_ bv2147483647 32) ~var_1_32~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_48a8fb6f_9f791ebc_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_8~0"),
		};
		final String formulaAsString = "(not (= ~var_1_8~0 (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_65a44613_8a5702aa_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_9~0"),
		};
		final String formulaAsString = "(not (= ~var_1_9~0 (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a53ec299_bd5cbfe1_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_7~0"),
		};
		final String formulaAsString = "(not (= ~var_1_7~0 (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b035ef5c_3545d320_Treesizes_3_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_24~0"),
		};
		final String formulaAsString = "(bvule (_ bv2147483647 32) ~var_1_24~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_df5be27d_5a315c46_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_5~0"),
		};
		final String formulaAsString = "(not (= ~var_1_5~0 (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3e03be23_15f209b_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_59~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_59~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_70a6940c_cd6073c8_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "max_~c~0"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvadd max_~c~0 (_ bv2147483648 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_84942be_1a13dda7_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_15~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_15~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_84d813e_55e47955_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_30~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_30~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ae3a2cba_f917565_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_20~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_20~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b7a35e6_22e885ef_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_32~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_32~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bdf0ab1_da17c975_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_31~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_31~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_133c2b2e_431ff8d6_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_41~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_41~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ca4ac2f_794b43d5_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_38~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_38~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2eaf1192_ee6fcc7a_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_21~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_21~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3bf9dce9_c113a349_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_25~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_25~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3c1eedec_6d83009f_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_47~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_47~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3dfbc0d3_f22f56b8_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_35~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_35~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3e773084_c1b58e66_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_33~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_33~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_44a51a5c_68c2d2ba_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_24~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_24~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4c36bcc5_67c6dddc_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_37~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_37~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5a32e174_be5e38c8_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_29~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_29~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_622ab839_fae89729_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_17~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_17~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6777a0e3_5a726dee_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_53~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_53~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_711508b8_8d177f0d_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_81~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_81~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_72dbc5b5_71fb9f98_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_22~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_22~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_798554a6_8eaa88f2_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "max_#res"),
		};
		final String formulaAsString = "(not (bvsge (_ bv2147483648 32) |max_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_99aeb733_f636dba8_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_42~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_42~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9a49529f_298709a3_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_13~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_13~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9c3c1aec_160e0da8_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_16~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_16~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9d7b41f2_b139c620_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_19~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_19~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9f94b7f5_bc518ea8_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_26~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_26~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b22f669c_513148e7_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_34~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_34~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b3e4437e_3ae7cec1_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_27~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_27~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c0f947c0_3d40f8e3_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_28~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_28~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c2aade58_5942f81c_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_11~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_11~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c50c5cf0_f0defd37_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_50~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_50~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d0d632bd_8ba8bbe9_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_14~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_14~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2ad06dd_95b5914e_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_23~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_23~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d7165b0f_7b0e9186_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_49~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_49~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_da0c24bf_99eb6f70_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_10~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_10~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e53132f7_5841e76b_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_18~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_18~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_eb854586_7ee85531_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_12~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ~var_1_12~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f8c22f8a_54290568_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "old(~head~0.base)"),
		};
		final String formulaAsString = "(not (bvugt |old(~head~0.base)| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8a68b774_4720c521_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~y~0", "~x~0"),
		};
		final String formulaAsString = "(and (bvsge ~y~0 (_ bv0 32)) (= ~x~0 ~y~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_368bddfd_58386024_Treesizes_7_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r2~0"),
		};
		final String formulaAsString = "(= ((_ extract 7 0) (bvadd (_ bv1 32) ((_ zero_extend 24) ~r2~0))) (_ bv2 8))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9bdda19c_ce26185a_Treesizes_7_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r3~0"),
		};
		final String formulaAsString = "(= ((_ extract 7 0) (bvadd (_ bv1 32) ((_ zero_extend 24) ~r3~0))) (_ bv2 8))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cc671139_ddd238ca_Treesizes_7_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r1~0"),
		};
		final String formulaAsString = "(= (_ bv2 8) ((_ extract 7 0) (bvadd (_ bv1 32) ((_ zero_extend 24) ~r1~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7562c9fb_8f308654_Treesizes_6_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "max_~a~0"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) (bvadd max_~a~0 (_ bv2147483648 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a84513_fd9870f7_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "base2flt_#res"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvadd (_ bv1 32) |base2flt_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e0993fc5_c426dbd_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~nomsg~0", "~g3v_new~0"),
		};
		final String formulaAsString = "(= ~g3v_new~0 ((_ extract 7 0) ((_ sign_extend 24) ~nomsg~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fd8c8e3c_bcfc232_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "inspect_base_~dll.base"),
		};
		final String formulaAsString = "(not (= inspect_base_~dll.base (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_94e71026_896152d6_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~g2v_new~0", "~nomsg~0"),
		};
		final String formulaAsString = "(= ~g2v_new~0 ((_ extract 7 0) ((_ sign_extend 24) ~nomsg~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_357e0a11_9c6c1563_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "max_#t~ret14"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvadd |max_#t~ret14| (_ bv2147483648 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a10e0c56_16d35cb5_Treesizes_7_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#in~n", "mult_~n"),
		};
		final String formulaAsString = "(= (bvmul (_ bv3 32) mult_~n) (bvmul |mult_#in~n| (_ bv3 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a10e0c56_739baafa_Treesizes_7_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#in~n", "mult_~n"),
		};
		final String formulaAsString = "(= (bvmul |mult_#in~n| (_ bv5 32)) (bvmul (_ bv5 32) mult_~n))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cc3b08ba_5120d625_Treesizes_9_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~L~0"),
		};
		final String formulaAsString = "(and (bvugt ~L~0 (_ bv0 32)) (bvugt (bvadd ~L~0 (_ bv4294967295 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_805ebe7d_3030b099_Treesizes_8_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~path1_len~0"),
		};
		final String formulaAsString = "(and (bvsgt ~path1_len~0 (_ bv0 32)) (not (bvult (_ bv1 32) ~path1_len~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1be17da9_ce0619c1_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "bounded_malloc_#res.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |bounded_malloc_#res.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_30c7d7b0_ef7a382a_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_19~0"),
		};
		final String formulaAsString = "(not (bvugt ~var_1_19~0 (_ bv4294967294 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a78d4413_1b65caf3_Treesizes_5_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~s2p_new~0"),
		};
		final String formulaAsString = "(= ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8))) ~s2p_new~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fb696490_843674ae_Treesizes_5_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~s1p_new~0"),
		};
		final String formulaAsString = "(= ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8))) ~s1p_new~0)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5ce5b1cc_7a1c93d4_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_9~0"),
		};
		final String formulaAsString = "(bvult ((_ sign_extend 24) ~var_1_9~0) (_ bv1073741823 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3a6e6ac_4c301a2_Treesizes_7_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r1~0"),
		};
		final String formulaAsString = "(= (_ bv1 8) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ~r1~0) (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8077ef98_dda4f0ae_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~k~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvneg |ULTIMATE.start_main_~k~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f0caabda_ca23de4d_Treesizes_3_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~l~0#1"),
		};
		final String formulaAsString = "(bvsle (_ bv1 32) |ULTIMATE.start_main_~l~0#1|)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4c12d5f3_92b0d80e_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~side1Failed_History_0~0"),
		};
		final String formulaAsString = "(= ((_ zero_extend 24) ~side1Failed_History_0~0) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_773816b6_c87b186_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~y~0#1"),
		};
		final String formulaAsString = "(not (bvugt |ULTIMATE.start_main_~y~0#1| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bde1e1d2_d89e431f_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~side2Failed_History_0~0"),
		};
		final String formulaAsString = "(= (_ bv0 32) ((_ zero_extend 24) ~side2Failed_History_0~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_11fb90c9_47572ab2_Treesizes_7_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r3~0"),
		};
		final String formulaAsString = "(= ~r3~0 ((_ extract 7 0) (bvadd (_ bv1 32) ((_ sign_extend 24) (_ bv1 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_24bd3ea2_58c5f1d0_Treesizes_7_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r1~0"),
		};
		final String formulaAsString = "(= ~r1~0 ((_ extract 7 0) (bvadd (_ bv1 32) ((_ sign_extend 24) (_ bv1 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_32fc07b3_9ca74411_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(not (bvugt |ULTIMATE.start_main_~x~0#1| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4edfe2a8_4aad096c_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_mulflt_~b#1"),
		};
		final String formulaAsString = "(not (bvugt |ULTIMATE.start_mulflt_~b#1| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_86fb52dc_d6c583c9_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1"),
		};
		final String formulaAsString = "(not (bvugt |ULTIMATE.start_main_~a~0#1| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9aef5925_a26b42cb_Treesizes_7_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r2~0"),
		};
		final String formulaAsString = "(= (_ bv1 8) ((_ extract 7 0) (bvadd (_ bv1 32) ((_ sign_extend 24) ~r2~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e6c2493e_86307da0_Treesizes_7_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r2~0"),
		};
		final String formulaAsString = "(= ~r2~0 ((_ extract 7 0) (bvadd (_ bv1 32) ((_ sign_extend 24) (_ bv1 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e952fc35_5c5bcccc_Treesizes_7_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r3~0"),
		};
		final String formulaAsString = "(= (_ bv1 8) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ~r3~0) (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_66f22922_92769768_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_2~0", "~x_1~0"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) ~x_1~0) (not (bvult (_ bv0 32) ~x_2~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_66f22922_c936b88e_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_2~0", "~x_1~0"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) ~x_2~0) (not (bvult (_ bv0 32) ~x_1~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_466e16eb_a6870d51_Treesizes_3_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~zero~0#1"),
		};
		final String formulaAsString = "(bvule |ULTIMATE.start_main_~zero~0#1| (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5678d8ff_6fa4ab3a_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~R~0#1"),
		};
		final String formulaAsString = "(= (bvurem (_ bv1 32) |ULTIMATE.start_main_~R~0#1|) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bb9576da_36bd114e_Treesizes_11_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~g~0"),
		};
		final String formulaAsString = "(and (or (= ~g~0 (_ bv1 32)) (bvsle ~g~0 (_ bv0 32))) (bvslt ~g~0 (_ bv1000 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e5a2a9da_d2645228_Treesizes_6_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_19~0"),
		};
		final String formulaAsString = "(forall ((~var_1_33~0 (_ BitVec 16))) (not (bvult ((_ zero_extend 16) ~var_1_33~0) ~var_1_19~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_10e965ed_e8ff4699_Treesizes_12_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~j~0"),
		};
		final String formulaAsString = "(forall ((~N~0 (_ BitVec 32))) (or (bvslt (_ bv1 32) ~N~0) (bvslt ~j~0 ~N~0) (not (bvslt (_ bv0 32) ~N~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_695db440_e2db4f35_Treesizes_5_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_11~0"),
		};
		final String formulaAsString = "(not (bvsge (_ bv4294967168 32) ((_ sign_extend 24) ~var_1_11~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e17ebc6b_6390973c_Treesizes_12_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~i~0"),
		};
		final String formulaAsString = "(forall ((~N~0 (_ BitVec 32))) (or (bvslt (_ bv1 32) ~N~0) (bvslt ~i~0 ~N~0) (not (bvslt (_ bv0 32) ~N~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_398dbb6e_d3751f12_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_mp_add_~i~0#1"),
		};
		final String formulaAsString = "(= (_ bv2 32) ((_ zero_extend 24) |ULTIMATE.start_mp_add_~i~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4319ff2d_5d1e8b18_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~bit~0#1"),
		};
		final String formulaAsString = "(= ((_ zero_extend 24) |ULTIMATE.start_main_~bit~0#1|) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_62133dd3_845266e8_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
		};
		final String formulaAsString = "(not (= |ULTIMATE.start_main_~x~0#1.base| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7e8a1bda_306e107_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(exists ((~c~0 (_ BitVec 32))) (and (= (bvadd ~c~0 (bvneg ~c~0)) ~counter~0) (bvugt ~c~0 (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_eed285d6_bd42b476_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_byte_buf_write_#in~buf.base"),
		};
		final String formulaAsString = "(not (bvugt |aws_byte_buf_write_#in~buf.base| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_22a0340b_ee7f85ac_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_step_#t~mem24#1"),
		};
		final String formulaAsString = "(not (bvslt |ULTIMATE.start_step_#t~mem24#1| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_488022e1_5708ae7f_Treesizes_10_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_9~0"),
		};
		final String formulaAsString = "(or (not (bvsgt (_ bv4294967291 32) ~var_1_9~0)) (not (= ~var_1_9~0 (bvneg ~var_1_9~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b2bd5c90_59818b0c_Treesizes_3_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~min~0#1"),
		};
		final String formulaAsString = "(bvsle (_ bv2147483647 32) |ULTIMATE.start_main_~min~0#1|)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c4fef087_8725e428_Treesizes_10_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo_#in~n"),
		};
		final String formulaAsString = "(and (not (bvslt |fibo_#in~n| (_ bv1 32))) (bvslt (bvadd |fibo_#in~n| (_ bv4294967295 32)) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fcb90427_2cd2ab1f_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~ptr~0#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_main_~ptr~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_69d882ab_586713d4_Treesizes_12_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_2~0", "~x_1~0"),
		};
		final String formulaAsString = "(forall ((~a~0 (_ BitVec 32))) (or (bvult (_ bv0 32) ~a~0) (= (bvadd ~x_1~0 (bvmul ~a~0 (_ bv2 32))) ~x_2~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_69d882ab_5c8b033a_Treesizes_12_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_2~0", "~x_1~0"),
		};
		final String formulaAsString = "(forall ((~b~0 (_ BitVec 32))) (or (bvult (_ bv0 32) ~b~0) (= (bvadd (bvmul ~b~0 (_ bv3 32)) ~x_2~0) ~x_1~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a6152145_b553c46d_Treesizes_3_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~bufferlen~0#1"),
		};
		final String formulaAsString = "(bvsle (_ bv2 32) |ULTIMATE.start_main_~bufferlen~0#1|)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a78afc15_648a0b06_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvadd |ULTIMATE.start_main_~a~0#1| (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d9943ffb_334cb0a6_Treesizes_10_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo1_#in~n"),
		};
		final String formulaAsString = "(and (bvslt (bvadd |fibo1_#in~n| (_ bv4294967295 32)) (_ bv1 32)) (not (bvslt |fibo1_#in~n| (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4a007277_6fd58cf7_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~tail~0#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_main_~tail~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_589121d4_7d8098c3_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~temp~2#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_main_~temp~2#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7e8a1bda_3acf56fd_Treesizes_7_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_8 (_ BitVec 32))) (= (bvadd v_arrayElimCell_8 (bvneg v_arrayElimCell_8)) ~counter~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_86690222_4a3f826b_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_#t~mem5#1.base"),
		};
		final String formulaAsString = "(not (= |ULTIMATE.start_main_#t~mem5#1.base| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9cde2c8b_fee16d8c_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_#t~mem6#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_main_#t~mem6#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cbdacd28_64d5b5a9_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~bcki~0#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_main_~bcki~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2f7b251_9394f44f_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_#t~mem7#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_main_#t~mem7#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e5baea2a_a9e04aa2_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~max~0#1"),
		};
		final String formulaAsString = "(not (bvsgt (_ bv2147483647 32) |ULTIMATE.start_main_~max~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_18a6f0f0_334aa0bf_Treesizes_6_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967294 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1a18792a_9f0eeaa1_Treesizes_6_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967292 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_280c9f2b_84806b53_Treesizes_6_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967290 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8a1b632a_3d95272d_Treesizes_6_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967293 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d9cb43e7_a2f55cce_Treesizes_6_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967289 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e730d5ff_182b695a_Treesizes_6_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967291 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a33e5b3b_4b7f0bd_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~s1p_new~0"),
		};
		final String formulaAsString = "(not (= (_ bv1 32) ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~s1p_new~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4e395ca5_5ed35b4c_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_check_~tmp___0~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 32) ((_ sign_extend 24) |ULTIMATE.start_check_~tmp___0~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7f9523c9_449739b5_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_#t~mem10#1"),
		};
		final String formulaAsString = "(not (bvsgt (_ bv2147483647 32) |ULTIMATE.start_main_#t~mem10#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9ed86dc0_5b4e10fd_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_search_list_~l#1.base"),
		};
		final String formulaAsString = "(not (= |ULTIMATE.start_search_list_~l#1.base| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b9a026a9_716b3fc3_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~s2p_new~0"),
		};
		final String formulaAsString = "(not (= (_ bv1 32) ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~s2p_new~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_faabd3ab_a54c9b37_Treesizes_10_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_0~0", "~y_7~0", "~x_6~0", "~y_1~0"),
		};
		final String formulaAsString = "(and (= ~y_7~0 ~x_0~0) (= ~y_1~0 ~x_0~0) (= ~x_6~0 ~x_0~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_46e664bd_dfb627be_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_string_eq_~a#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_aws_string_eq_~a#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ca15f04d_fe4b95c9_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_sll_length_~head#1.base"),
		};
		final String formulaAsString = "(not (= |ULTIMATE.start_sll_length_~head#1.base| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_de0036d5_c6f62d28_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem120#1"),
		};
		final String formulaAsString = "(= ((_ zero_extend 24) |ULTIMATE.start_property_#t~mem120#1|) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e398fd2_35123f37_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_4~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (= ~var_1_1~0 (_ bv0 8)) (bvsle ((_ zero_extend 24) ~var_1_4~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_368bddfd_c3d14c16_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r2~0"),
		};
		final String formulaAsString = "(= ((_ extract 7 0) (bvadd (_ bv1 32) ((_ sign_extend 24) ~r2~0))) ((_ extract 7 0) (bvadd (_ bv1 32) ((_ sign_extend 24) (_ bv1 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6d2e133_7ddea7b8_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem22#1"),
		};
		final String formulaAsString = "(= |ULTIMATE.start_step_#t~mem22#1| ((_ extract 7 0) ((_ sign_extend 24) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9bdda19c_c6dc80f0_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r3~0"),
		};
		final String formulaAsString = "(= ((_ extract 7 0) (bvadd (_ bv1 32) ((_ sign_extend 24) (_ bv1 8)))) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ~r3~0) (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b6a1b702_2c6a6ca3_Treesizes_9_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~output_len~0"),
		};
		final String formulaAsString = "(exists ((~path2_len~0 (_ BitVec 32))) (and (not (bvult (_ bv1 32) ~path2_len~0)) (bvugt ~path2_len~0 ~output_len~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cc671139_fc91ccd3_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~r1~0"),
		};
		final String formulaAsString = "(= ((_ extract 7 0) (bvadd (_ bv1 32) ((_ sign_extend 24) (_ bv1 8)))) ((_ extract 7 0) (bvadd ((_ sign_extend 24) ~r1~0) (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_19b5006f_4586f08e_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem30#1"),
		};
		final String formulaAsString = "(= |ULTIMATE.start_step_#t~mem30#1| ((_ extract 7 0) ((_ sign_extend 24) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4b928657_951778fe_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem38#1"),
		};
		final String formulaAsString = "(= |ULTIMATE.start_step_#t~mem38#1| ((_ extract 7 0) ((_ sign_extend 24) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c8f0d3f0_9f6d5ad7_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem42#1"),
		};
		final String formulaAsString = "(= |ULTIMATE.start_step_#t~mem42#1| ((_ extract 7 0) ((_ sign_extend 24) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1d293126_c4a31e57_Treesizes_10_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#in~n"),
		};
		final String formulaAsString = "(and (not (bvslt |fibonacci_#in~n| (_ bv1 32))) (bvslt (bvadd |fibonacci_#in~n| (_ bv4294967295 32)) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1509f4f2_9ddbae4b_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_8~0", "~var_1_34~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_8~0) (_ bv0 32)) (= (_ bv0 8) ~var_1_34~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_305d5464_dd5e8042_Treesizes_11_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_2~0", "~x_1~0", "~a~0"),
		};
		final String formulaAsString = "(or (bvult (_ bv0 32) ~a~0) (= (bvadd ~x_1~0 (bvmul ~a~0 (_ bv2 32))) ~x_2~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_36526cf4_42a07973_Treesizes_9_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~output_len~0"),
		};
		final String formulaAsString = "(forall ((~path1_len~0 (_ BitVec 32))) (or (bvult (_ bv1 32) ~path1_len~0) (not (bvugt ~path1_len~0 ~output_len~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_75c6cfee_d87b9177_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_17~0", "~var_1_5~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_17~0) (_ bv0 32)) (= ~var_1_5~0 (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5e7b5ba0_4cee13_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_3~0#1"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_3~0#1|) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7e8a1bda_c0d5288d_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(and (exists ((~n~0 (_ BitVec 32))) (and (not (bvslt (_ bv1 32) ~n~0)) (bvslt ~counter~0 ~n~0))) (bvsge ~counter~0 (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b420a85a_bfa4cde_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_uas_probe_~shost~1#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_uas_probe_~shost~1#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f59a8790_2c6a6ca3_Treesizes_9_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~output_len~0"),
		};
		final String formulaAsString = "(exists ((~path2_len~0 (_ BitVec 32))) (and (not (bvult (_ bv1 32) ~path2_len~0)) (bvugt ~path2_len~0 ~output_len~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fea0eb1_f1adb28_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_5~0#1"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_5~0#1|) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_48bb1244_9ea98eb7_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_sll_append_#t~mem8#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_sll_append_#t~mem8#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_51e0206_2a208174_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_63~0", "~var_1_62~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_63~0) (_ bv0 32)) (= (_ bv0 8) ~var_1_62~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_86834d6_9479162a_Treesizes_10_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_2~0"),
		};
		final String formulaAsString = "(forall ((~var_1_3~0 (_ BitVec 32))) (or (bvsle (bvnot ~var_1_3~0) ~var_1_2~0) (not (bvsge ~var_1_3~0 (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_afef54a0_3f1d52ca_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_dll_append_#t~mem8#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_dll_append_#t~mem8#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7334266_76392155_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_correct_version_~j~0#1"),
		};
		final String formulaAsString = "(= (_ bv6 32) (bvmul |ULTIMATE.start_correct_version_~j~0#1| (_ bv3 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7b0025_87543d3c_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_18~0", "~var_1_16~0"),
		};
		final String formulaAsString = "(and (= (_ bv0 8) ~var_1_16~0) (bvsle ((_ zero_extend 24) ~var_1_18~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2b401c7c_2b3bea7f_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_4~0#1"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_4~0#1|) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3958ef16_df9b9411_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_24~0", "~var_1_44~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_44~0) (_ bv0 32)) (= (_ bv0 8) ~var_1_24~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7bab3764_98d4bf56_Treesizes_5_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~r_add2~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvadd |ULTIMATE.start_main_~r_add2~0#1| (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cdfdcac3_a1695b11_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_12~0", "~var_1_10~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_12~0) (_ bv0 32)) (= (_ bv0 8) ~var_1_10~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d7ac58ad_168d3b79_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_28~0", "~var_1_51~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_51~0) (_ bv0 32)) (= (_ bv0 8) ~var_1_28~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e543fe3a_e345eae4_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_2~0#1"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_2~0#1|) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a036d293_ae31b696_Treesizes_9_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~path2_len~0"),
		};
		final String formulaAsString = "(forall ((~output_len~0 (_ BitVec 32))) (or (not (bvugt ~path2_len~0 ~output_len~0)) (bvult ~output_len~0 (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_335afab1_29da886b_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(= (_ bv5 32) (bvand (_ bv5 32) (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv8 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_59180d24_eaab2a46_Treesizes_12_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo_#in~n"),
		};
		final String formulaAsString = "(and (bvslt (bvadd |fibo_#in~n| (_ bv4294967293 32)) (_ bv1 32)) (not (bvslt (bvadd |fibo_#in~n| (_ bv4294967294 32)) (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_514d8b42_8e30e340_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_0~0#1"),
		};
		final String formulaAsString = "(not (= |ULTIMATE.start_step_~stepLocal_0~0#1| (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_68eecfbe_1e7b643e_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~z~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvurem (bvadd |ULTIMATE.start_main_~z~0#1| (_ bv2 32)) (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6999c6bb_3ac9e6e7_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvurem (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv2 32)) (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_755e5440_a6784d82_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(= (bvurem (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv4 32)) (_ bv4 32)) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7787bd00_67834a82_Treesizes_4_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_1~0#1"),
		};
		final String formulaAsString = "(not (= |ULTIMATE.start_step_~stepLocal_1~0#1| (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c96ff65a_a3cd13f0_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~y~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvurem (bvadd |ULTIMATE.start_main_~y~0#1| (_ bv2 32)) (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e1498d16_d47fa07c_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~z~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvsrem (bvadd |ULTIMATE.start_main_~z~0#1| (_ bv2 32)) (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e88564f3_cd113780_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~i~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvurem (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv6 32)) (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e88564f3_d115a66b_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~i~0#1"),
		};
		final String formulaAsString = "(= (bvurem (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv2 32)) (_ bv2 32)) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7fae18ae_eebeb1b8_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem79#1"),
		};
		final String formulaAsString = "(= |ULTIMATE.start_property_#t~mem79#1| ((_ extract 7 0) ((_ sign_extend 24) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7e8a1bda_122600ca_Treesizes_15_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(forall ((~C~0 (_ BitVec 32))) (or (not (bvugt (bvadd ~C~0 ~counter~0) (_ bv0 32))) (= (bvadd (bvneg ~C~0) ~C~0 ~counter~0) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a45a8bcf_901651b2_Treesizes_13_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~M~0"),
		};
		final String formulaAsString = "(and (bvsge ~M~0 (_ bv0 32)) (exists ((~N~0 (_ BitVec 32))) (and (bvslt ~M~0 ~N~0) (not (bvslt (_ bv1 32) ~N~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d5076adc_928b919c_Treesizes_13_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~M~0"),
		};
		final String formulaAsString = "(and (exists ((~N~0 (_ BitVec 32))) (and (bvsle ~M~0 ~N~0) (not (bvslt (_ bv0 32) ~N~0)))) (bvsge ~M~0 (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_18032071_89a44543_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem139#1"),
		};
		final String formulaAsString = "(= |ULTIMATE.start_property_#t~mem139#1| ((_ extract 7 0) ((_ sign_extend 24) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a34d7f2c_5d6fa4fe_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem112#1"),
		};
		final String formulaAsString = "(= |ULTIMATE.start_property_#t~mem112#1| ((_ extract 7 0) ((_ sign_extend 24) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_20bb6fb3_e2e490a_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_14~0", "~var_1_2~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_14~0)) (not (= ~var_1_2~0 (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4b1f8f69_17e467ec_Treesizes_8_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1"),
		};
		final String formulaAsString = "(or (bvule |ULTIMATE.start_main_~a~0#1| (_ bv1 32)) (not (bvuge |ULTIMATE.start_main_~a~0#1| (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_37b9613d_33bfd3db_Treesizes_14_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo1_#in~n"),
		};
		final String formulaAsString = "(and (bvslt (bvadd |fibo1_#in~n| (_ bv4294967294 32)) (_ bv1 32)) (not (= |fibo1_#in~n| (_ bv1 32))) (not (bvslt |fibo1_#in~n| (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5482c7e9_eab31eb7_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~j~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvsrem (bvadd |ULTIMATE.start_main_~j~0#1| (_ bv4294967292 32)) (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7b09a37f_f7d24801_Treesizes_14_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo2_#in~n"),
		};
		final String formulaAsString = "(and (not (bvslt |fibo2_#in~n| (_ bv1 32))) (not (= (_ bv1 32) |fibo2_#in~n|)) (bvslt (bvadd |fibo2_#in~n| (_ bv4294967294 32)) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ee681fc0_f058e65d_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvsrem (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv4294967294 32)) (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_10981935_ea9dc83b_Treesizes_8_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) (bvurem (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv2 32)) (_ bv2 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_21ff5d95_2d4a49b7_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_7~0", "~last_1_var_1_47~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_7~0) (_ bv0 32)) (= ~last_1_var_1_47~0 (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fdc2ad15_3562740b_Treesizes_8_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~i~0#1"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) (bvsrem (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv2 32)) (_ bv2 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b389775_c9c50469_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_6~0", "~var_1_5~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_5~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_6~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1946e8ae_403072a9_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_4~0", "~var_1_3~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_3~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_4~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_66a3ff35_a70b0855_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_8~0", "~var_1_9~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_9~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_8~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a5a97821_f977046_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~last_1_var_1_14~0", "~var_1_16~0"),
		};
		final String formulaAsString = "(and (= ~last_1_var_1_14~0 (_ bv0 8)) (bvsle ((_ zero_extend 24) ~var_1_16~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b5904ec7_3c5f5bbd_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_4~0", "~var_1_5~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_5~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_4~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b5025290_92994472_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_17~0"),
		};
		final String formulaAsString = "(forall ((~var_1_28~0 (_ BitVec 32))) (or (not (bvugt ~var_1_17~0 ~var_1_28~0)) (= (_ bv0 32) ~var_1_28~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_42f4d09e_252b3a70_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_9~0", "~var_1_10~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_10~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_9~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_aa2c7064_9686a2c7_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_buf_write_u8_~buf#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_aws_byte_buf_write_u8_~buf#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_127ccd51_74f6c80e_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_19~0", "~var_1_32~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_32~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_19~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_299ff125_9097c9c3_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_dll_circular_create_~head~0#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_dll_circular_create_~head~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_336be4a1_ee744c7a_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_14~0", "~var_1_13~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_14~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_13~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3765e9fb_431112da_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_29~0", "~var_1_28~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_29~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_28~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5b341867_91befe76_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_19~0", "~var_1_28~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_19~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_28~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_63d334c7_5e4bf68b_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_12~0", "~var_1_43~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_12~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_43~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_69c2c3a7_85f2f796_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_12~0", "~var_1_20~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_12~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_20~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_83f6ab40_51d11087_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_28~0", "~var_1_62~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_62~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_28~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ad7fd3ba_e6789519_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_27~0", "~var_1_25~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_25~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_27~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_af2615f8_e5ef79da_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_35~0", "~var_1_34~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_34~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_35~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e0c50e30_44003b4b_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_23~0", "~var_1_22~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_23~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_22~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ef328f58_79facb9c_Treesizes_16_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~M~0"),
		};
		final String formulaAsString = "(exists ((~N~0 (_ BitVec 32))) (and (bvsle ~M~0 ~N~0) (bvslt (_ bv0 32) ~N~0) (not (bvslt (_ bv1 32) ~N~0)) (not (bvslt ~M~0 ~N~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_667e1d44_eb4755e2_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_9~0"),
		};
		final String formulaAsString = "(forall ((~var_1_10~0 (_ BitVec 32))) (or (not (bvsge ~var_1_10~0 (_ bv0 32))) (not (bvsgt (bvadd ~var_1_9~0 (bvneg ~var_1_10~0)) ~var_1_9~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7e89ba97_323a376_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_sll_circular_append_#t~mem10#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_sll_circular_append_#t~mem10#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8351ebb_13c7059a_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_buf_write_be32_~buf#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_aws_byte_buf_write_be32_~buf#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_97a4cbe8_1c1629a6_Treesizes_8_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~p2_new~0", "~id3~0"),
		};
		final String formulaAsString = "(not (= ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~p2_new~0))) ((_ sign_extend 24) ~id3~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_97e2642e_bc4d77c9_Treesizes_8_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id2~0", "~p1_new~0"),
		};
		final String formulaAsString = "(not (= ((_ sign_extend 24) ~id2~0) ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~p1_new~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_41616691_e2652533_Treesizes_5_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem63#1"),
		};
		final String formulaAsString = "(= |ULTIMATE.start_property_#t~mem63#1| ((_ extract 7 0) ((_ sign_extend 24) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_800ba5cd_46a2b797_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_dll_circular_append_#t~mem10#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_dll_circular_append_#t~mem10#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e5ed30df_384ccf1c_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_buf_write_be64_~buf#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_aws_byte_buf_write_be64_~buf#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fa73615e_b6a6c636_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_buf_write_be16_~buf#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_aws_byte_buf_write_be16_~buf#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_66f22922_24c7f75_Treesizes_15_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_2~0", "~x_1~0"),
		};
		final String formulaAsString = "(and (exists ((~b~0 (_ BitVec 32))) (and (not (bvult (_ bv0 32) ~b~0)) (= (bvmul ~b~0 (_ bv3 32)) ~x_2~0))) (= (_ bv0 32) ~x_1~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_500d3f4_573c5f54_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_24~0", "~var_1_23~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_23~0) (_ bv0 32)) (bvsge ((_ zero_extend 24) ~var_1_24~0) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_66f22922_e2ce19ff_Treesizes_15_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_2~0", "~x_1~0"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) ~x_2~0) (exists ((~a~0 (_ BitVec 32))) (and (= ~x_1~0 (bvmul ~a~0 (_ bv2 32))) (not (bvult (_ bv0 32) ~a~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_66f22922_f4764c04_Treesizes_15_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_2~0", "~x_1~0"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) ~x_2~0) (exists ((~a~0 (_ BitVec 32))) (and (= (bvmul ~a~0 (_ bv3 32)) ~x_1~0) (not (bvult (_ bv0 32) ~a~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2243d702_6c3d132a_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_31~0", "~var_1_30~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_31~0) (_ bv0 32)) (bvsge ((_ zero_extend 24) ~var_1_30~0) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2ac8cb92_549b603d_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_19~0", "~var_1_20~0"),
		};
		final String formulaAsString = "(and (bvsge ((_ zero_extend 24) ~var_1_19~0) (_ bv1 32)) (bvsle ((_ zero_extend 24) ~var_1_20~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5230230d_cc6eb3f9_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_dll_circular_prepend_#t~mem10#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_dll_circular_prepend_#t~mem10#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5852f175_546dee66_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_18~0", "~var_1_17~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_18~0) (_ bv0 32)) (bvsge ((_ zero_extend 24) ~var_1_17~0) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_59dc382a_5ec8ae27_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_21~0", "~var_1_20~0"),
		};
		final String formulaAsString = "(and (bvsge ((_ zero_extend 24) ~var_1_20~0) (_ bv1 32)) (bvsle ((_ zero_extend 24) ~var_1_21~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_79dcf41d_b42706ec_Treesizes_18_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~Y~0"),
		};
		final String formulaAsString = "(forall ((~X~0 (_ BitVec 32))) (or (= (bvadd (bvmul ~X~0 (_ bv2 32)) ~Y~0) (_ bv19998 32)) (bvslt (bvadd ~X~0 (_ bv1 32)) (_ bv10000 32)) (not (bvslt ~X~0 (_ bv10000 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_874188d7_cef7a069_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_24~0", "~var_1_23~0"),
		};
		final String formulaAsString = "(and (bvsge ((_ zero_extend 24) ~var_1_23~0) (_ bv1 32)) (bvsle ((_ zero_extend 24) ~var_1_24~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_be5f7b9b_110242ad_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_4~0", "~var_1_5~0"),
		};
		final String formulaAsString = "(and (not (= ~var_1_4~0 (_ bv0 8))) (not (= ~var_1_5~0 (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c2648f52_c095d6a1_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_19~0", "~var_1_18~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_19~0) (_ bv0 32)) (bvsge ((_ zero_extend 24) ~var_1_18~0) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ff278fe4_fb1cfba2_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_8~0", "~var_1_7~0"),
		};
		final String formulaAsString = "(and (not (= ~var_1_8~0 (_ bv0 8))) (not (= ~var_1_7~0 (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_71c3a7fe_b0352351_Treesizes_16_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo2_#in~n"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 32) |fibo2_#in~n|)) (bvslt (bvadd |fibo2_#in~n| (_ bv4294967295 32)) (_ bv1 32)) (not (bvslt (bvadd (_ bv1 32) |fibo2_#in~n|) (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ee553655_7fa00a44_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(= (bvsrem (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv1 32)) (_ bv2 32)) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6cbaed41_b4bc8928_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_9~0", "~var_1_10~0"),
		};
		final String formulaAsString = "(and (not (= ~var_1_9~0 (_ bv0 8))) (not (= (_ bv0 8) ~var_1_10~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_80772cee_2a337e51_Treesizes_14_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#in~n"),
		};
		final String formulaAsString = "(and (not (= (_ bv1 32) |fibonacci_#in~n|)) (bvslt (bvadd |fibonacci_#in~n| (_ bv4294967294 32)) (_ bv1 32)) (not (bvslt |fibonacci_#in~n| (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8b2e2cdc_fc08c4a0_Treesizes_8_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id1~0", "~p3_new~0"),
		};
		final String formulaAsString = "(not (bvsgt ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~p3_new~0))) ((_ sign_extend 24) ~id1~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a6152145_af5c0074_Treesizes_7_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~bufferlen~0#1"),
		};
		final String formulaAsString = "(or (bvslt (_ bv2 32) |ULTIMATE.start_main_~bufferlen~0#1|) (= (_ bv2 32) |ULTIMATE.start_main_~bufferlen~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d75fa776_db6e4b5e_Treesizes_8_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id1~0", "~p4_new~0"),
		};
		final String formulaAsString = "(not (bvsgt ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~p4_new~0))) ((_ sign_extend 24) ~id1~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3fd38c6b_cad383a_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_32~0", "~var_1_33~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_33~0)) (not (= (_ bv0 8) ~var_1_32~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a78d99d3_3d0e809_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_31~0", "~var_1_30~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_31~0)) (not (= (_ bv0 8) ~var_1_30~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c46e710b_be9f0af4_Treesizes_9_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~i~0#1"),
		};
		final String formulaAsString = "(and (bvsge (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv4294967295 32)) (_ bv0 32)) (bvsge |ULTIMATE.start_main_~i~0#1| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_109ea795_330fc1a2_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_31~0", "~var_1_32~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_31~0)) (not (= (_ bv0 8) ~var_1_32~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ef82012_bf6c94af_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_12~0", "~var_1_11~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_11~0)) (not (= (_ bv0 8) ~var_1_12~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1fdde29a_7526167b_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_19~0", "~var_1_14~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_14~0)) (not (= (_ bv0 8) ~var_1_19~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_297c5d12_83fdc256_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_18~0", "~var_1_17~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_17~0)) (not (= (_ bv0 8) ~var_1_18~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_52a0efb4_5af45e66_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_28~0", "~var_1_27~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_27~0)) (not (= (_ bv0 8) ~var_1_28~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6e975a59_c8954148_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_16~0", "~var_1_15~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_16~0)) (not (= (_ bv0 8) ~var_1_15~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7ecf2112_6142f47d_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_29~0", "~var_1_30~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_29~0)) (not (= (_ bv0 8) ~var_1_30~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_827bc38e_577e648c_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_38~0", "~var_1_20~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_20~0)) (not (= (_ bv0 8) ~var_1_38~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_85522a3d_63ad8334_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_36~0", "~var_1_37~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_36~0)) (not (= (_ bv0 8) ~var_1_37~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_86cf2fe3_e20ed876_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_19~0", "~var_1_18~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_19~0)) (not (= (_ bv0 8) ~var_1_18~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a3feed70_bdc061db_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_24~0", "~var_1_23~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_23~0)) (not (= (_ bv0 8) ~var_1_24~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b226e3f5_c0d5288d_Treesizes_13_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(and (exists ((~n~0 (_ BitVec 32))) (and (not (bvslt (_ bv1 32) ~n~0)) (bvslt ~counter~0 ~n~0))) (bvsge ~counter~0 (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b3461db0_92fe6cc6_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_47~0", "~var_1_22~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_47~0)) (not (= (_ bv0 8) ~var_1_22~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ba8125a5_7a4aa401_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_14~0", "~var_1_13~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_14~0)) (not (= (_ bv0 8) ~var_1_13~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bb0fd7e4_b21d3548_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_11~0", "~var_1_10~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_10~0)) (not (= (_ bv0 8) ~var_1_11~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bfe6a341_d262cf4f_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_22~0", "~var_1_21~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_21~0)) (not (= (_ bv0 8) ~var_1_22~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d72655e0_d7a94eeb_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_21~0", "~var_1_20~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_21~0)) (not (= (_ bv0 8) ~var_1_20~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ebb37d63_d88e04f2_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_26~0", "~var_1_25~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_26~0)) (not (= (_ bv0 8) ~var_1_25~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f21bf71e_5acfcc3b_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_47~0", "~var_1_48~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_48~0)) (not (= (_ bv0 8) ~var_1_47~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fe809433_803c62da_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_13~0", "~var_1_12~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_13~0)) (not (= (_ bv0 8) ~var_1_12~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_dac00c6f_87df19bc_Treesizes_7_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_1 (_ BitVec 32))) (= (bvadd (bvneg v_arrayElimCell_1) v_arrayElimCell_1) |ULTIMATE.start_main_~sum~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3f7003b1_ac4b2ca4_Treesizes_10_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_3~0"),
		};
		final String formulaAsString = "(forall ((~var_1_2~0 (_ BitVec 16)) (~var_1_4~0 (_ BitVec 8))) (not (= (bvashr ~var_1_3~0 ((_ sign_extend 24) ~var_1_4~0)) (bvnot ((_ zero_extend 16) ~var_1_2~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ca0e54a1_7dd4418d_Treesizes_10_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4~0"),
		};
		final String formulaAsString = "(forall ((~var_1_3~0 (_ BitVec 16)) (~var_1_5~0 (_ BitVec 8))) (not (= (bvashr ~var_1_4~0 ((_ sign_extend 24) ~var_1_5~0)) (bvnot ((_ zero_extend 16) ~var_1_3~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_29190bff_5a815ed0_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_buf_append_dynamic_#t~mem934#1"),
		};
		final String formulaAsString = "(not (bvugt |ULTIMATE.start_aws_byte_buf_append_dynamic_#t~mem934#1| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d78013e_78f6f173_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_4~0", "isFloorCalling_#res"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ~calls_4~0)) (= |isFloorCalling_#res| (_ bv0 32))) (= (_ bv0 32) ~calls_4~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e77b849c_77febb67_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_1~0", "isFloorCalling_#res"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ~calls_1~0)) (= |isFloorCalling_#res| (_ bv0 32))) (= (_ bv0 32) ~calls_1~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_17f14338_3e6541a9_Treesizes_16_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo1_#in~n"),
		};
		final String formulaAsString = "(and (not (bvslt (bvadd |fibo1_#in~n| (_ bv4294967294 32)) (_ bv1 32))) (not (= |fibo1_#in~n| (_ bv3 32))) (bvslt (bvadd |fibo1_#in~n| (_ bv4294967292 32)) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_48d22069_cf85ecbe_Treesizes_8_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~g2v_new~0", "~g1v_new~0"),
		};
		final String formulaAsString = "(not (= ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~g2v_new~0))) ((_ sign_extend 24) ~g1v_new~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b9c8efde_9ea36564_Treesizes_16_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo2_#in~n"),
		};
		final String formulaAsString = "(and (not (= (_ bv5 32) |fibo2_#in~n|)) (bvslt (bvadd |fibo2_#in~n| (_ bv4294967290 32)) (_ bv1 32)) (not (bvslt (bvadd |fibo2_#in~n| (_ bv4294967292 32)) (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fcc3f3a9_6ce4471b_Treesizes_16_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo2_#in~n"),
		};
		final String formulaAsString = "(and (bvslt (bvadd |fibo2_#in~n| (_ bv4294967293 32)) (_ bv1 32)) (not (= (_ bv2 32) |fibo2_#in~n|)) (not (bvslt (bvadd |fibo2_#in~n| (_ bv4294967295 32)) (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9dc3417_a1849bd3_Treesizes_16_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4~0"),
		};
		final String formulaAsString = "(or (forall ((~var_1_15~0 (_ BitVec 32))) (or (bvsgt ~var_1_15~0 ~var_1_4~0) (not (bvule ~var_1_15~0 (_ bv30 32))))) (not (= ~var_1_4~0 (bvsrem ~var_1_4~0 ~var_1_4~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6ff924ed_4f1ea566_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~break_10~0"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~i_9~0"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) ~i_9~0) (= ((_ zero_extend 24) ~break_10~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_653a601c_2c9c29bc_Treesizes_16_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~An~0", "~i_AC~0"),
		};
		final String formulaAsString = "(and (bvslt ~i_AC~0 ~An~0) (forall ((~Cn~0 (_ BitVec 32))) (or (not (bvslt (_ bv0 32) ~Cn~0)) (bvslt (_ bv1 32) ~Cn~0) (bvslt ~i_AC~0 ~Cn~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c577cd6_e11b9d85_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_array_eq_c_str_harness_~array~0#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_aws_array_eq_c_str_harness_~array~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e76ac151_91b6425c_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_6~0", "~var_1_17~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_17~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_6~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_29c38e61_5df1e192_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_cursor_read_u8_harness_#t~mem58#1"),
		};
		final String formulaAsString = "(not (bvuge |ULTIMATE.start_aws_byte_cursor_read_u8_harness_#t~mem58#1| (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5b962e78_10bfe7aa_Treesizes_12_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_2~0", "~var_1_3~0"),
		};
		final String formulaAsString = "(or (bvsgt ~var_1_3~0 ~var_1_2~0) (forall ((~var_1_8~0 (_ BitVec 32)) (~var_1_7~0 (_ BitVec 32))) (not (bvsle ~var_1_2~0 (bvadd ~var_1_7~0 (bvneg ~var_1_8~0))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1bfc1ff5_25853d38_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_25~0", "~var_1_44~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_25~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_44~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7526f2c2_84e30a06_Treesizes_10_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_#t~mem7#1"),
		};
		final String formulaAsString = "(and (bvslt (bvadd (_ bv4294967295 32) |ULTIMATE.start_main_#t~mem7#1|) (_ bv6 32)) (not (bvslt |ULTIMATE.start_main_#t~mem7#1| (_ bv6 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c9938787_c4df8d14_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_14~0", "~var_1_51~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_14~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_51~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7c2cd9de_f242441d_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_string_eq_c_str_ignore_case_~str#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_aws_string_eq_c_str_ignore_case_~str#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_83760389_62c5a01a_Treesizes_10_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "thread1Thread1of1ForFork1_~i~0#1"),
		};
		final String formulaAsString = "(forall ((~n~0 (_ BitVec 32))) (or (bvult (_ bv2 32) (bvadd ~n~0 (_ bv4294967295 32))) (bvult |thread1Thread1of1ForFork1_~i~0#1| ~n~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1d293126_1b42cd77_Treesizes_16_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#in~n"),
		};
		final String formulaAsString = "(and (not (bvslt (bvadd (_ bv1 32) |fibonacci_#in~n|) (_ bv1 32))) (not (= (_ bv0 32) |fibonacci_#in~n|)) (bvslt (bvadd |fibonacci_#in~n| (_ bv4294967295 32)) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4ff802cc_eb601705_Treesizes_7_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~A~0.base", "~counter~0"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvadd (select |#memory_int| ~A~0.base) ~counter~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_56f07883_c6595ca7_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "thread2Thread1of1ForFork0_~i~1#1"),
		};
		final String formulaAsString = "(forall ((~n~0 (_ BitVec 32))) (or (not (bvult (_ bv1 32) ~n~0)) (bvult |thread2Thread1of1ForFork0_~i~1#1| (bvadd ~n~0 (_ bv4294967295 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7a60b261_10a84a5e_Treesizes_10_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_7~0"),
		};
		final String formulaAsString = "(forall ((~var_1_8~0 (_ BitVec 32)) (~var_1_9~0 (_ BitVec 32))) (not (bvuge (bvashr ((_ sign_extend 24) ~var_1_7~0) (bvadd ~var_1_8~0 ~var_1_9~0)) (_ bv1000160 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e5a2a9da_e9b9e9ad_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_19~0"),
		};
		final String formulaAsString = "(forall ((~var_1_33~0 (_ BitVec 16)) (~var_1_34~0 (_ BitVec 16))) (bvule ~var_1_19~0 (bvudiv ~var_1_19~0 (bvadd ((_ zero_extend 16) ~var_1_33~0) (bvneg ((_ zero_extend 16) ~var_1_34~0))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2355a5e7_a48b6193_Treesizes_16_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#in~n"),
		};
		final String formulaAsString = "(and (not (= (_ bv3 32) |fibonacci_#in~n|)) (not (bvslt (bvadd |fibonacci_#in~n| (_ bv4294967294 32)) (_ bv1 32))) (bvslt (bvadd |fibonacci_#in~n| (_ bv4294967292 32)) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a44c1198_aedce6d4_Treesizes_16_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#in~n"),
		};
		final String formulaAsString = "(and (not (= (_ bv2 32) |fibonacci_#in~n|)) (not (bvslt (bvadd |fibonacci_#in~n| (_ bv4294967295 32)) (_ bv1 32))) (bvslt (bvadd |fibonacci_#in~n| (_ bv4294967293 32)) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e55c438e_ea9a0cc9_Treesizes_11_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_26~0", "~var_1_25~0"),
		};
		final String formulaAsString = "(or (not (= ~var_1_25~0 (bvadd (_ bv100000000 32) ~var_1_26~0))) (not (bvugt ~var_1_25~0 ~var_1_26~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_622ab839_6d28bf1f_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_17~0"),
		};
		final String formulaAsString = "(forall ((~var_1_13~0 (_ BitVec 8))) (not (bvsgt (bvneg (bvsdiv ((_ zero_extend 24) ~var_1_13~0) ((_ zero_extend 24) ~var_1_17~0))) ((_ zero_extend 24) ~var_1_13~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_97464f35_c5dcb804_Treesizes_10_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ppp_write_#t~ret367"),
		};
		final String formulaAsString = "(exists ((|copy_from_user_~sz~0#1| (_ BitVec 32))) (and (not (bvslt |copy_from_user_~sz~0#1| (_ bv0 32))) (not (bvuge |copy_from_user_~sz~0#1| |ppp_write_#t~ret367|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cf50f181_fd1b75c3_Treesizes_10_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "copy_from_user_~n#1"),
		};
		final String formulaAsString = "(exists ((|copy_from_user_~sz~0#1| (_ BitVec 32))) (and (not (bvslt |copy_from_user_~sz~0#1| (_ bv0 32))) (not (bvuge |copy_from_user_~sz~0#1| |copy_from_user_~n#1|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_183d0beb_2287593f_Treesizes_10_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id1~0", "~p4_new~0"),
		};
		final String formulaAsString = "(and (= ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8))) ~p4_new~0) (bvsge ((_ sign_extend 24) ~id1~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_687946f6_4dbd0311_Treesizes_10_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id2~0", "~p1_new~0"),
		};
		final String formulaAsString = "(and (bvsge ((_ sign_extend 24) ~id2~0) (_ bv0 32)) (= ~p1_new~0 ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bd116b4d_3a1f5ccc_Treesizes_10_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id1~0", "~p3_new~0"),
		};
		final String formulaAsString = "(and (= ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8))) ~p3_new~0) (bvsge ((_ sign_extend 24) ~id1~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fa0eabe2_b8d3dcb4_Treesizes_10_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~p2_new~0", "~id3~0"),
		};
		final String formulaAsString = "(and (bvsge ((_ sign_extend 24) ~id3~0) (_ bv0 32)) (= ~p2_new~0 ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7b2a3ab9_5796c10c_Treesizes_10_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ppp_write_~tmp___0~19"),
		};
		final String formulaAsString = "(exists ((|copy_from_user_~sz~0#1| (_ BitVec 32))) (and (not (bvslt |copy_from_user_~sz~0#1| (_ bv0 32))) (not (bvuge |copy_from_user_~sz~0#1| ppp_write_~tmp___0~19))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3a834e38_ba24909c_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_~buf#1.base"),
		};
		final String formulaAsString = "(not (= |ULTIMATE.start_aws_byte_buf_write_from_whole_cursor_~buf#1.base| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_95f011c7_50abcb53_Treesizes_16_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo1_#in~n", "fibo1_~n"),
		};
		final String formulaAsString = "(or (bvslt fibo1_~n (_ bv1 32)) (= (_ bv1 32) fibo1_~n) (not (bvslt (bvadd (_ bv4294967294 32) fibo1_~n) (_ bv1 32))) (= |fibo1_#in~n| (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d6ffab28_e5a4942a_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(and (bvult (_ bv0 32) (bvmul |ULTIMATE.start_main_~n~0#1| (_ bv4 32))) (not (bvult (_ bv4 32) (bvmul |ULTIMATE.start_main_~n~0#1| (_ bv4 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_dc548b10_c3db02c6_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_step_#t~mem44#1", "ULTIMATE.start_step_~stepLocal_0~0#1"),
		};
		final String formulaAsString = "(not (bvsgt |ULTIMATE.start_step_~stepLocal_0~0#1| |ULTIMATE.start_step_#t~mem44#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e8efa665_569b2064_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_4~0", "isExecutiveFloorCalling_#res"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ~calls_4~0)) (= |isExecutiveFloorCalling_#res| (_ bv0 32))) (= (_ bv0 32) ~calls_4~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4bbb5d96_19052393_Treesizes_4_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_string_new_from_c_str_harness_~c_str~0#1.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) |ULTIMATE.start_aws_string_new_from_c_str_harness_~c_str~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c7941834_28473abc_Treesizes_10_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "copy_from_user_#res#1"),
		};
		final String formulaAsString = "(exists ((|copy_from_user_~sz~0#1| (_ BitVec 32))) (and (not (bvslt |copy_from_user_~sz~0#1| (_ bv0 32))) (not (bvuge |copy_from_user_~sz~0#1| |copy_from_user_#res#1|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_db3c904b_d6ecbcce_Treesizes_11_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_13~0"),
		};
		final String formulaAsString = "(and (bvsge ~var_1_13~0 (_ bv0 32)) (exists ((~var_1_30~0 (_ BitVec 8))) (not (bvsgt ((_ zero_extend 24) ~var_1_30~0) (bvneg ~var_1_13~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ac6e62a_5f096885_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~j~0#1"),
		};
		final String formulaAsString = "(and (not (bvslt (_ bv1 32) |ULTIMATE.start_main_~j~0#1|)) (bvsgt |ULTIMATE.start_main_~j~0#1| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3be0ecf_c65212ac_Treesizes_12_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~result~0#1"),
		};
		final String formulaAsString = "(and (bvsgt (bvadd (_ bv10 32) |ULTIMATE.start_main_~result~0#1|) (_ bv100 32)) (not (bvsgt (bvadd (_ bv9 32) |ULTIMATE.start_main_~result~0#1|) (_ bv100 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_97e5645_3efc1bc2_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~this_expect~0#1"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) (bvsrem (bvadd |ULTIMATE.start_main_~this_expect~0#1| (_ bv1 32)) (_ bv2 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5ffe8b7c_7ab758cf_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_5~0", "ULTIMATE.start_step_~stepLocal_3~0#1"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_3~0#1|) (_ bv0 32)) (= ~var_1_5~0 (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b38daf5_84d868c5_Treesizes_13_13() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x1~0", "~x2~0"),
		};
		final String formulaAsString = "(and (bvslt (bvadd ~x2~0 (_ bv4294967295 32)) (_ bv10000 32)) (not (bvslt ~x1~0 (_ bv10000 32))) (= ~x1~0 ~x2~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b9b711cf_e1e39458_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_1~0#1", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (= ~var_1_1~0 (_ bv0 8)) (bvsle ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_1~0#1|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c854f967_a5a8d934_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_6~0", "ULTIMATE.start_step_~stepLocal_4~0#1"),
		};
		final String formulaAsString = "(and (= ~var_1_6~0 (_ bv0 8)) (bvsle ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_4~0#1|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_66f4f84_10a079b5_Treesizes_13_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_7~0"),
		};
		final String formulaAsString = "(forall ((~var_1_12~0 (_ BitVec 8))) (or (not (bvsge ((_ zero_extend 24) ~var_1_12~0) (_ bv127 32))) (not (bvsgt ((_ zero_extend 24) ~var_1_7~0) ((_ zero_extend 24) ~var_1_12~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_69d882ab_f85c32e_Treesizes_23_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_2~0", "~x_1~0"),
		};
		final String formulaAsString = "(forall ((~a~0 (_ BitVec 32)) (~b~0 (_ BitVec 32))) (or (not (bvult (_ bv0 32) ~a~0)) (not (bvult (_ bv0 32) ~b~0)) (= (bvadd ~b~0 ~x_2~0) (bvadd ~a~0 ~x_1~0)) (bvult (_ bv1 32) ~b~0) (bvult (_ bv1 32) ~a~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_75de1b34_5a26caff_Treesizes_13_13() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x1~0", "~x2~0"),
		};
		final String formulaAsString = "(and (not (bvslt ~x1~0 (_ bv10000 32))) (= ~x1~0 ~x2~0) (bvslt (bvadd ~x1~0 (_ bv4294967295 32)) (_ bv10000 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4d0616ce_23c30c3_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_17~0", "ULTIMATE.start_step_~stepLocal_3~0#1"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_17~0) (_ bv0 32)) (= |ULTIMATE.start_step_~stepLocal_3~0#1| (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5ea8e028_974f1b99_Treesizes_13_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~y~0", "ULTIMATE.start_main_~z~0#1"),
		};
		final String formulaAsString = "(or (= (bvurem (bvadd |ULTIMATE.start_main_~z~0#1| (bvmul ~y~0 (_ bv2 32))) (_ bv2 32)) (_ bv0 32)) (= ~y~0 (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_edb6b29_7ae491c4_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_31~0"),
		};
		final String formulaAsString = "(forall ((~var_1_10~0 (_ BitVec 32))) (or (forall ((~var_1_37~0 (_ BitVec 16))) (bvslt (bvashr ~var_1_10~0 ((_ zero_extend 16) ~var_1_37~0)) ~var_1_31~0)) (not (bvsgt (_ bv4294967291 32) ~var_1_10~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_edb6b29_8802638c_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_31~0"),
		};
		final String formulaAsString = "(forall ((~var_1_29~0 (_ BitVec 32))) (or (forall ((~var_1_37~0 (_ BitVec 16))) (bvslt (bvashr ~var_1_29~0 ((_ zero_extend 16) ~var_1_37~0)) ~var_1_31~0)) (not (bvsgt (_ bv4294967291 32) ~var_1_29~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_826a431c_43c461ac_Treesizes_13_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_15~0"),
		};
		final String formulaAsString = "(or (forall ((~var_1_24~0 (_ BitVec 32))) (not (bvsge ~var_1_24~0 (_ bv0 32)))) (bvuge (bvxor (_ bv4294967096 32) ((_ sign_extend 24) ~var_1_15~0)) ((_ sign_extend 24) ~var_1_15~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7fedf9cc_685ffa4b_Treesizes_6_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~pat_len~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~a_len~0#1| (_ BitVec 32))) (bvule |ULTIMATE.start_main_~pat_len~0#1| (bvadd (_ bv1 32) |ULTIMATE.start_main_~a_len~0#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6b4f19ca_261dce2c_Treesizes_7_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "check_~n#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvadd (_ bv2147483648 32) (select |#memory_int| |check_~n#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f5941c5f_6090dca1_Treesizes_13_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_18~0"),
		};
		final String formulaAsString = "(forall ((~var_1_33~0 (_ BitVec 16))) (or (not (bvsge ((_ zero_extend 16) ~var_1_33~0) (_ bv32767 32))) (not (bvult ((_ zero_extend 16) ~var_1_33~0) ((_ sign_extend 24) ~var_1_18~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a15347ed_93e8a0b_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isExecutiveFloorCalling_#t~ret135", "~calls_4~0"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) ~calls_4~0) (or (not (= (_ bv0 32) ~calls_4~0)) (= (_ bv0 32) |isExecutiveFloorCalling_#t~ret135|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fd6510f_6b0fb287_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isExecutiveFloorCalling_#t~ret102", "~calls_4~0"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ~calls_4~0)) (= (_ bv0 32) |isExecutiveFloorCalling_#t~ret102|)) (= (_ bv0 32) ~calls_4~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_40192902_32db7921_Treesizes_12_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_6~0", "~var_1_5~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_5~0) (_ bv0 32)) (= ~var_1_1~0 (_ bv0 8)) (bvsle ((_ zero_extend 24) ~var_1_6~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_606da078_bb32ca6_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_13~0"),
		};
		final String formulaAsString = "(forall ((~var_1_6~0 (_ BitVec 8))) (not (bvule (bvadd (bvneg ((_ zero_extend 24) ~var_1_6~0)) ~var_1_13~0) (_ bv10 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e0d523af_7d9f80e1_Treesizes_11_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "old(~waterLevel~0)", "~waterLevel~0"),
		};
		final String formulaAsString = "(and (bvsgt (bvadd ~waterLevel~0 (_ bv1 32)) (_ bv0 32)) (= (bvadd ~waterLevel~0 (_ bv1 32)) |old(~waterLevel~0)|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2057918b_1d27c668_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_4~0", "stopRequestedInDirection_#t~ret40#1"),
		};
		final String formulaAsString = "(and (or (= (_ bv0 32) |stopRequestedInDirection_#t~ret40#1|) (not (= (_ bv0 32) ~calls_4~0))) (= (_ bv0 32) ~calls_4~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fb5d7dab_dc1c5063_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_4~0", "stopRequestedInDirection_#t~ret73#1"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ~calls_4~0)) (= (_ bv0 32) |stopRequestedInDirection_#t~ret73#1|)) (= (_ bv0 32) ~calls_4~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_72bf8091_c43d1cc3_Treesizes_11_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~c~0#1", "~SIZE~0", "~last~0"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~c~0#1| (_ bv0 32)) (= (_ bv20 32) ~SIZE~0) (not (bvsge (_ bv0 32) ~last~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_86a187aa_e7cc291a_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_1~0"),
		};
		final String formulaAsString = "(forall ((~var_1_9~0 (_ BitVec 8))) (or (not (bvsge ((_ zero_extend 24) ~var_1_9~0) (_ bv1 32))) (= ((_ zero_extend 24) ~var_1_1~0) ((_ zero_extend 24) ~var_1_9~0)) (not (bvsle ((_ zero_extend 24) ~var_1_9~0) (_ bv1 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6e18ab87_5cf01b0f_Treesizes_16_16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~l_4~0", "~f1_6~0"),
		};
		final String formulaAsString = "(and (or (= (_ bv0 32) ~l_4~0) (bvsgt ~f1_6~0 (_ bv0 32))) (or (not (bvsgt ~f1_6~0 (_ bv0 32))) (= (_ bv1 32) ~l_4~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_71838328_d525c341_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_4~0", "stopRequestedInDirection_~tmp___0~5#1"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ~calls_4~0)) (= (_ bv0 32) |stopRequestedInDirection_~tmp___0~5#1|)) (= (_ bv0 32) ~calls_4~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_69d882ab_f0df95d1_Treesizes_25_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_2~0", "~x_1~0"),
		};
		final String formulaAsString = "(forall ((~a~0 (_ BitVec 32)) (~b~0 (_ BitVec 32))) (or (not (bvult (_ bv0 32) ~b~0)) (bvult (_ bv2 32) ~a~0) (= (bvadd ~a~0 ~x_1~0) (bvadd ~x_2~0 (bvmul ~b~0 (_ bv2 32)))) (bvult (_ bv1 32) ~b~0) (not (bvult (_ bv1 32) ~a~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_69d882ab_f1ef4e34_Treesizes_25_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~x_2~0", "~x_1~0"),
		};
		final String formulaAsString = "(forall ((~a~0 (_ BitVec 32)) (~b~0 (_ BitVec 32))) (or (not (bvult (_ bv1 32) ~b~0)) (not (bvult (_ bv0 32) ~a~0)) (bvult (_ bv2 32) ~b~0) (= (bvadd ~b~0 ~x_2~0) (bvadd ~x_1~0 (bvmul ~a~0 (_ bv2 32)))) (bvult (_ bv1 32) ~a~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_de3343c5_6cac9ec9_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "buttonForFloorIsPressed_#res", "~floorButtons_4~0"),
		};
		final String formulaAsString = "(and (= ~floorButtons_4~0 (_ bv0 32)) (or (= |buttonForFloorIsPressed_#res| (_ bv0 32)) (not (= ~floorButtons_4~0 (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_76d1079_37b9877e_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem29#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_84 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_84) |ULTIMATE.start_step_#t~mem29#1|) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_84)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_76d1079_644bebd4_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem29#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_26 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_26) |ULTIMATE.start_step_#t~mem29#1|) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_26)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_76d1079_9cba844c_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem29#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_19 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_19) |ULTIMATE.start_step_#t~mem29#1|) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_19)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_76d1079_d1781af4_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem29#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_22 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_22) |ULTIMATE.start_step_#t~mem29#1|) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_22)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_52e31882_2959ae87_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem39#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_57 (_ BitVec 32))) (and (= |ULTIMATE.start_step_#t~mem39#1| ((_ extract 7 0) v_arrayElimCell_57)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_57)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_52e31882_37d9f6c0_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem39#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_47 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_47))) (= ((_ extract 7 0) v_arrayElimCell_47) |ULTIMATE.start_step_#t~mem39#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_52e31882_4042d8e5_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem39#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_45 (_ BitVec 32))) (and (= |ULTIMATE.start_step_#t~mem39#1| ((_ extract 7 0) v_arrayElimCell_45)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_45)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_63af018f_8a9e58ec_Treesizes_11_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~c~0#1", "~SIZE~0", "~last~0"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~c~0#1| (_ bv0 32)) (not (bvsge (_ bv0 32) ~last~0)) (= (_ bv200000 32) ~SIZE~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9eac4ed6_189cf26b_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem27#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_11 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_11) |ULTIMATE.start_step_#t~mem27#1|) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_11)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b1370d5a_d5368bbb_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem31#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_81 (_ BitVec 32))) (and (= |ULTIMATE.start_step_#t~mem31#1| ((_ extract 7 0) v_arrayElimCell_81)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_81)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cfb51705_135af755_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem12#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_18 (_ BitVec 32))) (and (= |ULTIMATE.start_step_#t~mem12#1| ((_ extract 7 0) v_arrayElimCell_18)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_18)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cfb51705_dec98187_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem12#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_19 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_19))) (= ((_ extract 7 0) v_arrayElimCell_19) |ULTIMATE.start_step_#t~mem12#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d4c90144_9662a16e_Treesizes_16_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#in~n", "fibonacci_~n"),
		};
		final String formulaAsString = "(or (= (_ bv2 32) |fibonacci_#in~n|) (= (_ bv1 32) fibonacci_~n) (bvslt fibonacci_~n (_ bv1 32)) (not (bvslt (bvadd fibonacci_~n (_ bv4294967294 32)) (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bba51fda_2af00337_Treesizes_6_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (bvsgt (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_169c5213_e56dea7e_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "thread3Thread1of1ForFork0_~i~2"),
		};
		final String formulaAsString = "(forall ((~a~0 (_ BitVec 32)) (~b~0 (_ BitVec 32))) (or (not (bvult (_ bv0 32) ~a~0)) (bvult thread3Thread1of1ForFork0_~i~2 (bvadd ~a~0 ~b~0)) (bvult (_ bv0 32) ~b~0) (bvult (_ bv1 32) ~a~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5c89c1bb_ce6a33f_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_39~0", "ULTIMATE.start_step_~stepLocal_10~0#1"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_10~0#1|) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_39~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fb9efd5_35260cd5_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_35~0", "ULTIMATE.start_step_~stepLocal_17~0#1"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_35~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_17~0#1|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9265ee29_555e3937_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_25~0", "ULTIMATE.start_step_~stepLocal_10~0#1"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_25~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) |ULTIMATE.start_step_~stepLocal_10~0#1|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6d2e133_41c9e7c0_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem22#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_9 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_9) |ULTIMATE.start_step_#t~mem22#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_9)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1686e9f1_bd671b17_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem58#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_4 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_4) |ULTIMATE.start_step_#t~mem58#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_4)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4c264fe3_d68cd58_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem84#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_44 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_44))) (= |ULTIMATE.start_property_#t~mem84#1| ((_ extract 7 0) v_arrayElimCell_44))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7a0de3a_41536a50_Treesizes_9_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~s~0#1"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_main_~s~0#1_13| (_ BitVec 32))) (not (bvult |v_ULTIMATE.start_main_~s~0#1_13| (bvadd (bvmul |ULTIMATE.start_main_~s~0#1| (_ bv4294967295 32)) |v_ULTIMATE.start_main_~s~0#1_13|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7d48c81_342fed48_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem9#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_37 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_37)) (_ bv0 32)) (= ((_ extract 7 0) v_arrayElimCell_37) |ULTIMATE.start_step_#t~mem9#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7d48c81_4543c04d_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem9#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_48 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_48) |ULTIMATE.start_step_#t~mem9#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_48)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7d48c81_86e48dfa_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem9#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_45 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_45)) (_ bv0 32)) (= ((_ extract 7 0) v_arrayElimCell_45) |ULTIMATE.start_step_#t~mem9#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7d48c81_97996874_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem9#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_41 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_41) |ULTIMATE.start_step_#t~mem9#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_41)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_13c79d43_8f7714fb_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem79#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_67 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem79#1| ((_ extract 7 0) v_arrayElimCell_67)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_67)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_31b131a9_30f9ea52_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem88#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_18 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem88#1| ((_ extract 7 0) v_arrayElimCell_18)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_18)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_31b131a9_44e295e9_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem88#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_19 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_19))) (= |ULTIMATE.start_property_#t~mem88#1| ((_ extract 7 0) v_arrayElimCell_19))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_31b131a9_f5a684d9_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem88#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_17 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_17))) (= |ULTIMATE.start_property_#t~mem88#1| ((_ extract 7 0) v_arrayElimCell_17))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4c264fe3_7c835c26_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem84#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_45 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem84#1| ((_ extract 7 0) v_arrayElimCell_45)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_45)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4c264fe3_a76b43fa_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem84#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_35 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem84#1| ((_ extract 7 0) v_arrayElimCell_35)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_35)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6d2e133_56b8941_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem22#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_26 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_26) |ULTIMATE.start_step_#t~mem22#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_26)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9a6f8788_4d55c89f_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem89#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_94 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_94))) (= |ULTIMATE.start_property_#t~mem89#1| ((_ extract 7 0) v_arrayElimCell_94))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9a6f8788_970ae4e4_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem89#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_24 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem89#1| ((_ extract 7 0) v_arrayElimCell_24)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_24)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9a6f8788_e95646ec_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem89#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_31 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem89#1| ((_ extract 7 0) v_arrayElimCell_31)) (not (= ((_ extract 7 0) v_arrayElimCell_31) (_ bv0 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2064600_14d5a34d_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem91#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_34 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem91#1| ((_ extract 7 0) v_arrayElimCell_34)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_34)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2064600_4f98a024_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem91#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_39 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem91#1| ((_ extract 7 0) v_arrayElimCell_39)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_39)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2064600_7791e07e_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem91#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_27 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem91#1| ((_ extract 7 0) v_arrayElimCell_27)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_27)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2064600_97b5b98a_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem91#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_14 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem91#1| ((_ extract 7 0) v_arrayElimCell_14)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_14)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2064600_a7e80ebc_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem91#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_55 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_55))) (= |ULTIMATE.start_property_#t~mem91#1| ((_ extract 7 0) v_arrayElimCell_55))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2064600_adc84516_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem91#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_20 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem91#1| ((_ extract 7 0) v_arrayElimCell_20)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_20)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2064600_c15388e5_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem91#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_11 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_11))) (= |ULTIMATE.start_property_#t~mem91#1| ((_ extract 7 0) v_arrayElimCell_11))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2064600_d27a02b7_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem91#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_49 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_49))) (= |ULTIMATE.start_property_#t~mem91#1| ((_ extract 7 0) v_arrayElimCell_49))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2064600_dfb27b16_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem91#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_47 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem91#1| ((_ extract 7 0) v_arrayElimCell_47)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_47)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_62b6d4f3_f9125e83_Treesizes_13_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_8~0", "~var_1_6~0", "~var_1_7~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_7~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_6~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_8~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a3ec27c9_20e6d9b_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem31#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_34 (_ BitVec 32))) (and (= |ULTIMATE.start_step_#t~mem31#1| ((_ extract 7 0) v_arrayElimCell_34)) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_34)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ca9f9597_bb7d3b9d_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(= (bvurem |ULTIMATE.start_main_~y~0#1| (_ bv2 32)) (bvurem (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv2 32)) (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1686e9f1_600fbd00_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem58#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_23 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_23) |ULTIMATE.start_step_#t~mem58#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_23)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1686e9f1_b06749e1_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem58#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_11 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_11) |ULTIMATE.start_step_#t~mem58#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_11)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1686e9f1_f9b1384a_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem58#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_10 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_10)) (_ bv0 32)) (= ((_ extract 7 0) v_arrayElimCell_10) |ULTIMATE.start_step_#t~mem58#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a3ec27c9_4e001543_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem31#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_25 (_ BitVec 32))) (and (= |ULTIMATE.start_step_#t~mem31#1| ((_ extract 7 0) v_arrayElimCell_25)) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_25)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_13c79d43_24fbbafd_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem79#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_110 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem79#1| ((_ extract 7 0) v_arrayElimCell_110)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_110)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_13c79d43_81849b66_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem79#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_123 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_123))) (= |ULTIMATE.start_property_#t~mem79#1| ((_ extract 7 0) v_arrayElimCell_123))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_31b131a9_c39a972e_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem88#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_123 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_123))) (= |ULTIMATE.start_property_#t~mem88#1| ((_ extract 7 0) v_arrayElimCell_123))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_594f14a1_333ac4a0_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem123#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_69 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_69))) (= ((_ extract 7 0) v_arrayElimCell_69) |ULTIMATE.start_property_#t~mem123#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_594f14a1_6dca2c73_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem123#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_62 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_62))) (= ((_ extract 7 0) v_arrayElimCell_62) |ULTIMATE.start_property_#t~mem123#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_594f14a1_73b941a9_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem123#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_31 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_31) |ULTIMATE.start_property_#t~mem123#1|) (not (= ((_ extract 7 0) v_arrayElimCell_31) (_ bv0 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_95bf42db_77fb17d6_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem138#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_89 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_89))) (= ((_ extract 7 0) v_arrayElimCell_89) |ULTIMATE.start_property_#t~mem138#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c92a0dab_d35450ad_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem146#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_70 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_70) |ULTIMATE.start_property_#t~mem146#1|) (not (= ((_ extract 7 0) v_arrayElimCell_70) (_ bv0 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c92a0dab_dbb6c2a0_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem146#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_57 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_57))) (= ((_ extract 7 0) v_arrayElimCell_57) |ULTIMATE.start_property_#t~mem146#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c92a0dab_e4b3d6ad_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem146#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_39 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_39))) (= ((_ extract 7 0) v_arrayElimCell_39) |ULTIMATE.start_property_#t~mem146#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_794ca2_2028b99f_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_2~0#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_12 (_ BitVec 32))) (and (not (= ((_ extract 7 0) v_arrayElimCell_12) (_ bv0 8))) (= ((_ extract 7 0) v_arrayElimCell_12) |ULTIMATE.start_step_~stepLocal_2~0#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_794ca2_520e99ef_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_2~0#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_29 (_ BitVec 32))) (and (= |ULTIMATE.start_step_~stepLocal_2~0#1| ((_ extract 7 0) v_arrayElimCell_29)) (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_29)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bc63bd3d_859af6c9_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_55| (_ BitVec 32))) (or (not (bvsge (bvadd (_ bv13 32) |v_fibonacci_#t~ret4_BEFORE_CALL_55|) (_ bv34 32))) (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_55| |fibonacci_#res|) (_ bv34 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_11cf5e23_c8be9a2_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_6~0#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_71 (_ BitVec 32))) (and (not (= ((_ extract 7 0) v_arrayElimCell_71) (_ bv0 8))) (= ((_ extract 7 0) v_arrayElimCell_71) |ULTIMATE.start_step_~stepLocal_6~0#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cc0c8e90_1980bd4e_Treesizes_19_14() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_4~0", "~var_1_2~0", "~var_1_3~0"),
		};
		final String formulaAsString = "(and (or (not (= ~var_1_3~0 (_ bv0 8))) (not (= ~var_1_4~0 (_ bv0 8)))) (or (not (= ~var_1_4~0 (_ bv0 8))) (not (= ~var_1_2~0 (_ bv0 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_11cf5e23_75bc1dfc_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_~stepLocal_6~0#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_82 (_ BitVec 32))) (and (not (= (_ bv0 8) ((_ extract 7 0) v_arrayElimCell_82))) (= |ULTIMATE.start_step_~stepLocal_6~0#1| ((_ extract 7 0) v_arrayElimCell_82))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_dda4f0ae_c0134332_Treesizes_13_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~k~0#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_8 (_ BitVec 32))) (= (_ bv0 32) (bvneg (bvadd (bvmul (_ bv4294967295 32) (bvneg v_arrayElimCell_8)) |ULTIMATE.start_main_~k~0#1| (bvmul v_arrayElimCell_8 (_ bv4294967295 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9f11acb3_a366babf_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_252| (_ BitVec 32))) (or (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_252| |fibonacci_#res|) (_ bv34 32)) (not (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_252| (_ bv34 32)) (_ bv34 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a77d7d81_f470a16b_Treesizes_14_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~a~0", "thread1Thread1of1ForFork2_~i~0"),
		};
		final String formulaAsString = "(or (bvult thread1Thread1of1ForFork2_~i~0 ~a~0) (forall ((~b~0 (_ BitVec 32))) (or (bvult (_ bv0 32) (bvadd ~a~0 ~b~0)) (bvult (_ bv0 32) ~b~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a92b60f5_4063d702_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (= (_ bv2 32) |isEven_#in~n|) (forall ((|v_isOdd_#in~n_BEFORE_CALL_6| (_ BitVec 32))) (= (_ bv1 32) (bvsrem |v_isOdd_#in~n_BEFORE_CALL_6| (_ bv2 32))))) (= (_ bv1 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fb2f4309_e99293e7_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (= (_ bv1 32) |isEven_#in~n|) (forall ((|v_isOdd_#in~n_BEFORE_CALL_4| (_ BitVec 32))) (= (bvsrem |v_isOdd_#in~n_BEFORE_CALL_4| (_ bv2 32)) (_ bv0 32)))) (= (_ bv0 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_44080e26_a43ec067_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (forall ((|v_isOdd_#in~n_BEFORE_CALL_21| (_ BitVec 32))) (= (bvsrem |v_isOdd_#in~n_BEFORE_CALL_21| (_ bv2 32)) (_ bv1 32))) (= (_ bv4 32) |isEven_#in~n|)) (= (_ bv1 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6d681d0_4f489300_Treesizes_13_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_24~0", "~var_1_23~0", "~var_1_22~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_23~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_24~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_22~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b0bf240d_afdcf203_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (= (_ bv3 32) |isEven_#in~n|) (forall ((|v_isOdd_#in~n_BEFORE_CALL_13| (_ BitVec 32))) (= (_ bv0 32) (bvsrem |v_isOdd_#in~n_BEFORE_CALL_13| (_ bv2 32))))) (= (_ bv0 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b0bf240d_c61b36d6_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (= (_ bv3 32) |isEven_#in~n|) (forall ((|v_isOdd_#in~n_BEFORE_CALL_17| (_ BitVec 32))) (= (_ bv0 32) (bvsrem |v_isOdd_#in~n_BEFORE_CALL_17| (_ bv2 32))))) (= (_ bv0 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_de7352ea_2f207100_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (forall ((|v_isOdd_#in~n_BEFORE_CALL_39| (_ BitVec 32))) (= (_ bv0 32) (bvsrem |v_isOdd_#in~n_BEFORE_CALL_39| (_ bv2 32)))) (= (_ bv7 32) |isEven_#in~n|)) (= (_ bv0 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e36789ac_602cac17_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (forall ((|v_isOdd_#in~n_BEFORE_CALL_47| (_ BitVec 32))) (= (_ bv1 32) (bvsrem |v_isOdd_#in~n_BEFORE_CALL_47| (_ bv2 32)))) (= (_ bv8 32) |isEven_#in~n|)) (= (_ bv1 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_622a1f2a_6e335387_Treesizes_13_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_12~0", "~var_1_11~0", "~var_1_10~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_10~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_12~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_11~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_66b51e31_8d83b20f_Treesizes_13_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_65~0", "~var_1_64~0", "~var_1_63~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_63~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_64~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_65~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f9c9f9a1_4c5b787f_Treesizes_13_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_27~0", "~var_1_26~0", "~var_1_25~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_25~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_27~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_26~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fab631b3_e3ab4e8e_Treesizes_13_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_25~0", "~var_1_24~0", "~var_1_23~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_23~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_25~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_24~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2c92d8ab_79144aff_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (forall ((|v_isOdd_#in~n_BEFORE_CALL_89| (_ BitVec 32))) (= (_ bv1 32) (bvsrem |v_isOdd_#in~n_BEFORE_CALL_89| (_ bv2 32)))) (= (_ bv12 32) |isEven_#in~n|)) (= (_ bv1 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2dad18a_fdea9845_Treesizes_14_14() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~g2v_new~0", "~g1v_new~0", "~nomsg~0"),
		};
		final String formulaAsString = "(and (= (_ bv0 8) ~g1v_new~0) (= (_ bv0 8) (bvadd (_ bv1 8) ~nomsg~0)) (= ~g2v_new~0 ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1cc6728f_bfc0e2a0_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (forall ((|v_isOdd_#in~n_BEFORE_CALL_131| (_ BitVec 32))) (= (_ bv0 32) (bvsrem |v_isOdd_#in~n_BEFORE_CALL_131| (_ bv2 32)))) (= (_ bv15 32) |isEven_#in~n|)) (= (_ bv0 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3702139a_bd756ab0_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (forall ((|v_isOdd_#in~n_BEFORE_CALL_116| (_ BitVec 32))) (= (_ bv1 32) (bvsrem |v_isOdd_#in~n_BEFORE_CALL_116| (_ bv2 32)))) (= (_ bv14 32) |isEven_#in~n|)) (= (_ bv1 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_74ee010e_7eeb28f_Treesizes_15_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_9~0", "~var_1_6~0", "~var_1_7~0"),
		};
		final String formulaAsString = "(and (= ~var_1_6~0 (_ bv0 8)) (or (= ~var_1_9~0 (_ bv0 8)) (forall ((~var_1_8~0 (_ BitVec 8))) (not (= ((_ sign_extend 24) ~var_1_8~0) ((_ sign_extend 24) ~var_1_7~0))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7d51a86e_429986c4_Treesizes_13_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_9~0", "~var_1_37~0", "~var_1_38~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_38~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_9~0) (_ bv0 32)) (bvsge ((_ zero_extend 24) ~var_1_37~0) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_95da27d5_7bbae80d_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (forall ((|v_isOdd_#in~n_BEFORE_CALL_102| (_ BitVec 32))) (= (_ bv0 32) (bvsrem |v_isOdd_#in~n_BEFORE_CALL_102| (_ bv2 32)))) (= (_ bv13 32) |isEven_#in~n|)) (= (_ bv0 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a7813e82_fa4537ae_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(and (or (= (_ bv16 32) |isEven_#in~n|) (forall ((|v_isOdd_#in~n_BEFORE_CALL_147| (_ BitVec 32))) (= (_ bv1 32) (bvsrem |v_isOdd_#in~n_BEFORE_CALL_147| (_ bv2 32))))) (= (_ bv1 32) |isEven_#res|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a7b5d519_cc1713d1_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~side1Failed_History_1~0", "read_side1_failed_history_#res"),
		};
		final String formulaAsString = "(and (= (_ bv0 8) ~side1Failed_History_1~0) (or (= (_ bv0 8) |read_side1_failed_history_#res|) (not (= (_ bv0 8) ~side1Failed_History_1~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b35e4647_83b050c0_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "read_side2_failed_history_#res", "~side2Failed_History_1~0"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 8) ~side2Failed_History_1~0)) (= (_ bv0 8) |read_side2_failed_history_#res|)) (= (_ bv0 8) ~side2Failed_History_1~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bccf0a0_3b22a801_Treesizes_14_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_97| (_ BitVec 32))) (or (not (bvsge (bvadd (_ bv29 32) |v_fibonacci_#t~ret4_BEFORE_CALL_97|) (_ bv34 32))) (bvsge (bvadd (_ bv26 32) |v_fibonacci_#t~ret4_BEFORE_CALL_97| |fibonacci_#res|) (_ bv34 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_38fc3460_ee559ec4_Treesizes_14_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_89| (_ BitVec 32))) (or (not (bvsge (bvadd (_ bv26 32) |v_fibonacci_#t~ret4_BEFORE_CALL_89|) (_ bv34 32))) (bvsge (bvadd (_ bv21 32) |v_fibonacci_#t~ret4_BEFORE_CALL_89| |fibonacci_#res|) (_ bv34 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fff7a1b1_5af74a13_Treesizes_14_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_76| (_ BitVec 32))) (or (bvsge (bvadd (_ bv13 32) |v_fibonacci_#t~ret4_BEFORE_CALL_76| |fibonacci_#res|) (_ bv34 32)) (not (bvsge (bvadd (_ bv21 32) |v_fibonacci_#t~ret4_BEFORE_CALL_76|) (_ bv34 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8b91ee27_381202c5_Treesizes_13_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_17~0", "~var_1_16~0", "~var_1_15~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_17~0) (_ bv0 32)) (bvsge ((_ zero_extend 24) ~var_1_15~0) (_ bv1 32)) (bvsle ((_ zero_extend 24) ~var_1_16~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c4a6fe6c_32667a5c_Treesizes_16_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~Y~0"),
		};
		final String formulaAsString = "(exists ((thread2Thread1of1ForFork0_~x~1 (_ BitVec 32))) (and (bvslt (bvadd thread2Thread1of1ForFork0_~x~1 (_ bv4294967295 32)) (_ bv10000 32)) (not (bvslt thread2Thread1of1ForFork0_~x~1 (_ bv10000 32))) (= (bvmul thread2Thread1of1ForFork0_~x~1 (_ bv2 32)) ~Y~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c4a6fe6c_327f8129_Treesizes_16_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~Y~0"),
		};
		final String formulaAsString = "(exists ((thread1Thread1of1ForFork1_~x~0 (_ BitVec 32))) (and (not (bvslt thread1Thread1of1ForFork1_~x~0 (_ bv10000 32))) (bvslt (bvadd thread1Thread1of1ForFork1_~x~0 (_ bv4294967295 32)) (_ bv10000 32)) (= ~Y~0 (bvmul thread1Thread1of1ForFork1_~x~0 (_ bv2 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d82b1cfe_ea26c47e_Treesizes_13_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_19~0", "~var_1_21~0", "~var_1_20~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_19~0) (_ bv0 32)) (bvsge ((_ zero_extend 24) ~var_1_21~0) (_ bv1 32)) (bvsle ((_ zero_extend 24) ~var_1_20~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3a21e13f_5886655e_Treesizes_17_16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_6~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (or (= ~var_1_1~0 (_ bv0 8)) (= ~var_1_6~0 (_ bv0 8))) (or (= ((_ zero_extend 24) ~var_1_1~0) (_ bv1 32)) (not (= ~var_1_6~0 (_ bv0 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3f0ee1a2_e30b59b3_Treesizes_10_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res"),
		};
		final String formulaAsString = "(exists ((|v_mult_#t~ret5_156| (_ BitVec 32))) (= (bvmul (_ bv4 32) |v_mult_#t~ret5_156|) (bvadd (_ bv1 32) (bvmul (_ bv3 32) |mult_#res|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b101bad_5282bfde_Treesizes_14_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_105| (_ BitVec 32))) (or (not (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_105| (_ bv32 32)) (_ bv34 32))) (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_105| (_ bv31 32) |fibonacci_#res|) (_ bv34 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b101bad_888886e6_Treesizes_14_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_107| (_ BitVec 32))) (or (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_107| (_ bv32 32) |fibonacci_#res|) (_ bv34 32)) (not (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_107| (_ bv33 32)) (_ bv34 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3fc8c3b8_436f0c44_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_14_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= ((_ extract 7 0) (select |#memory_int| ~var_1_14_Pointer~0.base)) (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_73534e84_43db3d42_Treesizes_14_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_102| (_ BitVec 32))) (or (not (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_102| (_ bv31 32)) (_ bv34 32))) (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_102| (_ bv29 32) |fibonacci_#res|) (_ bv34 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a00b9eb4_f7351f37_Treesizes_14_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_108| (_ BitVec 32))) (or (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_108| (_ bv33 32) |fibonacci_#res|) (_ bv34 32)) (not (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_108| (_ bv33 32)) (_ bv34 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c083b321_f167bb9b_Treesizes_18_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#in~n", "fibonacci_~n"),
		};
		final String formulaAsString = "(or (not (bvslt (bvadd fibonacci_~n (_ bv4294967293 32)) (_ bv1 32))) (= (_ bv3 32) |fibonacci_#in~n|) (bvslt (bvadd fibonacci_~n (_ bv4294967295 32)) (_ bv1 32)) (= (_ bv2 32) fibonacci_~n))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3cd2d1a9_e3a7d1c_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_1~0", "stopRequestedInDirection__wrappee__empty_#t~ret15"),
		};
		final String formulaAsString = "(and (or (= (_ bv0 32) |stopRequestedInDirection__wrappee__empty_#t~ret15|) (not (= (_ bv0 32) ~calls_1~0))) (= (_ bv0 32) ~calls_1~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5d1e8a0d_7611e026_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvule (_ bv536870911 32) (select |#memory_int| (bvadd (_ bv12 32) |~#WrapperStruct00~0.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c0d5288d_435430a3_Treesizes_16_13() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(and (exists ((~n~0 (_ BitVec 32))) (and (not (bvslt (_ bv1 32) ~n~0)) (bvslt ~counter~0 ~n~0))) (bvsge ~counter~0 (_ bv0 32)) (bvslt ~counter~0 (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_57810256_a7546916_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "stopRequestedInDirection__wrappee__empty_#t~ret60", "~calls_1~0"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ~calls_1~0)) (= (_ bv0 32) |stopRequestedInDirection__wrappee__empty_#t~ret60|)) (= (_ bv0 32) ~calls_1~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9c806593_be65f104_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(forall ((v_mult_~n_235 (_ BitVec 32))) (not (= |ULTIMATE.start_main_~n~0#1| (bvadd (_ bv1 32) (bvmul (_ bv4 32) v_mult_~n_235)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5636be2f_52bf981f_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_1~0", "stopRequestedInDirection__wrappee__empty_~tmp___3~1"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ~calls_1~0)) (= (_ bv0 32) stopRequestedInDirection__wrappee__empty_~tmp___3~1)) (= (_ bv0 32) ~calls_1~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_90e7a977_d0358e14_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_1~0", "stopRequestedInDirection__wrappee__empty_~tmp___3~2"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) ~calls_1~0) (or (= (_ bv0 32) stopRequestedInDirection__wrappee__empty_~tmp___3~2) (not (= (_ bv0 32) ~calls_1~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7a1808f9_175b20e9_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_1~0", "stopRequestedInDirection__wrappee__weight_#t~ret29"),
		};
		final String formulaAsString = "(and (or (= |stopRequestedInDirection__wrappee__weight_#t~ret29| (_ bv0 32)) (not (= (_ bv0 32) ~calls_1~0))) (= (_ bv0 32) ~calls_1~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ab5996ca_c983e041_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_1~0", "stopRequestedInDirection__wrappee__weight_#t~ret27"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ~calls_1~0)) (= |stopRequestedInDirection__wrappee__weight_#t~ret27| (_ bv0 32))) (= (_ bv0 32) ~calls_1~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fcfbdbcb_ebc57494_Treesizes_15_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~end~0#1.base"),
		};
		final String formulaAsString = "(and (exists ((v_ArrVal_24 (_ BitVec 32))) (and (bvugt v_ArrVal_24 (_ bv0 32)) (not (= v_ArrVal_24 (bvadd (_ bv4 32) |ULTIMATE.start_main_~end~0#1.base|))))) (bvugt |ULTIMATE.start_main_~end~0#1.base| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5f810bb0_9bed0cac_Treesizes_16_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id1~0", "~nomsg~0"),
		};
		final String formulaAsString = "(and (= (_ bv0 8) (bvadd (_ bv1 8) ~nomsg~0)) (exists ((~send1~0 (_ BitVec 8))) (= ((_ sign_extend 24) ~id1~0) ((_ sign_extend 24) ~send1~0))) (bvsge ((_ sign_extend 24) ~id1~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bf0ced58_3fcc98a0_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~calls_1~0", "stopRequestedInDirection__wrappee__weight_~tmp___3~2"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ~calls_1~0)) (= (_ bv0 32) stopRequestedInDirection__wrappee__weight_~tmp___3~2)) (= (_ bv0 32) ~calls_1~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c7c2cf51_5a12dad5_Treesizes_16_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id2~0", "~nomsg~0"),
		};
		final String formulaAsString = "(and (bvsge ((_ sign_extend 24) ~id2~0) (_ bv0 32)) (= (_ bv0 8) (bvadd (_ bv1 8) ~nomsg~0)) (exists ((~send2~0 (_ BitVec 8))) (= ((_ sign_extend 24) ~send2~0) ((_ sign_extend 24) ~id2~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f1db0d16_89bc79ef_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "stopRequestedInDirection__wrappee__weight_~tmp___3~1", "~calls_1~0"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ~calls_1~0)) (= (_ bv0 32) stopRequestedInDirection__wrappee__weight_~tmp___3~1)) (= (_ bv0 32) ~calls_1~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8edbb6d2_94eee39_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (bvsgt (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv8 32))) (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e057edd6_e3102940_Treesizes_13_13() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_42~0", "~var_1_43~0", "~var_1_41~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_43~0)) (not (= (_ bv0 8) ~var_1_42~0)) (not (= (_ bv0 8) ~var_1_41~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7adf5571_79848261_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (bvsgt (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv4 32))) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8ca832c5_9d494031_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_#t~mem10#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_2 (_ BitVec 32))) (and (not (= ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_2)) (_ bv0 32))) (= ((_ extract 7 0) v_arrayElimCell_2) |ULTIMATE.start_main_#t~mem10#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cabed77d_6bb122de_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_#t~mem11#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_2 (_ BitVec 32))) (and (not (= ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_2)) (_ bv0 32))) (= ((_ extract 7 0) v_arrayElimCell_2) |ULTIMATE.start_main_#t~mem11#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9929a26c_81d4b8f4_Treesizes_11_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~y~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~x~0#1| (_ BitVec 32))) (or (bvugt |ULTIMATE.start_main_~x~0#1| |ULTIMATE.start_main_~y~0#1|) (= |ULTIMATE.start_main_~y~0#1| |ULTIMATE.start_main_~x~0#1|) (= |ULTIMATE.start_main_~x~0#1| (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_439fc69d_9ec8d1c8_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (bvsgt (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv12 32))) (_ bv3 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_befb7800_20d72fde_Treesizes_11_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem19#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_4 (_ BitVec 32))) (and (bvsge ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_4)) (_ bv0 32)) (= ((_ extract 7 0) v_arrayElimCell_4) |ULTIMATE.start_step_#t~mem19#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_32fc07b3_8490efdb_Treesizes_12_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~x~0#1_22| (_ BitVec 32))) (and (= (bvadd |v_ULTIMATE.start_main_~x~0#1_22| (bvneg |v_ULTIMATE.start_main_~x~0#1_22|)) |ULTIMATE.start_main_~x~0#1|) (not (= (_ bv0 32) |v_ULTIMATE.start_main_~x~0#1_22|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a0152660_e54bd4d5_Treesizes_5_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "assert_byte_from_buffer_matches_#t~mem589", "assert_byte_from_buffer_matches_#t~mem588"),
		};
		final String formulaAsString = "(= ((_ zero_extend 24) |assert_byte_from_buffer_matches_#t~mem589|) ((_ zero_extend 24) |assert_byte_from_buffer_matches_#t~mem588|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_befb7800_30fb1d6f_Treesizes_11_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem19#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_12 (_ BitVec 32))) (and (bvsge ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_12)) (_ bv0 32)) (= ((_ extract 7 0) v_arrayElimCell_12) |ULTIMATE.start_step_#t~mem19#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4225af64_96e29163_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= (_ bv5 32) (bvand (bvadd (_ bv8 32) (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|)) (_ bv5 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2c8eaf2_44cb0b49_Treesizes_11_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem30#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_133 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_133) |ULTIMATE.start_step_#t~mem30#1|) (bvsge ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_133)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_4ef67f14_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_1 (_ BitVec 32))) (and (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_1))) |ULTIMATE.start_step_#t~mem13#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_1)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_567269c3_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_5 (_ BitVec 32))) (and (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_5))) |ULTIMATE.start_step_#t~mem13#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_5)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_d4809497_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_9 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_9)) (_ bv0 32)) (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_9))) |ULTIMATE.start_step_#t~mem13#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9a1a8200_3d6e26a0_Treesizes_18_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_2~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (or (and (not (bvslt ~var_1_2~0 (_ bv0 32))) (= ~var_1_1~0 ~var_1_2~0)) (= ~var_1_1~0 (bvneg ~var_1_2~0))) (not (bvslt ~var_1_1~0 ~var_1_2~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a4a6673c_c2faa0d3_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= (_ bv0 32) (bvurem (bvadd (_ bv2 32) (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|)) (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b1a653fe_7d3c258a_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= (bvurem (bvadd (_ bv4 32) (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|)) (_ bv4 32)) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_1337d7d_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_69 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_69)) (_ bv0 32)) (= |ULTIMATE.start_step_#t~mem13#1| ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_69))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_50f8678_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_56 (_ BitVec 32))) (and (= |ULTIMATE.start_step_#t~mem13#1| ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_56)))) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_56)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3eaf80c3_9e519b74_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem78#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_28 (_ BitVec 32))) (and (bvslt ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_28)) (_ bv1 32)) (= |ULTIMATE.start_property_#t~mem78#1| ((_ extract 7 0) v_arrayElimCell_28))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ce71a7e8_b0e3b09d_Treesizes_14_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~sn~0#1"),
		};
		final String formulaAsString = "(or (= (_ bv0 32) |ULTIMATE.start_main_~sn~0#1|) (forall ((|ULTIMATE.start_main_~n~0#1| (_ BitVec 32))) (= (bvudiv (bvmul (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv1 32)) |ULTIMATE.start_main_~n~0#1|) (_ bv2 32)) |ULTIMATE.start_main_~sn~0#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_35964e82_487c04d9_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem14#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_71 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_71)) (_ bv0 32)) (= |ULTIMATE.start_step_#t~mem14#1| ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_71))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_35964e82_a1acb99e_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem14#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_29 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_29)) (_ bv0 32)) (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_29))) |ULTIMATE.start_step_#t~mem14#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_1442b280_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_66 (_ BitVec 32))) (and (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_66))) |ULTIMATE.start_step_#t~mem13#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_66)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_5a4d3e6f_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_27 (_ BitVec 32))) (and (= |ULTIMATE.start_step_#t~mem13#1| ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_27)))) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_27)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_61323be1_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_95 (_ BitVec 32))) (and (= |ULTIMATE.start_step_#t~mem13#1| ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_95)))) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_95)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_80916a3f_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_34 (_ BitVec 32))) (and (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_34))) |ULTIMATE.start_step_#t~mem13#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_34)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_8d693768_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_86 (_ BitVec 32))) (and (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_86))) |ULTIMATE.start_step_#t~mem13#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_86)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_da3e6eac_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_50 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_50)) (_ bv0 32)) (= |ULTIMATE.start_step_#t~mem13#1| ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_50))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_e68722df_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_41 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_41)) (_ bv0 32)) (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_41))) |ULTIMATE.start_step_#t~mem13#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b6a66f8_f33409bc_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem13#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_76 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_76)) (_ bv0 32)) (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_76))) |ULTIMATE.start_step_#t~mem13#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b9861c04_1a001d5f_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem10#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_79 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_79)) (_ bv0 32)) (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_79))) |ULTIMATE.start_step_#t~mem10#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1937b5cd_640c57ac_Treesizes_13_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_check_~a#1.base_BEFORE_CALL_1| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_check_~a#1.base_BEFORE_CALL_1|))) (= (select |#memory_int| (_ bv8 32)) ((_ sign_extend 24) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_381faa68_ea4a9ef8_Treesizes_11_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem107#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_12 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_12) |ULTIMATE.start_property_#t~mem107#1|) (bvslt (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_12)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9a6c54d5_6a4933e2_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~__CS_ret_PREEMPTED~0", "~__CS_ret~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ~__CS_ret_PREEMPTED~0))))) (= ~__CS_ret_PREEMPTED~0 ~__CS_ret~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_35964e82_7fc0bc56_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem14#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_130 (_ BitVec 32))) (and (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_130))) |ULTIMATE.start_step_#t~mem14#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_130)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6b3b011d_98ce2791_Treesizes_6_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (bvule (_ bv1 32) (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1937b5cd_9bc59aac_Treesizes_13_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (select |#memory_int| (_ bv8 32)) ((_ sign_extend 24) (_ bv0 8))) (exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_1| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_1|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ee1ed95_a32502b4_Treesizes_12_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "node_create_~temp~0#1.base", "old(#HeapAllocations)"),
		};
		final String formulaAsString = "(and (not (= |old(#HeapAllocations)| (_ bv0 32))) (= |old(#HeapAllocations)| |node_create_~temp~0#1.base|) (not (= (_ bv0 32) |node_create_~temp~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_28593eab_fb8ee58f_Treesizes_7_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_is_relaxed_prefix_~pat_length#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_is_relaxed_prefix_~a_length#1| (_ BitVec 32))) (not (bvugt |ULTIMATE.start_is_relaxed_prefix_~pat_length#1| (bvadd (_ bv1 32) |ULTIMATE.start_is_relaxed_prefix_~a_length#1|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c0cdd204_2d16cd96_Treesizes_13_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ((_ sign_extend 24) (_ bv0 8)) (select |#memory_int| (_ bv2 32))) (exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_2| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_2|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cf5e5ec6_133e2635_Treesizes_11_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem74#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_18 (_ BitVec 32))) (and (bvsge ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_18)) (_ bv0 32)) (= |ULTIMATE.start_property_#t~mem74#1| ((_ extract 7 0) v_arrayElimCell_18))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a2613468_6c4ad2c5_Treesizes_10_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~leader_len~0#1"),
		};
		final String formulaAsString = "(or (bvsle (_ bv0 32) (bvadd (_ bv2 32) |ULTIMATE.start_main_~leader_len~0#1|)) (not (bvsgt |ULTIMATE.start_main_~leader_len~0#1| (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b4a6b791_73d9b919_Treesizes_14_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~p3_old~0", "~id3~0", "~nomsg~0"),
		};
		final String formulaAsString = "(or (not (= ((_ sign_extend 24) ~nomsg~0) ((_ sign_extend 24) ~p3_old~0))) (forall ((|ULTIMATE.start_node3_~m3~0#1| (_ BitVec 8))) (not (= ((_ sign_extend 24) ~id3~0) ((_ sign_extend 24) |ULTIMATE.start_node3_~m3~0#1|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8e56bbc4_c3a7d137_Treesizes_16_16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~g2v_new~0", "~g1v_new~0", "~nomsg~0"),
		};
		final String formulaAsString = "(and (= (bvadd ~g2v_new~0 (_ bv1 8)) (_ bv0 8)) (= ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8))) ~g1v_new~0) (= (_ bv0 8) (bvadd (_ bv1 8) ~nomsg~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5b5e21b0_b91f897f_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_15_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= (_ bv0 8) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| ~var_1_15_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_92e499d7_9bd64a7_Treesizes_19_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~n"),
		};
		final String formulaAsString = "(forall ((|v_mult_#in~n_BEFORE_CALL_19| (_ BitVec 32))) (or (= (bvadd (_ bv1 32) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_19|)) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_19|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_32017391_a69e1a9b_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_task_~n#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) |ULTIMATE.start_task_~n#1.base|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4b0f2bed_4c4be70f_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem78#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_25 (_ BitVec 32))) (and (not (bvslt ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_25)) (_ bv1 32))) (= |ULTIMATE.start_property_#t~mem78#1| ((_ extract 7 0) v_arrayElimCell_25))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4b0f2bed_5fd2743d_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem78#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_36 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem78#1| ((_ extract 7 0) v_arrayElimCell_36)) (not (bvslt ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_36)) (_ bv1 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4b0f2bed_9dba0951_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem78#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_29 (_ BitVec 32))) (and (not (bvslt ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_29)) (_ bv1 32))) (= |ULTIMATE.start_property_#t~mem78#1| ((_ extract 7 0) v_arrayElimCell_29))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_92e499d7_3a60c788_Treesizes_19_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~n"),
		};
		final String formulaAsString = "(forall ((|v_mult_#in~n_BEFORE_CALL_13| (_ BitVec 32))) (or (= (bvadd (_ bv1 32) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_13|)) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_13|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_92e499d7_8ad9e9b6_Treesizes_19_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~n"),
		};
		final String formulaAsString = "(forall ((|v_mult_#in~n_BEFORE_CALL_35| (_ BitVec 32))) (or (= (bvadd (_ bv1 32) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_35|)) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_35|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_92e499d7_acad3f69_Treesizes_19_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~n"),
		};
		final String formulaAsString = "(forall ((|v_mult_#in~n_BEFORE_CALL_45| (_ BitVec 32))) (or (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_45|))) (= (bvadd (_ bv1 32) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_45|)) (bvadd |mult_#in~n| |mult_#res|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b22b3bbf_18a79357_Treesizes_10_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) (bvurem (bvadd (_ bv2 32) (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|)) (_ bv2 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5e51db81_91bef941_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem75#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_85 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem75#1| ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_85)))) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_85)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6722d7d6_e4a310c7_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem72#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_99 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_99)) (_ bv0 32)) (= |ULTIMATE.start_property_#t~mem72#1| ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_99))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_dca82f0b_32868916_Treesizes_13_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~b~0#1", "ULTIMATE.start_main_~a~0#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~b~0#1| (_ bv6 32)) (not (bvslt |ULTIMATE.start_main_~a~0#1| (_ bv6 32))) (bvslt (bvadd |ULTIMATE.start_main_~a~0#1| (_ bv4294967295 32)) (_ bv6 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_30335ec7_289eba8d_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv9 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4f343ab1_6e01f968_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv6 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a32b1395_89e4d7d6_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv3 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a9a80db5_f12aa99a_Treesizes_11_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~b~0#1", "ULTIMATE.start_main_~B~0#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~b~0#1| (bvudiv (bvmul |ULTIMATE.start_main_~B~0#1| (_ bv2 32)) (_ bv2 32))) (bvule |ULTIMATE.start_main_~B~0#1| (_ bv100 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2c9c29bc_37fbf921_Treesizes_19_16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~An~0", "~i_AC~0"),
		};
		final String formulaAsString = "(and (bvslt ~i_AC~0 ~An~0) (forall ((~Cn~0 (_ BitVec 32))) (or (not (bvslt (_ bv0 32) ~Cn~0)) (bvslt (_ bv1 32) ~Cn~0) (bvslt ~i_AC~0 ~Cn~0))) (bvsle ~i_AC~0 (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_19839183_55bbd141_Treesizes_16_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_30~0"),
		};
		final String formulaAsString = "(exists ((~var_1_32~0 (_ BitVec 16))) (and (bvsge (bvashr ~var_1_30~0 ((_ zero_extend 16) ~var_1_32~0)) ~var_1_30~0) (bvsge ((_ zero_extend 16) ~var_1_32~0) (_ bv1 32)) (bvsle ((_ zero_extend 16) ~var_1_32~0) (_ bv30 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1d7da984_168902a9_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv17 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_41d26606_4f013c40_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv37 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_580e7b42_efd0a5d3_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv21 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5e51db81_71c670bd_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem75#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_111 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem75#1| ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_111)))) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_111)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_72294e50_318f4818_Treesizes_19_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_3~0"),
		};
		final String formulaAsString = "(forall ((~var_1_4~0 (_ BitVec 8))) (or (not (bvsge ((_ sign_extend 24) ~var_1_4~0) (_ bv0 32))) (not (bvsgt ((_ sign_extend 24) ((_ extract 7 0) (bvadd (bvneg ((_ sign_extend 24) ~var_1_4~0)) ((_ sign_extend 24) ~var_1_3~0)))) ((_ sign_extend 24) ~var_1_3~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8eaa27a4_1c00fba3_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv11 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9663f735_8c1c44e3_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv25 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9c977896_33d780e4_Treesizes_12_12() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "addflt_~eb~0", "addflt_~ea~0"),
		};
		final String formulaAsString = "(and (exists ((v_addflt_~b_19 (_ BitVec 32))) (= (bvlshr v_addflt_~b_19 (_ bv24 32)) (bvadd addflt_~eb~0 (_ bv128 32)))) (= addflt_~ea~0 (_ bv127 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a1125242_85f53170_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem103#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_85 (_ BitVec 32))) (and (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_85))) |ULTIMATE.start_property_#t~mem103#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_85)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ae57463f_77bfbe09_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv24 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b253889d_9040a33b_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv18 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c3491b28_64398571_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "thread1Thread1of1ForFork1_~x~0", "~Y~0"),
		};
		final String formulaAsString = "(and (not (bvslt thread1Thread1of1ForFork1_~x~0 (_ bv10000 32))) (bvsle thread1Thread1of1ForFork1_~x~0 (_ bv10000 32)) (= thread1Thread1of1ForFork1_~x~0 ~Y~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_dd293648_39afe8a3_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv15 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_eacbe157_6ca82d3b_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv35 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_22334f03_a6fece80_Treesizes_7_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_9_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(bvsle ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| ~WrapperStruct00_var_1_9_Pointer~0.base))) (_ bv0 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3fc8c3b8_5c8e4a3c_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_14_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| ~var_1_14_Pointer~0.base)))) (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c4a6fe6c_b5e56d92_Treesizes_20_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~Y~0"),
		};
		final String formulaAsString = "(exists ((thread1Thread1of1ForFork1_~x~0 (_ BitVec 32))) (and (bvslt (bvadd thread1Thread1of1ForFork1_~x~0 (_ bv4294967295 32)) (_ bv10000 32)) (not (bvslt (bvadd ~Y~0 (bvmul thread1Thread1of1ForFork1_~x~0 (_ bv4294967295 32))) (_ bv10000 32))) (= ~Y~0 (bvmul thread1Thread1of1ForFork1_~x~0 (_ bv2 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8e195c5a_ce851609_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_buf_reset_harness_#t~mem1209#1"),
		};
		final String formulaAsString = "(= (concat (concat (concat ((_ extract 31 24) (_ bv0 32)) ((_ extract 23 16) (_ bv0 32))) ((_ extract 15 8) (_ bv0 32))) ((_ extract 7 0) (_ bv0 32))) |ULTIMATE.start_aws_byte_buf_reset_harness_#t~mem1209#1|)";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_88289764_b71f6c8_Treesizes_13_13() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "thread1Thread1of1ForFork1_~x~0", "~Y~0"),
		};
		final String formulaAsString = "(and (not (bvslt thread1Thread1of1ForFork1_~x~0 (_ bv10000 32))) (bvslt (bvadd ~Y~0 (_ bv4294967295 32)) (_ bv10000 32)) (= thread1Thread1of1ForFork1_~x~0 ~Y~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b5696063_e7cc291a_Treesizes_17_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_1~0"),
		};
		final String formulaAsString = "(forall ((~var_1_9~0 (_ BitVec 8))) (or (not (bvsge ((_ zero_extend 24) ~var_1_9~0) (_ bv1 32))) (= ((_ zero_extend 24) ~var_1_1~0) ((_ zero_extend 24) ~var_1_9~0)) (not (bvsle ((_ zero_extend 24) ~var_1_9~0) (_ bv1 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bbc0f9f5_7b2d768a_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv2 32) |~#WrapperStruct00~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_12cb055d_7c6947a7_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv15 32) |~#WrapperStruct00~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2f0fce4e_bb986874_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv30 32) |~#WrapperStruct00~0.base|))) (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3cdd782f_1c0b6e4c_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv19 32) |~#WrapperStruct00~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_46be48f9_c95ed19a_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv20 32) |~#WrapperStruct00~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4eddca32_9527ef17_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv16 32) |~#WrapperStruct00~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_53d64f45_1d14a197_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv45 32) |~#WrapperStruct00~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_76a2a87c_7412d41e_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv74 32) |~#WrapperStruct00~0.base|))) (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_99312126_2f5a9301_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv17 32) |~#WrapperStruct00~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9fb5c087_eabaee2d_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv11 32) |~#WrapperStruct00~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b2a37718_8bb023db_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv18 32) |~#WrapperStruct00~0.base|))) (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bf82c20d_437e56a8_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv21 32) |~#WrapperStruct00~0.base|))) (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e9364e35_789da40e_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv54 32) |~#WrapperStruct00~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_32fc07b3_4cbb2a62_Treesizes_13_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~y~0#1_21| (_ BitVec 32))) (and (not (= |ULTIMATE.start_main_~x~0#1| |v_ULTIMATE.start_main_~y~0#1_21|)) (not (bvugt |ULTIMATE.start_main_~x~0#1| |v_ULTIMATE.start_main_~y~0#1_21|)) (bvult |v_ULTIMATE.start_main_~y~0#1_21| (_ bv2 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_90318809_4f992fe5_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_8| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_8|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_90318809_77657594_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_9| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_9|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3a1f169f_4d772ea3_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_14_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= ((_ extract 7 0) (select |#memory_int| ~WrapperStruct00_var_1_14_Pointer~0.base)) (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_66cd4369_2cac510a_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_6| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_6|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_66cd4369_85565f90_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_8| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_8|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_66cd4369_f43adffd_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_7| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_7|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f43adffd_1e3c9f3c_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_9| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_9|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f43adffd_85565f90_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_8| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_8|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fdf61ea5_3c3a43e7_Treesizes_11_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~b~0#1", "ULTIMATE.start_main_~B~0#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~b~0#1| (bvudiv (bvmul |ULTIMATE.start_main_~B~0#1| (_ bv2 32)) (_ bv2 32))) (bvult |ULTIMATE.start_main_~B~0#1| (_ bv2147483647 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_14c0dc6b_3422a653_Treesizes_11_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~i~0#1"),
		};
		final String formulaAsString = "(bvsle (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv1 32) (bvneg (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv1 32)))) (bvmul |ULTIMATE.start_main_~n~0#1| (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1e3c9f3c_2fe00556_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_16| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_16|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1e3c9f3c_44e6819a_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_14| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_14|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1e3c9f3c_802de30b_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_13| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_13|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1e3c9f3c_855b2002_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_15| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_15|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1e3c9f3c_b594c64b_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_10| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_10|) (_ bv10 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1e3c9f3c_bb80fc9b_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_11| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_11|) (_ bv10 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1e3c9f3c_f0d846f5_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_12| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_12|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_48a07b68_6bbab34c_Treesizes_12_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~s~0#1"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_main_~v~0#1_9| (_ BitVec 8))) (not (bvslt ((_ zero_extend 24) ((_ extract 7 0) (bvadd ((_ zero_extend 24) |v_ULTIMATE.start_main_~v~0#1_9|) ((_ zero_extend 24) |ULTIMATE.start_main_~s~0#1|)))) ((_ zero_extend 24) |v_ULTIMATE.start_main_~v~0#1_9|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3ae969b_2ed335c3_Treesizes_19_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~n"),
		};
		final String formulaAsString = "(forall ((|v_mult_#in~n_BEFORE_CALL_33| (_ BitVec 32))) (or (not (= (bvmul |mult_#in~n| (_ bv4 32)) (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_33|))) (= (bvadd (_ bv1 32) (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_33|)) (bvadd |mult_#in~n| |mult_#res|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3ae969b_e8dfc9ae_Treesizes_19_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~n"),
		};
		final String formulaAsString = "(forall ((|v_mult_#in~n_BEFORE_CALL_43| (_ BitVec 32))) (or (not (= (bvmul |mult_#in~n| (_ bv4 32)) (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_43|))) (= (bvadd (_ bv1 32) (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_43|)) (bvadd |mult_#in~n| |mult_#res|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4aed3ee0_41bddb11_Treesizes_24_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "size_#res"),
		};
		final String formulaAsString = "(and (forall ((|v_size_#t~ret29_BEFORE_CALL_2| (_ BitVec 32))) (or (not (bvult (_ bv0 32) (bvadd (bvmul (_ bv4 32) |v_size_#t~ret29_BEFORE_CALL_2|) (_ bv4 32)))) (bvult (_ bv0 32) (bvadd (bvmul (_ bv4 32) |v_size_#t~ret29_BEFORE_CALL_2|) (_ bv4 32) (bvmul |size_#res| (_ bv4 32)))))) (= |size_#res| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4aed3ee0_5ef9076d_Treesizes_24_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "size_#res"),
		};
		final String formulaAsString = "(and (forall ((|v_size_#t~ret28_BEFORE_CALL_2| (_ BitVec 32))) (or (bvult (_ bv0 32) (bvadd (bvmul (_ bv4 32) |v_size_#t~ret28_BEFORE_CALL_2|) (_ bv4 32) (bvmul |size_#res| (_ bv4 32)))) (not (bvult (_ bv0 32) (bvadd (bvmul (_ bv4 32) |v_size_#t~ret28_BEFORE_CALL_2|) (_ bv4 32)))))) (= |size_#res| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4aed3ee0_7d846f1b_Treesizes_24_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "size_#res"),
		};
		final String formulaAsString = "(and (forall ((|v_size_#t~ret27_BEFORE_CALL_2| (_ BitVec 32))) (or (bvult (_ bv0 32) (bvadd (bvmul |v_size_#t~ret27_BEFORE_CALL_2| (_ bv4 32)) (_ bv4 32) (bvmul |size_#res| (_ bv4 32)))) (not (bvult (_ bv0 32) (bvadd (bvmul |v_size_#t~ret27_BEFORE_CALL_2| (_ bv4 32)) (_ bv4 32)))))) (= |size_#res| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4aed3ee0_9cb9e3d3_Treesizes_24_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "size_#res"),
		};
		final String formulaAsString = "(and (forall ((|v_size_#t~ret26_BEFORE_CALL_2| (_ BitVec 32))) (or (not (bvult (_ bv0 32) (bvadd (_ bv4 32) (bvmul (_ bv4 32) |v_size_#t~ret26_BEFORE_CALL_2|)))) (bvult (_ bv0 32) (bvadd (_ bv4 32) (bvmul (_ bv4 32) |v_size_#t~ret26_BEFORE_CALL_2|) (bvmul |size_#res| (_ bv4 32)))))) (= |size_#res| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_65dc130d_a481899a_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_addflt_~b#1", "ULTIMATE.start_main_~a~0#1", "ULTIMATE.start_addflt_~a#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_addflt_~b#1|) (bvult |ULTIMATE.start_main_~a~0#1| |ULTIMATE.start_addflt_~a#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8a41de47_454174c_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_i2o_dma_alloc_~addr#1.base_BEFORE_CALL_2| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_i2o_dma_alloc_~addr#1.base_BEFORE_CALL_2|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5e04e77d_72b6d497_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv20 32) |~#WrapperStruct00~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9283f536_230bede1_Treesizes_11_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~k~0#1"),
		};
		final String formulaAsString = "(and (bvslt (_ bv0 32) |ULTIMATE.start_main_~n~0#1|) (not (bvslt (_ bv1 32) |ULTIMATE.start_main_~n~0#1|)) (= |ULTIMATE.start_main_~k~0#1| (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bfaa8b8d_3f159d9_Treesizes_10_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (not (bvugt (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv4294967292 32)) (_ bv0 32))) (= |ULTIMATE.start_main_~x~0#1| |ULTIMATE.start_main_~n~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_648215bd_820556a5_Treesizes_11_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~i~0#1"),
		};
		final String formulaAsString = "(bvsle (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv2 32) (bvneg (bvadd |ULTIMATE.start_main_~i~0#1| (_ bv1 32)))) (bvmul |ULTIMATE.start_main_~n~0#1| (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9a6c54d5_5d8cb626_Treesizes_13_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~__CS_ret_PREEMPTED~0", "~__CS_ret~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ~__CS_ret_PREEMPTED~0))))) (= ((_ extract 7 0) ((_ zero_extend 24) ~__CS_ret_PREEMPTED~0)) ~__CS_ret~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2cb58625_6cebd5fc_Treesizes_12_12() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "addflt_~ma~0", "addflt_~mb~0"),
		};
		final String formulaAsString = "(and (exists ((v_addflt_~b_69 (_ BitVec 32))) (= (bvor (bvand (_ bv16777215 32) v_addflt_~b_69) (_ bv16777216 32)) addflt_~mb~0)) (= addflt_~ma~0 (_ bv33554431 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_56212f6a_711a20c4_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_step_#t~mem23#1", "ULTIMATE.start_step_~stepLocal_0~0#1"),
		};
		final String formulaAsString = "(and (bvsge |ULTIMATE.start_step_#t~mem23#1| (_ bv1073741822 32)) (= |ULTIMATE.start_step_~stepLocal_0~0#1| |ULTIMATE.start_step_#t~mem23#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_711a20c4_56212f6a_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_step_#t~mem23#1", "ULTIMATE.start_step_~stepLocal_0~0#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_step_~stepLocal_0~0#1| |ULTIMATE.start_step_#t~mem23#1|) (bvsge |ULTIMATE.start_step_~stepLocal_0~0#1| (_ bv1073741822 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3ba46193_7140f753_Treesizes_10_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (bvslt ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv1 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cf45448a_818fecab_Treesizes_23_21() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~min1~0", "~min2~0", "~M~0", "~N~0"),
		};
		final String formulaAsString = "(or (bvslt (_ bv1 32) ~N~0) (and (= ~min1~0 ~min2~0) (or (= (_ bv0 32) (bvmul ~M~0 (_ bv4 32))) (= (bvadd (_ bv2147483648 32) ~min2~0) (_ bv0 32)))) (not (bvslt ~M~0 ~N~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_607b702a_9526b86c_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (bvslt ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base))) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e8d08994_7d7573c4_Treesizes_10_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (bvslt ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv12 32) |~#WrapperStruct00~0.base|)))) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_eeb5faef_37574a83_Treesizes_12_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~bad_68_arg_0~0#1"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~var_67_arg_0~0#1_7| (_ BitVec 8))) (= |ULTIMATE.start_main_~bad_68_arg_0~0#1| ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv254 32) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_67_arg_0~0#1_7|))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4585f0cc_4b0e4010_Treesizes_12_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967292 32)) (_ bv0 32))) (= |ULTIMATE.start_main_~n~0#1| (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv4 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_72e6f070_31c8ccdd_Treesizes_12_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~n~0#1| (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv1 32))) (not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967295 32)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c4a6fe6c_160ceac7_Treesizes_23_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~Y~0"),
		};
		final String formulaAsString = "(exists ((thread1Thread1of1ForFork1_~x~0 (_ BitVec 32))) (and (bvslt (bvadd ~Y~0 (bvmul thread1Thread1of1ForFork1_~x~0 (_ bv4294967295 32)) (_ bv4294967295 32)) (_ bv10000 32)) (not (bvslt (bvadd ~Y~0 (bvmul thread1Thread1of1ForFork1_~x~0 (_ bv4294967295 32))) (_ bv10000 32))) (= ~Y~0 (bvmul thread1Thread1of1ForFork1_~x~0 (_ bv2 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e6a7f14f_10a28d0c_Treesizes_18_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "isEven_#res", "isEven_#in~n"),
		};
		final String formulaAsString = "(or (and (or (= (_ bv17 32) |isEven_#in~n|) (forall ((|v_isOdd_#in~n_BEFORE_CALL_164| (_ BitVec 32))) (= (_ bv0 32) (bvsrem |v_isOdd_#in~n_BEFORE_CALL_164| (_ bv2 32))))) (= (_ bv0 32) |isEven_#res|)) (bvslt |isEven_#res| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f6fbdd9f_28b4baec_Treesizes_12_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967293 32)) (_ bv0 32))) (= |ULTIMATE.start_main_~n~0#1| (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv3 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_38724446_30478161_Treesizes_12_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_main_~bad_60_arg_0~0#1"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~var_59_arg_0~0#1_16| (_ BitVec 8))) (= ((_ extract 7 0) (bvand (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) (bvand (_ bv254 32) ((_ zero_extend 24) |v_ULTIMATE.start_main_~var_59_arg_0~0#1_16|)))))) |ULTIMATE.start_main_~bad_60_arg_0~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e5cd60fe_531dbff5_Treesizes_16_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id2~0", "~id3~0", "~send3~0", "~p1_new~0"),
		};
		final String formulaAsString = "(and (= ((_ sign_extend 24) ~id3~0) ((_ sign_extend 24) ~send3~0)) (bvsge ((_ sign_extend 24) ~id2~0) (_ bv0 32)) (exists ((~send1~0 (_ BitVec 8))) (= ~p1_new~0 ((_ extract 7 0) ((_ sign_extend 24) ~send1~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_36a278d0_85526c67_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_3 (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_3)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_36a278d0_97eea29d_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_4 (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_4)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_36a278d0_c8bc7ec0_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_5 (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_5)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_36a278d0_fd12b6de_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_6 (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_6)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6e01f968_848e3cfc_Treesizes_10_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= (_ bv0 8) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv6 32) |~#WrapperStruct00~0.base|))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9a8fe880_48a00b6e_Treesizes_13_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "#HeapAllocations", "~head~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (_ bv1 32) (select |#memory_int| (bvadd |#HeapAllocations| (_ bv4294967288 32)))) (= (bvadd (_ bv8 32) ~head~0.base) |#HeapAllocations|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ab826d6_246e14a_Treesizes_21_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_59| (_ BitVec 32))) (or (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_59|))) (= (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_59|) (bvadd |mult_#in~n| |mult_#res|)))) (= |mult_#in~m| (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ab826d6_e11568b_Treesizes_21_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_64| (_ BitVec 32))) (or (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_64|))) (= (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_64|) (bvadd |mult_#in~n| |mult_#res|)))) (= |mult_#in~m| (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2f60708d_455b6cef_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_mulflt_~ea~1#1"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_mulflt_~b#1_67| (_ BitVec 32))) (= (bvadd (_ bv23 32) (bvlshr |v_ULTIMATE.start_mulflt_~b#1_67| (_ bv24 32))) |ULTIMATE.start_mulflt_~ea~1#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7ca5208_c454c148_Treesizes_18_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~lo~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~mid~0#1| (_ BitVec 32))) (or (not (bvsgt |ULTIMATE.start_main_~mid~0#1| (_ bv0 32))) (= (bvmul (_ bv2 32) |ULTIMATE.start_main_~mid~0#1|) (bvadd (_ bv2 32) |ULTIMATE.start_main_~lo~0#1|)) (bvsgt (bvadd (_ bv4294967295 32) |ULTIMATE.start_main_~mid~0#1|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ab826d6_2f17fe4b_Treesizes_21_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_28| (_ BitVec 32))) (or (= (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_28|) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_28|))))) (= |mult_#in~m| (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ab826d6_2f44a146_Treesizes_21_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (= |mult_#in~m| (_ bv1 32)) (forall ((|v_mult_#in~n_BEFORE_CALL_44| (_ BitVec 32))) (or (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_44|))) (= (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_44|) (bvadd |mult_#in~n| |mult_#res|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ab826d6_5b7f6079_Treesizes_21_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_88| (_ BitVec 32))) (or (= (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_88|) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_88|))))) (= |mult_#in~m| (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ab826d6_5fa542ee_Treesizes_21_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (= |mult_#in~m| (_ bv1 32)) (forall ((|v_mult_#in~n_BEFORE_CALL_25| (_ BitVec 32))) (or (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_25|))) (= (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_25|) (bvadd |mult_#in~n| |mult_#res|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ab826d6_93c936d8_Treesizes_21_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_40| (_ BitVec 32))) (or (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_40|))) (= (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_40|) (bvadd |mult_#in~n| |mult_#res|)))) (= |mult_#in~m| (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ab826d6_e9b7b4db_Treesizes_21_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_14| (_ BitVec 32))) (or (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_14|))) (= (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_14|) (bvadd |mult_#in~n| |mult_#res|)))) (= |mult_#in~m| (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ab826d6_ed3982ee_Treesizes_21_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (= |mult_#in~m| (_ bv1 32)) (forall ((|v_mult_#in~n_BEFORE_CALL_82| (_ BitVec 32))) (or (= (bvadd |mult_#in~n| |mult_#res|) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_82|)) (not (= (bvmul |mult_#in~n| (_ bv2 32)) (bvmul (_ bv2 32) |v_mult_#in~n_BEFORE_CALL_82|))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1eabe79b_39d1b9c2_Treesizes_10_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= (_ bv0 8) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv30 32) |~#WrapperStruct00~0.base|))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d60488db_56e46444_Treesizes_16_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_10~0"),
		};
		final String formulaAsString = "(forall ((~var_1_28~0 (_ BitVec 8))) (or (bvsle ((_ sign_extend 24) ~var_1_28~0) ~var_1_10~0) (not (bvsge ((_ sign_extend 24) ~var_1_28~0) (_ bv1 32))) (not (bvsle ((_ sign_extend 24) ~var_1_28~0) (_ bv7 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_32fc07b3_46eaa6f6_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~y~0#1| (_ BitVec 32))) (or (= (_ bv0 32) (bvadd |ULTIMATE.start_main_~y~0#1| |ULTIMATE.start_main_~x~0#1|)) (= (_ bv0 32) (bvadd |ULTIMATE.start_main_~y~0#1| |ULTIMATE.start_main_~x~0#1| (bvneg |ULTIMATE.start_main_~y~0#1|))) (= |ULTIMATE.start_main_~y~0#1| (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_82b1898d_368e9860_Treesizes_14_13() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~b~0#1", "~SIZE~0", "~last~0", "ULTIMATE.start_main_~a~0#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~a~0#1| (_ bv0 32)) (= |ULTIMATE.start_main_~b~0#1| (_ bv0 32)) (= (_ bv20 32) ~SIZE~0) (not (bvsge (_ bv0 32) ~last~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ad7d8414_efcc0668_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_15_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| ~WrapperStruct00_var_1_15_Pointer~0.base)))) (_ bv0 8))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d2433b15_fdb1dc4c_Treesizes_11_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv4 32) |~#WrapperStruct00~0.base|)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d6fe0a77_32b3c5_Treesizes_11_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv28 32) |~#WrapperStruct00~0.base|)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e4923c9c_5c0dafc6_Treesizes_17_13() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_9~0", "~var_1_12~0", "~var_1_11~0", "~var_1_10~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_10~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_9~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_12~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_11~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fb4931a9_36f11fc5_Treesizes_11_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| (bvadd (_ bv5 32) |~#WrapperStruct00~0.base|)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c95b8bbc_416dcc9a_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_property_#t~ite142#1"),
		};
		final String formulaAsString = "(and (bvsle (_ bv128 32) |ULTIMATE.start_property_#t~ite142#1|) (exists ((v_arrayElimCell_71 (_ BitVec 32))) (and (bvsge (bvadd |ULTIMATE.start_property_#t~ite142#1| (bvmul (bvneg v_arrayElimCell_71) (_ bv4294967295 32))) (_ bv4294967295 32)) (bvsge v_arrayElimCell_71 (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c95b8bbc_c49e1b2f_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_property_#t~ite142#1"),
		};
		final String formulaAsString = "(and (bvsle (_ bv128 32) |ULTIMATE.start_property_#t~ite142#1|) (exists ((v_arrayElimCell_44 (_ BitVec 32))) (and (bvsge (bvadd |ULTIMATE.start_property_#t~ite142#1| (bvmul (bvneg v_arrayElimCell_44) (_ bv4294967295 32))) (_ bv4294967295 32)) (bvsge v_arrayElimCell_44 (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c95b8bbc_cdaff590_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_property_#t~ite142#1"),
		};
		final String formulaAsString = "(and (bvsle (_ bv128 32) |ULTIMATE.start_property_#t~ite142#1|) (exists ((v_arrayElimCell_80 (_ BitVec 32))) (and (bvsge v_arrayElimCell_80 (_ bv0 32)) (bvsge (bvadd |ULTIMATE.start_property_#t~ite142#1| (bvmul (bvneg v_arrayElimCell_80) (_ bv4294967295 32))) (_ bv4294967295 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7e8a1bda_4d62877c_Treesizes_25_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(or (exists ((v_arrayElimCell_7 (_ BitVec 32))) (and (bvsle (_ bv0 32) (bvadd v_arrayElimCell_7 (_ bv2147483647 32))) (= ~counter~0 (bvadd (bvneg v_arrayElimCell_7) v_arrayElimCell_7)))) (exists ((v_arrayElimCell_7 (_ BitVec 32))) (and (bvsge v_arrayElimCell_7 (_ bv0 32)) (= ~counter~0 (bvadd (bvneg v_arrayElimCell_7) v_arrayElimCell_7)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7e8a1bda_e5e7a5c8_Treesizes_25_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(or (exists ((v_arrayElimCell_3 (_ BitVec 32))) (and (bvsle (_ bv0 32) (bvadd v_arrayElimCell_3 (_ bv2147483647 32))) (= ~counter~0 (bvadd v_arrayElimCell_3 (bvneg v_arrayElimCell_3))))) (exists ((v_arrayElimCell_3 (_ BitVec 32))) (and (= ~counter~0 (bvadd v_arrayElimCell_3 (bvneg v_arrayElimCell_3))) (bvsge v_arrayElimCell_3 (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b6fb419c_a2d07190_Treesizes_14_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (bvslt (bvadd (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) (_ bv4294967295 32)) (_ bv6 32)) (not (bvslt (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) (_ bv6 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_22624d41_8d886985_Treesizes_15_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_2~0"),
		};
		final String formulaAsString = "(exists ((~var_1_10~0 (_ BitVec 16))) (and (bvsge ((_ zero_extend 16) ~var_1_10~0) (_ bv16383 32)) (not (bvslt ~var_1_2~0 ((_ zero_extend 16) ~var_1_10~0))) (bvsle ((_ zero_extend 16) ~var_1_10~0) (_ bv32767 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f9f7d137_704d5733_Treesizes_17_13() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_15~0", "~var_1_14~0", "~var_1_13~0", "~var_1_12~0"),
		};
		final String formulaAsString = "(and (bvsle ((_ zero_extend 24) ~var_1_14~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_15~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_12~0) (_ bv0 32)) (bvsle ((_ zero_extend 24) ~var_1_13~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c54401fd_4bf123a3_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#A~0#1.base", "ULTIMATE.start_main_~max~0#1"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (bvsgt (select |#memory_int| (bvadd (_ bv4 32) |ULTIMATE.start_main_~#A~0#1.base|)) |ULTIMATE.start_main_~max~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3a1f169f_aa881d86_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_14_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(not (= (_ bv0 8) ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) (select |#memory_int| ~WrapperStruct00_var_1_14_Pointer~0.base))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d6ecbcce_423e34bb_Treesizes_17_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_13~0"),
		};
		final String formulaAsString = "(and (bvsge ~var_1_13~0 (_ bv0 32)) (forall ((~var_1_14~0 (_ BitVec 32))) (= (_ bv0 32) (bvmul ~var_1_13~0 ~var_1_14~0))) (exists ((~var_1_30~0 (_ BitVec 8))) (not (bvsgt ((_ zero_extend 24) ~var_1_30~0) (bvneg ~var_1_13~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_47b87102_4bfa8895_Treesizes_14_13() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~b~0#1", "~SIZE~0", "~last~0", "ULTIMATE.start_main_~a~0#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~a~0#1| (_ bv0 32)) (= |ULTIMATE.start_main_~b~0#1| (_ bv0 32)) (not (bvsge (_ bv0 32) ~last~0)) (= (_ bv200000 32) ~SIZE~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fdfb422e_374fc5f7_Treesizes_9_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_parse_expression_list_~start~0#1", "ULTIMATE.start_parse_expression_list_~i~0#1"),
		};
		final String formulaAsString = "(bvslt (bvadd (_ bv1 32) |ULTIMATE.start_parse_expression_list_~i~0#1| (bvneg (bvadd (_ bv1 32) |ULTIMATE.start_parse_expression_list_~start~0#1|))) (_ bv2 32))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_771e956a_165a641_Treesizes_14_12() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~__CS_ret_PREEMPTED~0", "~__CS_ret~0"),
		};
		final String formulaAsString = "(or (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ~__CS_ret_PREEMPTED~0)))) (not (= (_ bv0 32) ((_ zero_extend 24) ((_ extract 7 0) ((_ zero_extend 24) ~__CS_ret~0))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7e8a1bda_3fa400c9_Treesizes_25_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(or (exists ((v_arrayElimCell_4 (_ BitVec 32))) (and (bvsle v_arrayElimCell_4 (bvadd v_arrayElimCell_4 (_ bv2147483647 32))) (= (bvadd (bvneg v_arrayElimCell_4) v_arrayElimCell_4) ~counter~0))) (exists ((v_arrayElimCell_4 (_ BitVec 32))) (and (bvsge v_arrayElimCell_4 (_ bv0 32)) (= (bvadd (bvneg v_arrayElimCell_4) v_arrayElimCell_4) ~counter~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7e8a1bda_793c7733_Treesizes_25_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(or (exists ((v_arrayElimCell_2 (_ BitVec 32))) (and (= ~counter~0 (bvadd v_arrayElimCell_2 (bvneg v_arrayElimCell_2))) (bvsle v_arrayElimCell_2 (bvadd v_arrayElimCell_2 (_ bv2147483647 32))))) (exists ((v_arrayElimCell_2 (_ BitVec 32))) (and (= ~counter~0 (bvadd v_arrayElimCell_2 (bvneg v_arrayElimCell_2))) (bvsge v_arrayElimCell_2 (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7e8a1bda_b0c51d1e_Treesizes_25_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(or (exists ((v_arrayElimCell_1 (_ BitVec 32))) (and (bvsle v_arrayElimCell_1 (bvadd v_arrayElimCell_1 (_ bv2147483647 32))) (= (bvadd (bvneg v_arrayElimCell_1) v_arrayElimCell_1) ~counter~0))) (exists ((v_arrayElimCell_1 (_ BitVec 32))) (and (bvsge v_arrayElimCell_1 (_ bv0 32)) (= (bvadd (bvneg v_arrayElimCell_1) v_arrayElimCell_1) ~counter~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a76ca31a_fd43d993_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_18| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| (bvadd |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_18| (_ bv4 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fbab7173_e2fdc2c7_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_12| (_ BitVec 32))) (= (_ bv10 32) (select |#memory_int| (bvadd |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_12| (_ bv4 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b0ad32ba_bc2eaea6_Treesizes_16_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_26~0"),
		};
		final String formulaAsString = "(forall ((~var_1_34~0 (_ BitVec 16))) (or (bvsge ((_ zero_extend 16) ~var_1_34~0) ~var_1_26~0) (not (bvsle ((_ zero_extend 16) ~var_1_34~0) (_ bv32767 32))) (not (bvsge ((_ zero_extend 16) ~var_1_34~0) (_ bv16383 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_64e4a6d6_2a1efa1d_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~q~0#1", "ULTIMATE.start_main_~r~0#1", "ULTIMATE.start_main_~A~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~b~0#1| (_ BitVec 32))) (= (bvadd |ULTIMATE.start_main_~r~0#1| (bvmul |ULTIMATE.start_main_~q~0#1| |ULTIMATE.start_main_~b~0#1|)) |ULTIMATE.start_main_~A~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_64e4a6d6_4426aa6d_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~q~0#1", "ULTIMATE.start_main_~r~0#1", "ULTIMATE.start_main_~A~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~d~0#1| (_ BitVec 32))) (= |ULTIMATE.start_main_~A~0#1| (bvadd (bvmul |ULTIMATE.start_main_~q~0#1| |ULTIMATE.start_main_~d~0#1|) |ULTIMATE.start_main_~r~0#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_64e4a6d6_ec7e5c79_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~q~0#1", "ULTIMATE.start_main_~r~0#1", "ULTIMATE.start_main_~A~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~B~0#1| (_ BitVec 32))) (= (bvadd (bvmul |ULTIMATE.start_main_~q~0#1| |ULTIMATE.start_main_~B~0#1|) |ULTIMATE.start_main_~r~0#1|) |ULTIMATE.start_main_~A~0#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_de9f5ea0_56648d5f_Treesizes_13_13() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "thread1Thread1of1ForFork1_~x~0", "~Y~0"),
		};
		final String formulaAsString = "(and (not (bvslt thread1Thread1of1ForFork1_~x~0 (_ bv10000 32))) (bvslt (bvadd thread1Thread1of1ForFork1_~x~0 (_ bv4294967295 32)) (_ bv10000 32)) (= thread1Thread1of1ForFork1_~x~0 ~Y~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fbcd3365_cd6aebf8_Treesizes_17_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_10~0"),
		};
		final String formulaAsString = "(exists ((~var_1_6~0 (_ BitVec 8)) (~var_1_5~0 (_ BitVec 8))) (and (bvsle ((_ zero_extend 24) ~var_1_6~0) (_ bv64 32)) (bvsge ((_ zero_extend 24) ~var_1_5~0) (_ bv64 32)) (bvugt (bvsdiv ((_ zero_extend 24) ~var_1_6~0) ((_ zero_extend 24) ~var_1_5~0)) ~var_1_10~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2a9d1f33_4e5d77f4_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_6| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_6|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2a9d1f33_94813daa_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_7| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_7|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2a9d1f33_9a25b721_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_4| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_4|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2a9d1f33_d12eac03_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_3|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2a9d1f33_fd950981_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_5|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8d1f8dd1_2b52cb36_Treesizes_16_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "thread2Thread1of1ForFork0_~i~1#1", "~counter~0"),
		};
		final String formulaAsString = "(and (or (= (_ bv0 32) (bvmul (_ bv4 32) |thread2Thread1of1ForFork0_~i~1#1|)) (forall ((v_arrayElimCell_10 (_ BitVec 32)) (v_arrayElimCell_9 (_ BitVec 32))) (= (bvneg v_arrayElimCell_9) (bvneg v_arrayElimCell_10)))) (= (_ bv0 32) ~counter~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9e46b0eb_846178ef_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_4| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_4|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9e46b0eb_87ca6ab6_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_3| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_3|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9e46b0eb_a8c590f4_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_7| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_7|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9e46b0eb_aa630453_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_6| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_6|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9e46b0eb_c0ea8e99_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_8| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_8|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9e46b0eb_c825efb9_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_5|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9e46b0eb_fd2e5d9c_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_9| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_9|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6c3b464e_aa09cde_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (= |mult_#in~m| (_ bv3 32)) (forall ((|v_mult_#in~n_BEFORE_CALL_80| (_ BitVec 32))) (or (= (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_80|) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul |mult_#in~n| (_ bv4 32)) (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_80|))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cbbd0017_b2b7319_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_24| (_ BitVec 32))) (or (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_24|) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_24|) (bvmul |mult_#in~n| (_ bv3 32)))))) (= |mult_#in~m| (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_196815b4_3d821832_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_56| (_ BitVec 32))) (or (= (bvmul (_ bv5 32) |v_mult_#in~n_BEFORE_CALL_56|) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul |mult_#in~n| (_ bv5 32)) (bvmul (_ bv5 32) |v_mult_#in~n_BEFORE_CALL_56|))))) (= |mult_#in~m| (_ bv4 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_196815b4_5a50598c_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_79| (_ BitVec 32))) (or (not (= (bvmul |mult_#in~n| (_ bv5 32)) (bvmul (_ bv5 32) |v_mult_#in~n_BEFORE_CALL_79|))) (= (bvmul (_ bv5 32) |v_mult_#in~n_BEFORE_CALL_79|) (bvadd |mult_#in~n| |mult_#res|)))) (= |mult_#in~m| (_ bv4 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_196815b4_93d8bb5c_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_85| (_ BitVec 32))) (or (= (bvadd |mult_#in~n| |mult_#res|) (bvmul (_ bv5 32) |v_mult_#in~n_BEFORE_CALL_85|)) (not (= (bvmul |mult_#in~n| (_ bv5 32)) (bvmul (_ bv5 32) |v_mult_#in~n_BEFORE_CALL_85|))))) (= |mult_#in~m| (_ bv4 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6c3b464e_299bedc1_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (= |mult_#in~m| (_ bv3 32)) (forall ((|v_mult_#in~n_BEFORE_CALL_57| (_ BitVec 32))) (or (= (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_57|) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_57|) (bvmul |mult_#in~n| (_ bv4 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6c3b464e_3984969f_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_62| (_ BitVec 32))) (or (= (bvadd |mult_#in~n| |mult_#res|) (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_62|)) (not (= (bvmul |mult_#in~n| (_ bv4 32)) (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_62|))))) (= |mult_#in~m| (_ bv3 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6c3b464e_7e3537e4_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (= |mult_#in~m| (_ bv3 32)) (forall ((|v_mult_#in~n_BEFORE_CALL_86| (_ BitVec 32))) (or (= (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_86|) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_86|) (bvmul |mult_#in~n| (_ bv4 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6c3b464e_b0c0f5cf_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_38| (_ BitVec 32))) (or (not (= (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_38|) (bvmul |mult_#in~n| (_ bv4 32)))) (= (bvmul (_ bv4 32) |v_mult_#in~n_BEFORE_CALL_38|) (bvadd |mult_#in~n| |mult_#res|)))) (= |mult_#in~m| (_ bv3 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cacd1c9e_c167d0b4_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_78| (_ BitVec 32))) (or (not (= (bvmul (_ bv6 32) |v_mult_#in~n_BEFORE_CALL_78|) (bvmul |mult_#in~n| (_ bv6 32)))) (= (bvmul (_ bv6 32) |v_mult_#in~n_BEFORE_CALL_78|) (bvadd |mult_#in~n| |mult_#res|)))) (= |mult_#in~m| (_ bv5 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cbbd0017_2b7238f0_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (forall ((|v_mult_#in~n_BEFORE_CALL_43| (_ BitVec 32))) (or (not (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_43|) (bvmul |mult_#in~n| (_ bv3 32)))) (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_43|) (bvadd |mult_#in~n| |mult_#res|)))) (= |mult_#in~m| (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cbbd0017_3a1b2b7b_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (= |mult_#in~m| (_ bv2 32)) (forall ((|v_mult_#in~n_BEFORE_CALL_58| (_ BitVec 32))) (or (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_58|) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_58|) (bvmul |mult_#in~n| (_ bv3 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cbbd0017_4116c20c_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (= |mult_#in~m| (_ bv2 32)) (forall ((|v_mult_#in~n_BEFORE_CALL_87| (_ BitVec 32))) (or (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_87|) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_87|) (bvmul |mult_#in~n| (_ bv3 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cbbd0017_7c205b17_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (= |mult_#in~m| (_ bv2 32)) (forall ((|v_mult_#in~n_BEFORE_CALL_63| (_ BitVec 32))) (or (= (bvadd |mult_#in~n| |mult_#res|) (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_63|)) (not (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_63|) (bvmul |mult_#in~n| (_ bv3 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cbbd0017_a9b12eae_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (= |mult_#in~m| (_ bv2 32)) (forall ((|v_mult_#in~n_BEFORE_CALL_39| (_ BitVec 32))) (or (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_39|) (bvadd |mult_#in~n| |mult_#res|)) (not (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_39|) (bvmul |mult_#in~n| (_ bv3 32)))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cbbd0017_ec591ab5_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "mult_#res", "mult_#in~m", "mult_#in~n"),
		};
		final String formulaAsString = "(and (= |mult_#in~m| (_ bv2 32)) (forall ((|v_mult_#in~n_BEFORE_CALL_81| (_ BitVec 32))) (or (not (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_81|) (bvmul |mult_#in~n| (_ bv3 32)))) (= (bvmul (_ bv3 32) |v_mult_#in~n_BEFORE_CALL_81|) (bvadd |mult_#in~n| |mult_#res|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_72ea377_ada70d41_Treesizes_12_12() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967292 32)) (_ bv0 32))) (= |ULTIMATE.start_main_~n~0#1| (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv2 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c5c6ae15_fecb2f9e_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_18| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_18|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_18617fa9_3b0855a4_Treesizes_12_12() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967292 32)) (_ bv0 32))) (= |ULTIMATE.start_main_~n~0#1| (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv3 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_81c13ad1_e81b6b0e_Treesizes_12_12() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~n~0#1| (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv2 32))) (not (bvugt (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv4294967295 32)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b2c2ea18_6a75cd40_Treesizes_12_12() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(and (not (bvugt (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv4294967292 32)) (_ bv0 32))) (= |ULTIMATE.start_main_~n~0#1| (bvadd |ULTIMATE.start_main_~x~0#1| (_ bv1 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ddb3f0a4_2eee8e6c_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_22| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| (bvadd |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_22| (_ bv4 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ddb3f0a4_ae32433a_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_21| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| (bvadd |v_ULTIMATE.start_main_~a~0#1.base_BEFORE_CALL_21| (_ bv4 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1e6105ac_2113c0b5_Treesizes_17_16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_42~0", "~var_1_43~0", "~var_1_44~0", "~var_1_41~0"),
		};
		final String formulaAsString = "(and (bvsge ((_ zero_extend 24) ~var_1_42~0) (_ bv1 32)) (bvsge ((_ zero_extend 24) ~var_1_43~0) (_ bv1 32)) (bvsge ((_ zero_extend 24) ~var_1_41~0) (_ bv1 32)) (bvsle ((_ zero_extend 24) ~var_1_44~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d712457d_32774b62_Treesizes_17_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_8~0", "~var_1_9~0", "~var_1_11~0", "~var_1_10~0"),
		};
		final String formulaAsString = "(and (not (= ~var_1_9~0 (_ bv0 8))) (not (= (_ bv0 8) ~var_1_10~0)) (not (= ~var_1_8~0 (_ bv0 8))) (not (= (_ bv0 8) ~var_1_11~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_dd8c848e_ba58d4b_Treesizes_22_22() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_2~0", "~var_1_9~0", "~var_1_1~0"),
		};
		final String formulaAsString = "(and (or (and (not (bvslt ~var_1_2~0 (_ bv0 32))) (= ~var_1_1~0 ~var_1_2~0)) (= ~var_1_1~0 (bvneg ~var_1_2~0))) (not (bvslt ~var_1_1~0 ~var_1_2~0)) (not (= ~var_1_9~0 (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7b9d1144_59438017_Treesizes_21_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~k~0#1| (_ BitVec 32))) (or (not (bvslt (_ bv5 32) (bvmul |ULTIMATE.start_main_~k~0#1| (_ bv2 32)))) (bvslt (_ bv6 32) (bvmul |ULTIMATE.start_main_~k~0#1| (_ bv2 32))) (bvslt |ULTIMATE.start_main_~k~0#1| (_ bv0 32)) (= |ULTIMATE.start_main_~k~0#1| (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv3 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7ca5208_8a85c41a_Treesizes_20_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~lo~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~mid~0#1| (_ BitVec 32))) (or (bvsgt (bvadd (_ bv4294967293 32) |ULTIMATE.start_main_~mid~0#1|) (_ bv0 32)) (= (bvmul (_ bv2 32) |ULTIMATE.start_main_~mid~0#1|) (bvadd (_ bv6 32) |ULTIMATE.start_main_~lo~0#1|)) (not (bvsgt (bvadd (_ bv4294967294 32) |ULTIMATE.start_main_~mid~0#1|) (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_88cb4bfc_7afae466_Treesizes_16_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_8~0"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~last_1_var_1_10~0"),
		};
		final String formulaAsString = "(and (= ~last_1_var_1_10~0 (_ bv128 32)) (exists ((~var_1_7~0 (_ BitVec 8))) (and (not (bvsgt ((_ sign_extend 24) ~var_1_7~0) ((_ sign_extend 24) ~var_1_8~0))) (bvsge ((_ sign_extend 24) ~var_1_7~0) (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7ca5208_64b32aba_Treesizes_20_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~lo~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~mid~0#1| (_ BitVec 32))) (or (not (bvsgt (bvadd (_ bv4294967259 32) |ULTIMATE.start_main_~mid~0#1|) (_ bv0 32))) (bvsgt (bvadd (_ bv4294967258 32) |ULTIMATE.start_main_~mid~0#1|) (_ bv0 32)) (= (bvadd (_ bv76 32) |ULTIMATE.start_main_~lo~0#1|) (bvmul (_ bv2 32) |ULTIMATE.start_main_~mid~0#1|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7ca5208_cf18b486_Treesizes_20_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~lo~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~mid~0#1| (_ BitVec 32))) (or (bvsgt (bvadd (_ bv4294967288 32) |ULTIMATE.start_main_~mid~0#1|) (_ bv0 32)) (= (bvmul (_ bv2 32) |ULTIMATE.start_main_~mid~0#1|) (bvadd (_ bv16 32) |ULTIMATE.start_main_~lo~0#1|)) (not (bvsgt (bvadd (_ bv4294967289 32) |ULTIMATE.start_main_~mid~0#1|) (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7ca5208_d5abe9a7_Treesizes_20_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~lo~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~mid~0#1| (_ BitVec 32))) (or (bvsgt (bvadd (_ bv4294967278 32) |ULTIMATE.start_main_~mid~0#1|) (_ bv0 32)) (= (bvmul (_ bv2 32) |ULTIMATE.start_main_~mid~0#1|) (bvadd (_ bv36 32) |ULTIMATE.start_main_~lo~0#1|)) (not (bvsgt (bvadd (_ bv4294967279 32) |ULTIMATE.start_main_~mid~0#1|) (_ bv0 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4c025375_a7d0908f_Treesizes_17_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_28~0", "~var_1_27~0", "~var_1_26~0", "~var_1_25~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_26~0)) (not (= (_ bv0 8) ~var_1_25~0)) (not (= (_ bv0 8) ~var_1_27~0)) (not (= (_ bv0 8) ~var_1_28~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7d3c753c_39f5e78e_Treesizes_17_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_58~0", "~var_1_57~0", "~var_1_56~0", "~var_1_55~0"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 8) ~var_1_55~0)) (not (= (_ bv0 8) ~var_1_57~0)) (not (= (_ bv0 8) ~var_1_56~0)) (not (= (_ bv0 8) ~var_1_58~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f544fe92_bc746d96_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~r~0#1", "ULTIMATE.start_main_~p~0#1", "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(and (not (bvule (_ bv1 32) |ULTIMATE.start_main_~n~0#1|)) (= |ULTIMATE.start_main_~r~0#1| |ULTIMATE.start_main_~n~0#1|) (= |ULTIMATE.start_main_~p~0#1| (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c563e47f_5aa931f3_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem85#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_property_#t~ite84#1"),
		};
		final String formulaAsString = "(= ((_ sign_extend 24) |ULTIMATE.start_property_#t~mem85#1|) ((_ sign_extend 24) ((_ extract 7 0) |ULTIMATE.start_property_#t~ite84#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1f914d6e_902445a9_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#pp~0.base", "~#pstate~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_77 (_ BitVec 32))) (= (_ bv1 32) (select (store |#memory_int| (bvadd (_ bv4 32) |~#pp~0.base|) v_ArrVal_77) |~#pstate~0.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a00b9eb4_9b858db4_Treesizes_15_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_2| (_ BitVec 32)) (|v_fibonacci_#in~n_BEFORE_CALL_4| (_ BitVec 32))) (or (not (bvsge |v_fibonacci_#t~ret4_BEFORE_CALL_2| (bvadd |v_fibonacci_#in~n_BEFORE_CALL_4| (_ bv4294967295 32)))) (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_2| |fibonacci_#res|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_4| (_ bv4294967295 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_df7e0d13_46781772_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_43 (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| v_aws_linked_list_front_~list.base_BEFORE_CALL_43))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_df7e0d13_67699fbd_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_41 (_ BitVec 32))) (not (= (select |#memory_$Pointer$.base| v_aws_linked_list_front_~list.base_BEFORE_CALL_41) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_df7e0d13_b17ae0e0_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_42 (_ BitVec 32))) (not (= (select |#memory_$Pointer$.base| v_aws_linked_list_front_~list.base_BEFORE_CALL_42) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_df7e0d13_b33160cd_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_linked_list_front_~list.base_BEFORE_CALL_40 (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| v_aws_linked_list_front_~list.base_BEFORE_CALL_40))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_49eb3196_a2505423_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ensure_byte_buf_has_allocated_buffer_member_#in~buf.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) |ensure_byte_buf_has_allocated_buffer_member_#in~buf.base|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2e5ff8b9_5757a421_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_5| (_ BitVec 32))) (not (= (select |#memory_$Pointer$.base| |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_5|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2e5ff8b9_a4d35267_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_3| (_ BitVec 32))) (not (= (select |#memory_$Pointer$.base| |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_3|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2e5ff8b9_b29af9c5_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_4| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_4|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_edf8e0cc_3a6a59d8_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#pp~0.base", "~#pstate~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_203 (_ BitVec 32))) (= (_ bv1 32) (select (store |#memory_int| |~#pp~0.base| v_ArrVal_203) (bvadd (_ bv4 32) |~#pstate~0.base|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d0941946_99b03f05_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~last_1_WrapperStruct00_var_1_5~0"),
		};
		final String formulaAsString = "(and (= ~last_1_WrapperStruct00_var_1_5~0 ((_ extract 7 0) ((_ sign_extend 24) (_ bv16 8)))) (exists ((|v_ULTIMATE.start_step_~stepLocal_1~0#1_26| (_ BitVec 8))) (bvsle ((_ zero_extend 24) ~last_1_WrapperStruct00_var_1_5~0) ((_ sign_extend 24) |v_ULTIMATE.start_step_~stepLocal_1~0#1_26|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7b9d1144_daef3c8a_Treesizes_22_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~k~0#1| (_ BitVec 32))) (or (not (bvslt (_ bv0 32) (bvmul |ULTIMATE.start_main_~k~0#1| (_ bv2 32)))) (bvslt (_ bv2 32) (bvmul |ULTIMATE.start_main_~k~0#1| (_ bv2 32))) (not (bvsge |ULTIMATE.start_main_~k~0#1| (_ bv4293967296 32))) (= (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv1 32)) |ULTIMATE.start_main_~k~0#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e86b78ef_39472272_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_6| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_6|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e86b78ef_8088213f_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_5|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e86b78ef_e47f4ed6_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_4| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_4|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7b9d1144_b078d983_Treesizes_22_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~k~0#1| (_ BitVec 32))) (or (not (bvslt (_ bv13 32) (bvmul |ULTIMATE.start_main_~k~0#1| (_ bv2 32)))) (bvslt (_ bv14 32) (bvmul |ULTIMATE.start_main_~k~0#1| (_ bv2 32))) (= (bvadd |ULTIMATE.start_main_~n~0#1| (_ bv7 32)) |ULTIMATE.start_main_~k~0#1|) (not (bvsge |ULTIMATE.start_main_~k~0#1| (_ bv4293967296 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3a13ba79_8c30d5f8_Treesizes_24_18() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~q1_back~0", "~q1_front~0", "~M~0", "~N~0"),
		};
		final String formulaAsString = "(and (exists ((~n1~0 (_ BitVec 32))) (and (not (bvslt (_ bv1 32) ~n1~0)) (bvslt ~q1_front~0 ~n1~0))) (bvsge ~M~0 (_ bv0 32)) (bvsge ~q1_front~0 (_ bv0 32)) (= (bvadd (_ bv1 32) ~q1_front~0) ~q1_back~0) (bvsgt ~N~0 ~M~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8235fe0_da92e931_Treesizes_13_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (select (store |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32))) (_ bv0 32)) |ULTIMATE.start_main_~a~0#1.base|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e7becfe0_fee30b24_Treesizes_22_15() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#res", "sum_#in~m"),
		};
		final String formulaAsString = "(and (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (not (bvsle (bvadd (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res|) (_ bv0 32))) (bvsle (bvadd (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967295 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_207f4868_13e6a9b7_Treesizes_13_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (select (store |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32))) (_ bv0 32)) |ULTIMATE.start_main_~x~0#1.base|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c8259b4e_a93232ff_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~var_1_11~0"),
		};
		final String formulaAsString = "(forall ((v_functionized3_~functionized3_localFunctionVar0_25 (_ BitVec 8))) (not (bvsgt (bvnot ((_ zero_extend 24) v_functionized3_~functionized3_localFunctionVar0_25)) ((_ sign_extend 24) ~var_1_11~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_20d72fde_610dabfd_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem19#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_8 (_ BitVec 32))) (and (bvsge ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_8)) (_ bv0 32)) (= |ULTIMATE.start_step_#t~mem19#1| ((_ extract 7 0) v_arrayElimCell_8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4543c04d_3b78ecd3_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem9#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_53 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_53)) (_ bv0 32)) (= ((_ extract 7 0) v_arrayElimCell_53) |ULTIMATE.start_step_#t~mem9#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_97996874_6ff68245_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem9#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_57 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_57)) (_ bv0 32)) (= ((_ extract 7 0) v_arrayElimCell_57) |ULTIMATE.start_step_#t~mem9#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_41c9e7c0_2075c419_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem22#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_17 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_17) |ULTIMATE.start_step_#t~mem22#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_17)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_56b8941_6e21451d_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem22#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_35 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_35)) (_ bv0 32)) (= ((_ extract 7 0) v_arrayElimCell_35) |ULTIMATE.start_step_#t~mem22#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e86b78ef_35da6bfe_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base_BEFORE_CALL_6| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base_BEFORE_CALL_6|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_30fb1d6f_fbb7b7c2_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem19#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_33 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_33) |ULTIMATE.start_step_#t~mem19#1|) (bvsge ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_33)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_600fbd00_ee1fa2a5_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem58#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_33 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_33)) (_ bv0 32)) (= ((_ extract 7 0) v_arrayElimCell_33) |ULTIMATE.start_step_#t~mem58#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b06749e1_e5dbff4f_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem58#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_15 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_15) |ULTIMATE.start_step_#t~mem58#1|) (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_15)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_df7e0d13_8208f5b7_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_17| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_17|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b0a6f0c8_46a0a2e7_Treesizes_18_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem96#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_58 (_ BitVec 32))) (and (bvsle ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_58)) (_ bv1 32)) (bvsge ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_58)) (_ bv1 32)) (= ((_ extract 7 0) ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_58))) |ULTIMATE.start_property_#t~mem96#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e4b41f83_c9e6b359_Treesizes_8_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_array_eq_c_str_harness_~array~0#1.base", "ULTIMATE.start_aws_array_eq_c_str_harness_~str_len~0#1"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) |ULTIMATE.start_aws_array_eq_c_str_harness_~array~0#1.base|) (not (bvugt |ULTIMATE.start_aws_array_eq_c_str_harness_~str_len~0#1| (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_681e1f00_d66ec143_Treesizes_15_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "read_manual_selection_history_#res", "~manual_selection_History_1~0"),
		};
		final String formulaAsString = "(and (or (not (= (_ bv0 32) ((_ sign_extend 24) ~manual_selection_History_1~0))) (= (_ bv0 32) ((_ sign_extend 24) |read_manual_selection_history_#res|))) (= (_ bv0 32) ((_ sign_extend 24) ~manual_selection_History_1~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bccf0a0_4cf15f49_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#in~n_BEFORE_CALL_94| (_ BitVec 32)) (|v_fibonacci_#t~ret4_BEFORE_CALL_53| (_ BitVec 32))) (or (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_53| |fibonacci_#res|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_94| (_ bv4294967295 32))) (not (bvsge (bvadd (_ bv3 32) |v_fibonacci_#t~ret4_BEFORE_CALL_53|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_94| (_ bv4294967295 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_df91795e_79c9196b_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_assert_byte_buf_equivalence_~lhs#1.base", "ULTIMATE.start_assert_byte_buf_equivalence_~rhs#1.base"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 32) |ULTIMATE.start_assert_byte_buf_equivalence_~rhs#1.base|)) (not (= (_ bv0 32) |ULTIMATE.start_assert_byte_buf_equivalence_~lhs#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b101bad_65bd058a_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#in~n_BEFORE_CALL_40| (_ BitVec 32)) (|v_fibonacci_#t~ret4_BEFORE_CALL_19| (_ BitVec 32))) (or (not (bvsge (bvadd (_ bv1 32) |v_fibonacci_#t~ret4_BEFORE_CALL_19|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_40| (_ bv4294967295 32)))) (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_19| |fibonacci_#res|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_40| (_ bv4294967295 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4634a921_31ce0285_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_16| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_16|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_73534e84_3e545fc4_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_38| (_ BitVec 32)) (|v_fibonacci_#in~n_BEFORE_CALL_80| (_ BitVec 32))) (or (not (bvsge (bvadd (_ bv2 32) |v_fibonacci_#t~ret4_BEFORE_CALL_38|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_80| (_ bv4294967295 32)))) (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_38| |fibonacci_#res|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_80| (_ bv4294967295 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d4fc5897_6b389cb3_Treesizes_10_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_hclhlock_init_tnode_~cluster#1"),
		};
		final String formulaAsString = "(and (exists ((|ULTIMATE.start_init_~i~4#1| (_ BitVec 32))) (= |ULTIMATE.start_hclhlock_init_tnode_~cluster#1| (bvurem |ULTIMATE.start_init_~i~4#1| (_ bv2 32)))) (bvult |ULTIMATE.start_hclhlock_init_tnode_~cluster#1| (_ bv2 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_90e9a7d9_f8d995f_Treesizes_22_15() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#t~ret4", "sum_#in~m"),
		};
		final String formulaAsString = "(and (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967295 32)) (_ bv0 32)) (= |sum_#t~ret4| (bvadd |sum_#in~m| |sum_#in~n|)) (not (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32))) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_880bab14_57a99d32_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_13 (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_13)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bccf0a0_9c0aec23_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#in~n_BEFORE_CALL_106| (_ BitVec 32)) (|v_fibonacci_#t~ret4_BEFORE_CALL_70| (_ BitVec 32))) (or (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_70| |fibonacci_#res|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_106| (_ bv4294967295 32))) (not (bvsge (bvadd (_ bv3 32) |v_fibonacci_#t~ret4_BEFORE_CALL_70|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_106| (_ bv4294967295 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_33336f31_39472272_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_6| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_6|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_33336f31_8088213f_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_5|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_33336f31_e47f4ed6_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_4| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_4|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e53d263c_8d519711_Treesizes_12_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_step_#t~mem5#1"),
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4_Pointer~0.base", "~var_1_8_Pointer~0.base"),
		};
		final String formulaAsString = "(and (= (_ bv60 32) ~var_1_4_Pointer~0.base) (exists ((v_arrayElimCell_37 (_ BitVec 32))) (= ((_ extract 7 0) v_arrayElimCell_37) |ULTIMATE.start_step_#t~mem5#1|)) (= (_ bv85 32) ~var_1_8_Pointer~0.base))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_38fc3460_f76bfeba_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#in~n_BEFORE_CALL_162| (_ BitVec 32)) (|v_fibonacci_#t~ret4_BEFORE_CALL_123| (_ BitVec 32))) (or (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_123| |fibonacci_#res|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_162| (_ bv4294967295 32))) (not (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_123| (_ bv5 32)) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_162| (_ bv4294967295 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7e8a1bda_c61e15a6_Treesizes_31_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~counter~0"),
		};
		final String formulaAsString = "(and (forall ((v_arrayElimCell_6 (_ BitVec 32))) (or (= (_ bv0 32) (bvadd v_arrayElimCell_6 (bvneg v_arrayElimCell_6) ~counter~0)) (not (bvsge v_arrayElimCell_6 (_ bv0 32))))) (forall ((v_arrayElimCell_6 (_ BitVec 32))) (or (not (bvsle (bvadd v_arrayElimCell_6 ~counter~0) (bvadd v_arrayElimCell_6 (_ bv2147483647 32)))) (= (_ bv0 32) (bvadd v_arrayElimCell_6 (bvneg v_arrayElimCell_6) ~counter~0)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_80ad67aa_ac0f74f5_Treesizes_13_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|)) (= (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv4 32))) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f524a408_1dd71b7a_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_7| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_7|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f524a408_23d215c2_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_4|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f524a408_58bb9188_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_5|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f524a408_6c0041b8_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_3| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_3|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f524a408_c8b9d6ce_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_6| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_ignore_case_~a#1.base_BEFORE_CALL_6|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fff7a1b1_ed7dc155_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_210| (_ BitVec 32)) (|v_fibonacci_#in~n_BEFORE_CALL_216| (_ BitVec 32))) (or (not (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_210| (_ bv8 32)) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_216| (_ bv4294967295 32)))) (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_210| |fibonacci_#res|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_216| (_ bv4294967295 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_133e2635_e7ac3ac3_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem74#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_25 (_ BitVec 32))) (and (= |ULTIMATE.start_property_#t~mem74#1| ((_ extract 7 0) v_arrayElimCell_25)) (bvsge ((_ sign_extend 24) ((_ extract 7 0) v_arrayElimCell_25)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_62133dd3_7d1cc3bd_Treesizes_25_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
		};
		final String formulaAsString = "(or (and (exists ((v_ArrVal_14 (_ BitVec 32))) (and (bvugt v_ArrVal_14 (_ bv0 32)) (not (= v_ArrVal_14 (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv4 32)))))) (bvugt |ULTIMATE.start_main_~x~0#1.base| (_ bv0 32))) (and (bvugt (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv4294967292 32)) (_ bv0 32)) (bvugt |ULTIMATE.start_main_~x~0#1.base| (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9e519b74_218066f2_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem78#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_32 (_ BitVec 32))) (and (bvslt ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_32)) (_ bv1 32)) (= |ULTIMATE.start_property_#t~mem78#1| ((_ extract 7 0) v_arrayElimCell_32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bc63bd3d_8ae9ad6_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibonacci_#res"),
		};
		final String formulaAsString = "(forall ((|v_fibonacci_#t~ret4_BEFORE_CALL_352| (_ BitVec 32)) (|v_fibonacci_#in~n_BEFORE_CALL_326| (_ BitVec 32))) (or (not (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_352| (_ bv13 32)) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_326| (_ bv4294967295 32)))) (bvsge (bvadd |v_fibonacci_#t~ret4_BEFORE_CALL_352| |fibonacci_#res|) (bvadd |v_fibonacci_#in~n_BEFORE_CALL_326| (_ bv4294967295 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_80130390_566c0c2_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_33| (_ BitVec 32))) (= (select |#memory_$Pointer$.base| (bvadd |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_33| (_ bv4 32))) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_33336f31_ebd3410_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_5|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_80130390_49f60911_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_35| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_35| (_ bv4 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_80130390_b50182cd_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_34| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_34| (_ bv4 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b7c841f6_865a12da_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_14| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_14| (_ bv8 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b7c841f6_b9bd64f3_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_13| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_13| (_ bv8 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b7c841f6_e2fd4909_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_15| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_15| (_ bv8 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ea4a9ef8_230dc96_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem107#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_16 (_ BitVec 32))) (and (= ((_ extract 7 0) v_arrayElimCell_16) |ULTIMATE.start_property_#t~mem107#1|) (bvslt (_ bv1 32) ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_16)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_33336f31_49efffe1_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_4| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_4|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4634a921_62a4976b_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base_BEFORE_CALL_17| (_ BitVec 32))) (not (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_be16_~cur#1.base_BEFORE_CALL_17|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e86b78ef_6cd84e87_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_5|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e86b78ef_a2f5abf0_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_4| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_4|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_82f2159c_3bc6f15e_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#var_1_14~0.base", "~var_1_14_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ~var_1_14_Pointer~0.base |~#var_1_14~0.base|) (bvsge ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| ~var_1_14_Pointer~0.base))) (_ bv1 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_251bc1c8_b211dad_Treesizes_10_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_5_Pointer~0.base", "~#var_1_13~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_169 (_ BitVec 32))) (= ((_ extract 7 0) (select (store |#memory_int| |~#var_1_13~0.base| v_ArrVal_169) ~var_1_5_Pointer~0.base)) (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_586b4f53_75fe1c12_Treesizes_16_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "max_#in~n.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_max_#in~n.base_BEFORE_CALL_10| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_max_#in~n.base_BEFORE_CALL_10| (_ bv4 32))))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |max_#in~n.base| (_ bv4 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_79a284cf_7001e8b9_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_14| (_ BitVec 32))) (not (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_14|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8235fe0_9107db00_Treesizes_16_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32)))) (_ bv0 32))) (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_93277719_7a0936a_Treesizes_9_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_lhs~0#1.base", "ULTIMATE.start_aws_array_eq_harness_~lhs~0#1.base"),
		};
		final String formulaAsString = "(and (not (= (_ bv0 32) |ULTIMATE.start_aws_array_eq_harness_~#old_byte_from_lhs~0#1.base|)) (not (= (_ bv0 32) |ULTIMATE.start_aws_array_eq_harness_~lhs~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a5a855f9_c69f3f8d_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "i2o_dma_alloc_~addr#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_i2o_dma_alloc_~addr#1.base_BEFORE_CALL_1| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_i2o_dma_alloc_~addr#1.base_BEFORE_CALL_1|))) (= (select |#memory_$Pointer$.base| |i2o_dma_alloc_~addr#1.base|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e995185a_c6dce7_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) |v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_5|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_213afdee_acf3f1d9_Treesizes_20_14() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id1~0", "~id2~0", "~send1~0"),
		};
		final String formulaAsString = "(and (= ((_ sign_extend 24) ~id1~0) ((_ sign_extend 24) ~send1~0)) (bvsge ((_ sign_extend 24) ~id2~0) (_ bv0 32)) (exists ((~send2~0 (_ BitVec 8))) (= ((_ sign_extend 24) ~send2~0) ((_ sign_extend 24) ~id2~0))) (bvsge ((_ sign_extend 24) ~id1~0) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_23acc061_7c25b6d2_Treesizes_20_14() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id2~0", "~id3~0", "~send2~0"),
		};
		final String formulaAsString = "(and (= ((_ sign_extend 24) ~send2~0) ((_ sign_extend 24) ~id2~0)) (bvsge ((_ sign_extend 24) ~id3~0) (_ bv0 32)) (bvsge ((_ sign_extend 24) ~id2~0) (_ bv0 32)) (exists ((~send3~0 (_ BitVec 8))) (= ((_ sign_extend 24) ~id3~0) ((_ sign_extend 24) ~send3~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_47b2ca69_f862613c_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_7| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv8 32) |v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_7|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4ebc07be_f8a7d9dd_Treesizes_19_14() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~last_1_var_1_11~0"),
		};
		final String formulaAsString = "(forall ((~var_1_8~0 (_ BitVec 8))) (or (not (bvsge ((_ sign_extend 24) ~var_1_8~0) (_ bv1 32))) (not (bvsle ((_ sign_extend 24) ~var_1_8~0) (_ bv15 32))) (not (= ~last_1_var_1_11~0 (bvashr ~last_1_var_1_11~0 ((_ sign_extend 24) ~var_1_8~0))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_bc509d35_6c91cce4_Treesizes_20_14() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id3~0", "~id4~0", "~send3~0"),
		};
		final String formulaAsString = "(and (bvsge ((_ sign_extend 24) ~id4~0) (_ bv0 32)) (bvsge ((_ sign_extend 24) ~id3~0) (_ bv0 32)) (= ((_ sign_extend 24) ~id3~0) ((_ sign_extend 24) ~send3~0)) (exists ((~send4~0 (_ BitVec 8))) (= ((_ sign_extend 24) ~id4~0) ((_ sign_extend 24) ~send4~0))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f997cc98_c5863196_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_10| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_~cur#1.base_BEFORE_CALL_10|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4c4be70f_9dba0951_Treesizes_12_12() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem78#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_29 (_ BitVec 32))) (and (not (bvslt ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_29)) (_ bv1 32))) (= |ULTIMATE.start_property_#t~mem78#1| ((_ extract 7 0) v_arrayElimCell_29))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5fd2743d_d9dec7f5_Treesizes_12_12() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem78#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_40 (_ BitVec 32))) (and (not (bvslt ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_40)) (_ bv1 32))) (= |ULTIMATE.start_property_#t~mem78#1| ((_ extract 7 0) v_arrayElimCell_40))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9dba0951_650280c1_Treesizes_12_12() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "ULTIMATE.start_property_#t~mem78#1"),
		};
		final String formulaAsString = "(exists ((v_arrayElimCell_33 (_ BitVec 32))) (and (not (bvslt ((_ zero_extend 24) ((_ extract 7 0) v_arrayElimCell_33)) (_ bv1 32))) (= |ULTIMATE.start_property_#t~mem78#1| ((_ extract 7 0) v_arrayElimCell_33))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fcfbdbcb_8ea9320f_Treesizes_25_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~end~0#1.base"),
		};
		final String formulaAsString = "(or (and (bvugt |ULTIMATE.start_main_~end~0#1.base| (_ bv0 32)) (exists ((v_ArrVal_23 (_ BitVec 32))) (and (bvugt v_ArrVal_23 (_ bv0 32)) (not (= v_ArrVal_23 (bvadd (_ bv4 32) |ULTIMATE.start_main_~end~0#1.base|)))))) (and (bvugt |ULTIMATE.start_main_~end~0#1.base| (_ bv0 32)) (bvugt (bvadd |ULTIMATE.start_main_~end~0#1.base| (_ bv4294967292 32)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1a9eb866_121dd6e4_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_6| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_6|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1a9eb866_37d9be52_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_2| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_2|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1a9eb866_421b8f06_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_7| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_7|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1a9eb866_9addb5c9_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_3| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_3|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1a9eb866_a567dc67_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_4| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_4|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1a9eb866_e7397042_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_~cursor#1.base_BEFORE_CALL_5|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c071545d_b23ef35d_Treesizes_8_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_13| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_13| (_ bv4 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_24ce643d_8e80d39f_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_8| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_8|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_311fa247_a749034b_Treesizes_10_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~q~0#1", "ULTIMATE.start_main_~r~0#1", "ULTIMATE.start_main_~b~0#1", "ULTIMATE.start_main_~A~0#1"),
		};
		final String formulaAsString = "(= |ULTIMATE.start_main_~A~0#1| (bvadd (bvneg |ULTIMATE.start_main_~b~0#1|) |ULTIMATE.start_main_~r~0#1| |ULTIMATE.start_main_~b~0#1| (bvmul |ULTIMATE.start_main_~q~0#1| |ULTIMATE.start_main_~b~0#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8d7e1301_10e45643_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_29| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_29|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d3479e50_e2bab8eb_Treesizes_21_21() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~s2s1_new~0", "~s1p_new~0", "~s1s1_new~0", "~nomsg~0"),
		};
		final String formulaAsString = "(and (= ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8))) ~s1p_new~0) (= (_ bv0 8) (bvadd (_ bv1 8) ~nomsg~0)) (= (bvadd (_ bv1 8) ~s2s1_new~0) (_ bv0 8)) (= ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8))) ~s1s1_new~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e4499a0a_2cf2107f_Treesizes_21_21() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~s1s2_new~0", "~s1p_new~0", "~nomsg~0", "~s2s2_new~0"),
		};
		final String formulaAsString = "(and (= ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8))) ~s1p_new~0) (= (_ bv0 8) (bvadd (_ bv1 8) ~s2s2_new~0)) (= (_ bv0 8) (bvadd (_ bv1 8) ~nomsg~0)) (= ~s1s2_new~0 ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e633493f_8242f95b_Treesizes_9_8() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#index~0#1.base", "ULTIMATE.start_main_~#array~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(or (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|)) (= |ULTIMATE.start_main_~#index~0#1.base| |ULTIMATE.start_main_~#array~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_207f4868_c4d8080d_Treesizes_16_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~i~0#1_14| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul (_ bv4 32) |v_ULTIMATE.start_main_~i~0#1_14|))))) (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_main_~x~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_207f4868_fe380819_Treesizes_16_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~i~0#1_15| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul (_ bv4 32) |v_ULTIMATE.start_main_~i~0#1_15|))))) (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_main_~x~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2e4412f1_848f7c23_Treesizes_10_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_9_Pointer~0.base", "~var_1_2_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_88 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_9_Pointer~0.base v_ArrVal_88) ~var_1_2_Pointer~0.base))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2fd81bb0_6926230e_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_23| (_ BitVec 32))) (not (= (select |#memory_$Pointer$.base| (bvadd |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_23| (_ bv12 32))) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2fd81bb0_9268c5bf_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_25| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_25| (_ bv12 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2fd81bb0_d5adc207_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_init_#in~list.base_BEFORE_CALL_24| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd |v_aws_linked_list_init_#in~list.base_BEFORE_CALL_24| (_ bv12 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cf587a88_2e7882d8_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_4| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_next_~node#1.base_BEFORE_CALL_4|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f997cc98_65db1474_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_10| (_ BitVec 32))) (not (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_10|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f997cc98_83264d26_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_11| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_~cur#1.base_BEFORE_CALL_11|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_96a90ae1_8dd79fc9_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_16 (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_16)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_96a90ae1_badb35ec_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_17 (_ BitVec 32))) (not (= (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_17)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_96a90ae1_ebb87f29_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_19 (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_19)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_96a90ae1_ef9221b9_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_18 (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv4 32) v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_18)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_17f5471a_94d9ee70_Treesizes_10_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_11_Pointer~0.base", "~var_1_2_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_98 (_ BitVec 32))) (= ((_ extract 7 0) (select (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_98) ~var_1_2_Pointer~0.base)) (_ bv0 8)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8029afb4_dfeeafc6_Treesizes_15_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (_ bv0 32) (select (store |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32))) (_ bv0 32)) (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv8 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d22d1fe4_69333bfb_Treesizes_11_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "save_byte_from_array_#in~size#1", "save_byte_from_array_#in~array#1.base", "save_byte_from_array_#in~storage#1.base"),
		};
		final String formulaAsString = "(or (= (_ bv0 32) |save_byte_from_array_#in~storage#1.base|) (not (bvugt |save_byte_from_array_#in~size#1| (_ bv0 32))) (= (_ bv0 32) |save_byte_from_array_#in~array#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_dd4108a3_75dfc2ca_Treesizes_15_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (_ bv0 32) (select (store |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32))) (_ bv0 32)) (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv8 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5d0e6377_40f3e753_Treesizes_15_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (_ bv0 32) (select (store |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32))) (_ bv0 32)) (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv32 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5e61730e_d1768de0_Treesizes_27_19() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "fibo1_#in~n", "fibo1_~n"),
		};
		final String formulaAsString = "(or (bvslt fibo1_~n (_ bv1 32)) (= (_ bv1 32) fibo1_~n) (not (bvslt (bvadd (_ bv4294967294 32) fibo1_~n) (_ bv1 32))) (and (bvslt (bvadd |fibo1_#in~n| (_ bv4294967294 32)) (_ bv1 32)) (not (= |fibo1_#in~n| (_ bv1 32))) (not (bvslt |fibo1_#in~n| (_ bv1 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_acae863a_f4b479f6_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#var_1_21~0.base", "~var_1_15_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_187 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| |~#var_1_21~0.base| v_ArrVal_187) ~var_1_15_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c6325404_659edba4_Treesizes_15_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (select (store |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32))) (_ bv0 32)) (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv16 32))) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c918fdd5_7c428a7d_Treesizes_15_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (_ bv0 32) (select (store |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32))) (_ bv0 32)) (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv24 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e7725c66_932e8d57_Treesizes_15_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (_ bv0 32) (select (store |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32))) (_ bv0 32)) (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv40 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f458a1f6_2e579e50_Treesizes_15_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (select (store |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32))) (_ bv0 32)) (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv24 32))) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fe8b1fb1_45ddb5ed_Treesizes_15_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (_ bv0 32) (select (store |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32))) (_ bv0 32)) (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv16 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5cf01b0f_9ab1e090_Treesizes_29_16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~l_4~0", "~f1_6~0"),
		};
		final String formulaAsString = "(and (exists ((v_~f1_6~0_103 (_ BitVec 32))) (bvsge ((_ sign_extend 32) ~f1_6~0) (bvadd ((_ sign_extend 32) (bvadd (bvmul v_~f1_6~0_103 (_ bv4294967295 32)) ~f1_6~0)) (_ bv18446744071562067968 64)))) (or (and (bvsgt ~f1_6~0 (_ bv0 32)) (= (_ bv1 32) ~l_4~0)) (and (= (_ bv0 32) ~l_4~0) (not (bvsgt ~f1_6~0 (_ bv0 32))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5e0b1e52_6a9aec2f_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_property_#t~mem68#1", "ULTIMATE.start_property_#t~ite67#1"),
		};
		final String formulaAsString = "(and (exists ((v_arrayElimCell_23 (_ BitVec 32))) (and (bvule v_arrayElimCell_23 (_ bv2147483647 32)) (bvuge (bvadd |ULTIMATE.start_property_#t~ite67#1| (bvmul (bvneg v_arrayElimCell_23) (_ bv4294967295 32))) (_ bv2147483647 32)))) (= |ULTIMATE.start_property_#t~mem68#1| |ULTIMATE.start_property_#t~ite67#1|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_33336f31_6cd84e87_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_5| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_5|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_33336f31_a2f5abf0_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_4| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_advance_nospec_~cursor#1.base_BEFORE_CALL_4|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c758286d_d3ec4f2d_Treesizes_10_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4_Pointer~0.base", "~var_1_12_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_131 (_ BitVec 32))) (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_12_Pointer~0.base v_ArrVal_131) ~var_1_4_Pointer~0.base))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_2e5ff8b9_1cf58b5d_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_init_harness_~#list~0#1.base_BEFORE_CALL_13| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_init_harness_~#list~0#1.base_BEFORE_CALL_13|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_34428c80_dd5f4d7c_Treesizes_9_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_9| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| (bvadd (_ bv12 32) |v_aws_linked_list_is_valid_#in~list#1.base_BEFORE_CALL_9|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6b48814d_197068dc_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_byte_cursor_compare_lookup_~lhs.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_2 (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| v_aws_byte_cursor_compare_lookup_~lhs.base_BEFORE_CALL_2))) (= (_ bv0 32) (select |#memory_int| aws_byte_cursor_compare_lookup_~lhs.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9bfa77fb_84636060_Treesizes_16_16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_9_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (bvsge (select |#memory_int| (_ bv65 32)) (_ bv1073741822 32)) (= (_ bv61 32) ~var_1_9_Pointer~0.base) (= (select |#memory_int| (_ bv61 32)) (select |#memory_int| (_ bv65 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d89dc97d_89af8ef3_Treesizes_29_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~p2_new~0", "~id3~0", "~nomsg~0"),
		};
		final String formulaAsString = "(and (bvsge ((_ sign_extend 24) ~id3~0) (_ bv0 32)) (= (_ bv0 8) (bvadd (_ bv1 8) ~nomsg~0)) (or (= ~p2_new~0 ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8)))) (exists ((~send2~0 (_ BitVec 8))) (and (= ((_ extract 7 0) ((_ sign_extend 24) ~send2~0)) ~p2_new~0) (not (= ((_ sign_extend 24) ~send2~0) ((_ sign_extend 24) (_ bv255 8))))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_33336f31_29f0dd76_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_18| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_18|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_33336f31_ba6021e8_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_17| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_17|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_33336f31_c7bc4f1c_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_16| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_16|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_79a284cf_d7057542_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_24| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_harness_~#cur~0#1.base_BEFORE_CALL_24|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ac93aad7_82447960_Treesizes_11_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#s~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_dll_remove_last_~snd_to_last~0#1.base| (_ BitVec 32))) (= (_ bv0 32) (select (store |#memory_$Pointer$.base| (bvadd (_ bv4 32) |ULTIMATE.start_dll_remove_last_~snd_to_last~0#1.base|) (_ bv0 32)) |ULTIMATE.start_main_~#s~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ac93aad7_87870ebd_Treesizes_11_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#s~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_sll_remove_last_~snd_to_last~0#1.base| (_ BitVec 32))) (= (_ bv0 32) (select (store |#memory_$Pointer$.base| (bvadd |ULTIMATE.start_sll_remove_last_~snd_to_last~0#1.base| (_ bv4 32)) (_ bv0 32)) |ULTIMATE.start_main_~#s~0#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_729f4317_be6f54f2_Treesizes_23_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#res", "sum_#in~m"),
		};
		final String formulaAsString = "(and (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (not (bvsle (bvadd (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967292 32)) (_ bv0 32))) (bvsle (bvadd (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967291 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_cd56db29_6a25698c_Treesizes_23_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#res", "sum_#in~m"),
		};
		final String formulaAsString = "(and (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (not (bvsle (bvadd (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967294 32)) (_ bv0 32))) (bvsle (bvadd (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967293 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e81cc094_586543d9_Treesizes_23_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#res", "sum_#in~m"),
		};
		final String formulaAsString = "(and (= (bvadd |sum_#in~m| |sum_#in~n|) |sum_#res|) (not (bvsle (bvadd (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967295 32)) (_ bv0 32))) (bvsle (bvadd (bvmul |sum_#in~m| (_ bv4294967295 32)) |sum_#res| (_ bv4294967294 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5cfc6d70_bd0797e1_Treesizes_17_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_step_~stepLocal_7~0#1"),
		};
		final String formulaAsString = "(exists ((~var_1_6~0 (_ BitVec 8)) (~var_1_5~0 (_ BitVec 8))) (and (bvsle ((_ zero_extend 24) ~var_1_6~0) (_ bv64 32)) (bvugt (bvsdiv ((_ zero_extend 24) ~var_1_6~0) ((_ zero_extend 24) ~var_1_5~0)) |ULTIMATE.start_step_~stepLocal_7~0#1|) (bvsge ((_ zero_extend 24) ~var_1_5~0) (_ bv64 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_883085ce_8cdbc037_Treesizes_17_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_property_#t~ite125#1", "ULTIMATE.start_property_#t~mem126#1"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_property_#t~ite125#1| |ULTIMATE.start_property_#t~mem126#1|) (exists ((v_arrayElimCell_74 (_ BitVec 32))) (and (bvuge (bvadd (bvmul (bvneg v_arrayElimCell_74) (_ bv4294967295 32)) |ULTIMATE.start_property_#t~mem126#1|) (_ bv2147483647 32)) (bvule v_arrayElimCell_74 (_ bv2147483647 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ec581d9_b48b21b_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~this_expect~0#1", "ULTIMATE.start_main_~this_buffer_empty~0#1"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) (bvsrem (bvadd |ULTIMATE.start_main_~this_expect~0#1| (_ bv2 32)) (_ bv2 32))) (= (bvneg (bvadd (_ bv1 32) (bvneg (bvadd (bvneg (bvadd (_ bv1 32) (bvneg |ULTIMATE.start_main_~this_buffer_empty~0#1|))) (_ bv1 32))))) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_7cf7ed32_81a51cb6_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_2_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_104 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_104) ~var_1_2_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b49de9e9_d784848a_Treesizes_21_9() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~this_expect~0#1", "ULTIMATE.start_main_~this_buffer_empty~0#1"),
		};
		final String formulaAsString = "(and (= (bvneg (bvadd (_ bv1 32) (bvneg (bvadd (bvneg (bvadd (_ bv1 32) (bvneg |ULTIMATE.start_main_~this_buffer_empty~0#1|))) (_ bv1 32))))) (_ bv0 32)) (= (_ bv0 32) (bvurem (bvadd |ULTIMATE.start_main_~this_expect~0#1| (_ bv2 32)) (_ bv2 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b62bac99_2aebe816_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_27| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_27|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b62bac99_5d1e737b_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_32| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_32|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b62bac99_9292c734_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_30| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_30|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b62bac99_b69d7bc5_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_28| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_28|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b62bac99_bf8e51e4_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_31| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_31|) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b62bac99_c49193ea_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_26| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_26|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b62bac99_da96d275_Treesizes_6_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_29| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_c_str_harness_~#cur~0#1.base_BEFORE_CALL_29|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3b60ac07_daf0912c_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_4_Pointer~0.base", "~var_1_8_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_179 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_8_Pointer~0.base v_ArrVal_179) ~var_1_4_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_815a6293_a035a9f7_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_6_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_161 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_161) ~var_1_6_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_aa0f8d72_fef70419_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_6_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_276 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_276) ~var_1_6_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3d79c5bf_4fd74ba6_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_11_Pointer~0.base", "~var_1_1_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_128 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_1_Pointer~0.base v_ArrVal_128) ~var_1_11_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_711a753b_d39d8ad8_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_11_Pointer~0.base", "~var_1_2_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_117 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_117) ~var_1_2_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8b647ef8_8c0bba8e_Treesizes_13_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~main__urilen~0#1"),
		};
		final String formulaAsString = "(and (bvsgt |ULTIMATE.start_main_~main__urilen~0#1| (_ bv0 32)) (exists ((|ULTIMATE.start_main_~main__cp~0#1| (_ BitVec 32))) (bvslt (bvadd |ULTIMATE.start_main_~main__cp~0#1| (_ bv4294967295 32)) |ULTIMATE.start_main_~main__urilen~0#1|)) (bvsle |ULTIMATE.start_main_~main__urilen~0#1| (_ bv1000000 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_379dc88c_85247a70_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_9_Pointer~0.base", "~var_1_18_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_233 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_9_Pointer~0.base v_ArrVal_233) ~var_1_18_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_47bb9031_77c343ed_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_19_Pointer~0.base", "~var_1_6_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_178 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_6_Pointer~0.base v_ArrVal_178) ~var_1_19_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_4adddc78_48e2703e_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_8_Pointer~0.base", "~var_1_11_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_197 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_11_Pointer~0.base v_ArrVal_197) ~var_1_8_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e2339404_9803d41b_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_5_Pointer~0.base", "~var_1_12_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_164 (_ BitVec 32))) (not (= ((_ extract 7 0) (select (store |#memory_int| ~var_1_12_Pointer~0.base v_ArrVal_164) ~var_1_5_Pointer~0.base)) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e4cdf6d_599373b1_Treesizes_18_16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~s2s1_new~0", "~s1p_new~0", "~s1s1_new~0", "~nomsg~0"),
		};
		final String formulaAsString = "(or (not (= ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~s2s1_new~0))) ((_ sign_extend 24) ~s1s1_new~0))) (= ((_ sign_extend 24) ~s1p_new~0) (_ bv1 32)) (= ((_ sign_extend 24) ~s1p_new~0) ((_ sign_extend 24) ~nomsg~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_ffe5e8f3_45a2a2a2_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_13_Pointer~0.base", "~var_1_2_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_204 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_13_Pointer~0.base v_ArrVal_204) ~var_1_2_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_266a1595_b4972457_Treesizes_21_14() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~id3~0", "~id4~0", "~send3~0"),
		};
		final String formulaAsString = "(or (= ((_ sign_extend 24) ~id3~0) ((_ sign_extend 24) ~id4~0)) (forall ((~send4~0 (_ BitVec 8))) (not (= ((_ sign_extend 24) ~id4~0) ((_ sign_extend 24) ~send4~0)))) (not (= ((_ sign_extend 24) ~id4~0) ((_ sign_extend 24) ((_ extract 7 0) ((_ sign_extend 24) ~send3~0))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_24ce643d_bce4702_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_29| (_ BitVec 32))) (not (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_29|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6f01e00d_112e4d76_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_10_Pointer~0.base", "~var_1_13_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_239 (_ BitVec 32))) (not (= ((_ extract 7 0) (select (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_239) ~var_1_13_Pointer~0.base)) (_ bv0 8))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a76d9bb3_100cca0b_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_end_~list#1.base_BEFORE_CALL_21| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_end_~list#1.base_BEFORE_CALL_21|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a76d9bb3_5a7ec1d2_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_end_~list#1.base_BEFORE_CALL_22| (_ BitVec 32))) (not (= (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_end_~list#1.base_BEFORE_CALL_22|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a76d9bb3_89c4f63f_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_end_~list#1.base_BEFORE_CALL_23| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_end_~list#1.base_BEFORE_CALL_23|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_aada204f_4c5369dc_Treesizes_15_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~b~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= ((_ extract 31 0) (_ bv1 64)) (select |#memory_int| |ULTIMATE.start_main_~b~0#1.base|)) (= (select |#memory_int| (bvadd |ULTIMATE.start_main_~b~0#1.base| (_ bv4 32))) ((_ extract 63 32) (_ bv1 64))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f7866b19_7a6fdd4a_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~var_1_10_Pointer~0.base", "~var_1_13_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((v_ArrVal_145 (_ BitVec 32))) (not (= (_ bv0 8) ((_ extract 7 0) (select (store |#memory_int| ~var_1_10_Pointer~0.base v_ArrVal_145) ~var_1_13_Pointer~0.base)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_24ce643d_7ccc8928_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_28| (_ BitVec 32))) (not (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_28|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_24ce643d_cef853a8_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_30| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_30|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f997cc98_75946e6e_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_38| (_ BitVec 32))) (not (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_38|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f997cc98_ae45ddcf_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_39| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_39|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f997cc98_c14651b3_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_37| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_read_u8_harness_~#cur~0#1.base_BEFORE_CALL_37|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_859edefc_a397a219_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_byte_cursor_is_valid_#in~cursor.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) (select |#memory_int| |aws_byte_cursor_is_valid_#in~cursor.base|)) (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_17| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_17|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d9f67585_7fa6a8d8_Treesizes_18_4() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_property_#t~ite167#1", "ULTIMATE.start_property_#t~ite176#1"),
		};
		final String formulaAsString = "(and (exists ((v_arrayElimCell_31 (_ BitVec 32))) (and (bvsge v_arrayElimCell_31 (_ bv0 32)) (bvsge (bvadd |ULTIMATE.start_property_#t~ite176#1| (bvmul (bvneg v_arrayElimCell_31) (_ bv4294967295 32))) (_ bv4294967295 32)))) (not (bvsle |ULTIMATE.start_property_#t~ite167#1| |ULTIMATE.start_property_#t~ite176#1|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_454d392_1f3abccd_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_22| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_22|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_454d392_9b96ba7e_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_23| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_23|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_454d392_c27648a8_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_21| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rend_~list#1.base_BEFORE_CALL_21|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_91c84b57_ef7fd346_Treesizes_11_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_testOne_~#f2~0#1.base", "ULTIMATE.start_testOne_~#f1~0#1.base", "#StackAllocations"),
		};
		final String formulaAsString = "(and (= |#StackAllocations| (bvadd (_ bv12 32) |ULTIMATE.start_testOne_~#f2~0#1.base|)) (= (bvadd (_ bv12 32) |ULTIMATE.start_testOne_~#f1~0#1.base|) |ULTIMATE.start_testOne_~#f2~0#1.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3cf2ceb0_8e2f4971_Treesizes_15_3() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "func_to_recursive_line_12_to_15_0_#in~i.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int", "old(#memory_int)"),
		};
		final String formulaAsString = "(and (exists ((func_to_recursive_line_12_to_15_0_~n.base (_ BitVec 32))) (not (bvult (select |#memory_int| |func_to_recursive_line_12_to_15_0_#in~i.base|) ((_ zero_extend 24) ((_ extract 7 0) (select |#memory_int| func_to_recursive_line_12_to_15_0_~n.base)))))) (= |old(#memory_int)| |#memory_int|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_10a4bdda_9371d122_Treesizes_23_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#t~ret4", "sum_#in~m"),
		};
		final String formulaAsString = "(and (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967294 32)) (_ bv0 32)) (= |sum_#t~ret4| (bvadd |sum_#in~m| |sum_#in~n|)) (not (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967295 32)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_21d1f138_5081ee0f_Treesizes_23_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#t~ret4", "sum_#in~m"),
		};
		final String formulaAsString = "(and (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967291 32)) (_ bv0 32)) (= |sum_#t~ret4| (bvadd |sum_#in~m| |sum_#in~n|)) (not (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967292 32)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_52374797_10c3288c_Treesizes_23_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#t~ret4", "sum_#in~m"),
		};
		final String formulaAsString = "(and (not (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967293 32)) (_ bv0 32))) (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967292 32)) (_ bv0 32)) (= |sum_#t~ret4| (bvadd |sum_#in~m| |sum_#in~n|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_5e18798d_4ce94ed8_Treesizes_23_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#t~ret4", "sum_#in~m"),
		};
		final String formulaAsString = "(and (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967288 32)) (_ bv0 32)) (= |sum_#t~ret4| (bvadd |sum_#in~m| |sum_#in~n|)) (not (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967289 32)) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8c814f0f_7e21469a_Treesizes_23_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#t~ret4", "sum_#in~m"),
		};
		final String formulaAsString = "(and (not (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967294 32)) (_ bv0 32))) (= |sum_#t~ret4| (bvadd |sum_#in~m| |sum_#in~n|)) (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967293 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_9ca0f779_24d5a409_Treesizes_23_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#t~ret4", "sum_#in~m"),
		};
		final String formulaAsString = "(and (not (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967291 32)) (_ bv0 32))) (= |sum_#t~ret4| (bvadd |sum_#in~m| |sum_#in~n|)) (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967290 32)) (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a3d02346_2b9c6e3e_Treesizes_23_17() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "sum_#in~n", "sum_#t~ret4", "sum_#in~m"),
		};
		final String formulaAsString = "(and (not (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967290 32)) (_ bv0 32))) (bvsle (bvadd |sum_#t~ret4| (bvmul |sum_#in~m| (_ bv4294967295 32)) (_ bv4294967289 32)) (_ bv0 32)) (= |sum_#t~ret4| (bvadd |sum_#in~m| |sum_#in~n|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_dd4108a3_2a3b4022_Treesizes_18_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32)))) (_ bv0 32))) (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv8 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_290d2aa_100f9df3_Treesizes_14_14() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "thread1Thread1of1ForFork1_~x~0", "~Y~0", "thread2Thread1of1ForFork0_~x~1"),
		};
		final String formulaAsString = "(and (not (bvslt thread2Thread1of1ForFork0_~x~1 (_ bv10000 32))) (bvsle thread1Thread1of1ForFork1_~x~0 (_ bv10000 32)) (= thread1Thread1of1ForFork1_~x~0 thread2Thread1of1ForFork0_~x~1) (= ~Y~0 (_ bv0 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_19599978_e9c9492_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "aws_byte_cursor_compare_lexical_~lhs#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_2| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| |v_aws_byte_cursor_compare_lexical_~lhs#1.base_BEFORE_CALL_2|))) (= (_ bv0 32) (select |#memory_int| |aws_byte_cursor_compare_lexical_~lhs#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_c6325404_bdc5a26b_Treesizes_18_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32)))) (_ bv0 32))) (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv16 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f094d8fe_43bc11b2_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_begin_~list#1.base_BEFORE_CALL_21| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_begin_~list#1.base_BEFORE_CALL_21|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f094d8fe_b4940888_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_begin_~list#1.base_BEFORE_CALL_23| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_begin_~list#1.base_BEFORE_CALL_23|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f094d8fe_ce55ddba_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_begin_~list#1.base_BEFORE_CALL_22| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_begin_~list#1.base_BEFORE_CALL_22|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f458a1f6_d0ff9c5d_Treesizes_18_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|ULTIMATE.start_main_~i~0#1| (_ BitVec 32))) (= (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (bvmul |ULTIMATE.start_main_~i~0#1| (_ bv4 32)))) (_ bv0 32))) (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (_ bv24 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d12a3aa3_d53efc4e_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_cursor_eq_~a#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_eq_~a#1.base|)) (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_2|) (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_d12a3aa3_47d17b4_Treesizes_12_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_aws_byte_cursor_eq_~a#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_17| (_ BitVec 32))) (= (select |#memory_int| |v_ULTIMATE.start_aws_byte_cursor_eq_~a#1.base_BEFORE_CALL_17|) (_ bv0 32))) (= (_ bv0 32) (select |#memory_int| |ULTIMATE.start_aws_byte_cursor_eq_~a#1.base|)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_69333bfb_51eba749_Treesizes_13_11() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "save_byte_from_array_#in~size#1", "save_byte_from_array_#in~array#1.base", "save_byte_from_array_#in~storage#1.base"),
		};
		final String formulaAsString = "(or (not (bvugt |save_byte_from_array_#in~storage#1.base| (_ bv0 32))) (not (bvugt |save_byte_from_array_#in~size#1| (_ bv0 32))) (not (bvugt |save_byte_from_array_#in~array#1.base| (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a47a0769_340d51bc_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_22| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_22|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a47a0769_6f88a92e_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_23| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_23|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_a47a0769_cbf56bed_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(exists ((|v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_21| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_aws_linked_list_rbegin_~list#1.base_BEFORE_CALL_21|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_53bb7fec_6a1f3c78_Treesizes_11_10() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~glob2_p_off~0#1"),
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~glob2_pathlim_off~0#1| (_ BitVec 32))) (and (bvsle |ULTIMATE.start_main_~glob2_p_off~0#1| |ULTIMATE.start_main_~glob2_pathlim_off~0#1|) (bvslt |ULTIMATE.start_main_~glob2_pathlim_off~0#1| (_ bv2147483647 32)) (bvsgt |ULTIMATE.start_main_~glob2_pathlim_off~0#1| (_ bv0 32))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_b67732c1_5bedd851_Treesizes_14_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#WrapperStruct00~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|v_ULTIMATE.start_updateVariables_#t~mem38#1_14| (_ BitVec 32))) (or (not (bvsge |v_ULTIMATE.start_updateVariables_#t~mem38#1_14| (_ bv0 32))) (bvsle (bvnot |v_ULTIMATE.start_updateVariables_#t~mem38#1_14|) (select |#memory_int| (bvadd (_ bv4 32) |~#WrapperStruct00~0.base|)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_6ef941a1_d9cd3573_Treesizes_14_6() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~#s~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_$Pointer$.base"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_1| (_ BitVec 32))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |v_ULTIMATE.start_main_~#s~0#1.base_BEFORE_CALL_1|)))) (not (= (_ bv0 32) (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~#s~0#1.base|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8029afb4_8c6efbd4_Treesizes_18_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv8 32)))) (exists ((|v_ULTIMATE.start_main_~i~0#1_42| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul (_ bv4 32) |v_ULTIMATE.start_main_~i~0#1_42|))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8029afb4_c03fc430_Treesizes_18_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv8 32)))) (exists ((|v_ULTIMATE.start_main_~i~0#1_43| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul (_ bv4 32) |v_ULTIMATE.start_main_~i~0#1_43|))))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_1ec4f412_5cc6d4d2_Treesizes_16_16() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~#signed_long_int_Array_0~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (bvsge (select |#memory_int| (_ bv77 32)) (_ bv1073741822 32)) (= (select |#memory_int| (_ bv77 32)) (select |#memory_int| (_ bv73 32))) (= (_ bv73 32) |~#signed_long_int_Array_0~0.base|))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_3a5682a1_23ef35f0_Treesizes_7_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~WrapperStruct00_var_1_8_Pointer~0.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(forall ((|ULTIMATE.start_step_#t~mem19#1| (_ BitVec 8))) (bvslt ((_ sign_extend 24) |ULTIMATE.start_step_#t~mem19#1|) (select |#memory_int| ~WrapperStruct00_var_1_8_Pointer~0.base)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_8235fe0_8814ae03_Treesizes_19_5() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~a~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(exists ((|ULTIMATE.start_main_~n~0#1| (_ BitVec 32))) (and (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~a~0#1.base| (bvmul |ULTIMATE.start_main_~n~0#1| (_ bv4 32)) (_ bv4294967292 32)))) (bvslt (_ bv0 32) |ULTIMATE.start_main_~n~0#1|) (not (bvslt (_ bv1 32) |ULTIMATE.start_main_~n~0#1|))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_90565463_8c30d356_Treesizes_21_21() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort8, "~s2s1_new~0", "~s1p_new~0", "~s1s1_new~0", "~nomsg~0"),
		};
		final String formulaAsString = "(and (= (_ bv0 8) (bvadd (_ bv1 8) ~nomsg~0)) (= ~s2s1_new~0 ((_ extract 7 0) ((_ sign_extend 24) (_ bv255 8)))) (= ((_ extract 7 0) ((_ sign_extend 24) (_ bv1 8))) ~s1p_new~0) (= ((_ extract 7 0) ((_ sign_extend 24) (_ bv1 8))) ~s1s1_new~0))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_e454a93b_e293d5b2_Treesizes_28_22() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "~q2_front~0", "~q2_back~0"),
		};
		final String formulaAsString = "(or (not (bvsge ~q2_front~0 (_ bv0 32))) (forall ((~n2~0 (_ BitVec 32))) (or (not (bvslt ~q2_back~0 ~n2~0)) (bvslt (_ bv2 32) ~n2~0))) (not (bvsgt (bvadd (_ bv1 32) ~q2_back~0) (bvadd (_ bv1 32) ~q2_front~0))) (not (bvsgt (bvadd (_ bv1 32) ~q2_back~0) ~q2_front~0)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_f80bc06a_69508dc1_Treesizes_14_14() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "addflt_~ma~0", "addflt_~mb~0"),
		};
		final String formulaAsString = "(and (exists ((v_addflt_~delta~0_50 (_ BitVec 32)) (v_addflt_~b_68 (_ BitVec 32))) (= addflt_~mb~0 (bvlshr (bvor (_ bv16777216 32) (bvand (_ bv16777215 32) v_addflt_~b_68)) v_addflt_~delta~0_50))) (= addflt_~ma~0 (_ bv33554431 32)))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void SimplificationOpportunity_fe8b1fb1_1d8c589c_Treesizes_18_7() {
		final FunDecl[] funDecls = new FunDecl[] {
			new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_main_~x~0#1.base"),
			new FunDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#memory_int"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~i~0#1_90| (_ BitVec 32))) (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (bvmul (_ bv4 32) |v_ULTIMATE.start_main_~i~0#1_90|))))) (= (_ bv0 32) (select |#memory_int| (bvadd |ULTIMATE.start_main_~x~0#1.base| (_ bv16 32)))))";
		SimplificationTest.runSimplificationTest(funDecls, formulaAsString, null, SIMPLIFICATION_TECHNIQUE, mServices, mLogger, mMgdScript, mCsvWriter);
	}

}
