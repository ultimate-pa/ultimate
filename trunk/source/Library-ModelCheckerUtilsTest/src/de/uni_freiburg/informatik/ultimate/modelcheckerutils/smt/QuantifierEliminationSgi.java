/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
@Category(NoRegression.class)
public class QuantifierEliminationSgi {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY = false;
	private static final boolean CHECK_SIMPLIFICATION_POSSIBILITY = false;
	private static final long TEST_TIMEOUT_MILLISECONDS = 10_00099999;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final LogLevel LOG_LEVEL_SOLVER = LogLevel.INFO;
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:1000 -memory:2024 -smt2 -in";
	// private static final String SOLVER_COMMAND = "smtinterpol -q";

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private static QuantifierEliminationTestCsvWriter mCsvWriter;

	@BeforeClass
	public static void beforeAllTests() {
		mCsvWriter = new QuantifierEliminationTestCsvWriter(QuantifierEliminationSgi.class.getSimpleName());
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

		final Script solverInstance =
				new HistoryRecordingScript(UltimateMocks.createSolver(SOLVER_COMMAND, LOG_LEVEL_SOLVER));
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
	public void simpleSgiExample00() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getBoolSort, "a"),
			};
		final String formulaAsString = "(exists ((x Bool)) (and (= x true) (= a true)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}
	
	@Test
	public void simpleSgiExample() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "y"),
			};
		final String formulaAsString = "(exists ((x Int)) (and (= x y) (= 5 y)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	//(x=0), (A=0) and (B=0), multiple possible maps
	public void simpleSgiExample02() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "A"),
				new FunDecl(SmtSortUtils::getIntSort, "B"),
			};
		final String formulaAsString = "(and (exists ((x Int)) (= x 0)) (= A 0) (= B 0))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	//(x=5) and (5=A), swapped ordering
	public void simpleSgiExample03() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "A"),
			};
		final String formulaAsString = "(and (exists ((x Int)) (= x 5)) (= 5 A))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	//two quantified term variables
	public void simpleSgiExample04() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "A"),
				new FunDecl(SmtSortUtils::getIntSort, "B"),
			};
		final String formulaAsString = "(and (exists ((x Int) (y Int)) (and (<= x 0) (> (+ y x) 0))) (<= A 0) (> (+ B A) 0))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	//noncommutative operator
	public void simpleSgiExample05() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "c"),
				new FunDecl(SmtSortUtils::getIntSort, "d"),
			};
		final String formulaAsString = "(and (exists ((x Int)) (<= x c)) (<= c d))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	//x,y distinct, true
	public void simpleSgiExample06() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "A"),
				new FunDecl(SmtSortUtils::getIntSort, "B"),
			};
		final String formulaAsString = "(and (exists ((X Int) (Y Int)) (and (> X 0) (> Y 0) (not (= X Y)))) (> A 0) (> B 0) (not (= A B)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	//x,y distinct, false
	public void simpleSgiExample07() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "A"),
				new FunDecl(SmtSortUtils::getIntSort, "B"),
				new FunDecl(SmtSortUtils::getIntSort, "M"),
			};
		final String formulaAsString = "(and (exists ((X Int) (Y Int)) (and (> X 0) (> Y 0) (not (= X Y)))) (> A 0) (not (= A B)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	//qsubformula rotation
	public void simpleSgiExample8() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "A"),
				new FunDecl(SmtSortUtils::getIntSort, "B"),
				new FunDecl(SmtSortUtils::getIntSort, "C"),
			};
		final String formulaAsString = "(and (exists ((X Int) (Y Int)) (and (> X 0) (> Y 0) (not (= X Y)))) (> A 0) (> B 0) (> C 0) (= A B) (not (= B C)))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	//parameter rotation
	public void simpleSgiExample9() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "A"),
				new FunDecl(SmtSortUtils::getIntSort, "B"),
				new FunDecl(SmtSortUtils::getIntSort, "C"),
			};
		final String formulaAsString = "(and (exists ((X Int) (Y Int) (Z Int)) (and (= X Y) (= Y Z))) (= A B) (= C A))";
		final String expectedResult = null;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResult, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate01() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"), new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~j~0#1", "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~k~0#1", "ULTIMATE.start_main_~#a~0#1.offset", "ULTIMATE.start_main_~#a~0#1.base"),
		};
		final String formulaAsString = "(and (<= (+ |ULTIMATE.start_main_~k~0#1| 1) 0) (<= 1 |ULTIMATE.start_main_~j~0#1|) (= 2 |ULTIMATE.start_main_~i~0#1|) (<= (+ 3 |ULTIMATE.start_main_~k~0#1|) 0) (<= 0 (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 4)) (= |ULTIMATE.start_main_~#a~0#1.offset| 0) (forall ((|v_ULTIMATE.start_main_~l~0#1_18| Int) (v_ArrVal_80 Int)) (or (< |v_ULTIMATE.start_main_~l~0#1_18| 2) (< v_ArrVal_80 |ULTIMATE.start_main_~j~0#1|) (< |ULTIMATE.start_main_~k~0#1| (+ (select (store (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) (+ |ULTIMATE.start_main_~#a~0#1.offset| (* |ULTIMATE.start_main_~i~0#1| 4) 4) v_ArrVal_80) (+ |ULTIMATE.start_main_~#a~0#1.offset| (* |v_ULTIMATE.start_main_~l~0#1_18| 4))) 2 |ULTIMATE.start_main_~i~0#1|)) (< (+ |ULTIMATE.start_main_~i~0#1| 1) |v_ULTIMATE.start_main_~l~0#1_18|))) (<= 1 (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 8)))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate02() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~j~0#1", "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~k~0#1", "ULTIMATE.start_main_~#b~0#1.offset", "ULTIMATE.start_main_~#a~0#1.offset", "ULTIMATE.start_main_~#b~0#1.base", "ULTIMATE.start_main_~N~0#1", "ULTIMATE.start_main_~#a~0#1.base"),
		};
		final String formulaAsString = "(and (<= 0 |ULTIMATE.start_main_~k~0#1|) (<= |ULTIMATE.start_main_~j~0#1| (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 0)) (= |ULTIMATE.start_main_~#b~0#1.offset| 0) (<= (+ (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 4) 1) (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 0)) (or (<= |ULTIMATE.start_main_~N~0#1| |ULTIMATE.start_main_~i~0#1|) (and (not (= |ULTIMATE.start_main_~i~0#1| 0)) (or (= |ULTIMATE.start_main_~i~0#1| 1) (< |ULTIMATE.start_main_~N~0#1| 2)) (<= |ULTIMATE.start_main_~N~0#1| 2) (= |ULTIMATE.start_main_~k~0#1| 0) (<= (+ |ULTIMATE.start_main_~j~0#1| 1) (+ (select (select |#memory_int| |ULTIMATE.start_main_~#b~0#1.base|) 0) (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) (* |ULTIMATE.start_main_~i~0#1| 4)))))) (exists ((|ULTIMATE.start_main_~#a~0#1.base| Int)) (and (<= (+ (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 4) 1) (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 0)) (<= (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 0) (+ (select (select |#memory_int| |ULTIMATE.start_main_~#b~0#1.base|) 0) (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 4))) (not (= |ULTIMATE.start_main_~#b~0#1.base| |ULTIMATE.start_main_~#a~0#1.base|)))) (<= |ULTIMATE.start_main_~j~0#1| (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 4)) (or (and (= |ULTIMATE.start_main_~k~0#1| 0) (<= (+ (* 2 |ULTIMATE.start_main_~j~0#1|) 1) (+ (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 4) (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 0)))) (< |ULTIMATE.start_main_~N~0#1| 2)) (= |ULTIMATE.start_main_~i~0#1| 1) (<= (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 0) (+ (select (select |#memory_int| |ULTIMATE.start_main_~#b~0#1.base|) 0) |ULTIMATE.start_main_~j~0#1|)) (<= |ULTIMATE.start_main_~N~0#1| 2) (= |ULTIMATE.start_main_~k~0#1| 0) (<= 0 (select (select |#memory_int| |ULTIMATE.start_main_~#b~0#1.base|) 4)) (= |ULTIMATE.start_main_~#a~0#1.offset| 0) (<= (+ (* 2 |ULTIMATE.start_main_~j~0#1|) 1) (+ (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) 0) (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) (* |ULTIMATE.start_main_~i~0#1| 4)))) (not (= |ULTIMATE.start_main_~#b~0#1.base| |ULTIMATE.start_main_~#a~0#1.base|)) (or (and (= |ULTIMATE.start_main_~i~0#1| 1) (= |ULTIMATE.start_main_~k~0#1| 0) (<= 1 (+ (select (select |#memory_int| |ULTIMATE.start_main_~#b~0#1.base|) 0) (select (select |#memory_int| |ULTIMATE.start_main_~#b~0#1.base|) 4)))) (< |ULTIMATE.start_main_~N~0#1| 2)) (<= |ULTIMATE.start_main_~i~0#1| 1))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate03() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#a~0#1.offset", "ULTIMATE.start_main_~#a~0#1.base"),
		};
		final String formulaAsString = "(and (forall ((v_ArrVal_43 Int)) (= (+ (select (store (store (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) (+ |ULTIMATE.start_main_~#a~0#1.offset| (* (mod |ULTIMATE.start_main_~i~0#1| 4294967296) 8)) (+ (select (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) (+ |ULTIMATE.start_main_~#a~0#1.offset| (* (mod |ULTIMATE.start_main_~i~0#1| 4294967296) 8))) (* (- 1) |ULTIMATE.start_main_~i~0#1| |ULTIMATE.start_main_~i~0#1|))) (+ |ULTIMATE.start_main_~#a~0#1.offset| (* (mod (+ |ULTIMATE.start_main_~i~0#1| 1) 4294967296) 8)) v_ArrVal_43) |ULTIMATE.start_main_~#a~0#1.offset|) 1) 0)) (forall ((v_ArrVal_43 Int)) (= (+ (select (store (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) (+ |ULTIMATE.start_main_~#a~0#1.offset| (* (mod (+ |ULTIMATE.start_main_~i~0#1| 1) 4294967296) 8)) v_ArrVal_43) |ULTIMATE.start_main_~#a~0#1.offset|) 1) 0)) (forall ((v_ArrVal_43 Int)) (= (+ (select (store (select |#memory_int| |ULTIMATE.start_main_~#a~0#1.base|) (+ |ULTIMATE.start_main_~#a~0#1.offset| (* (mod |ULTIMATE.start_main_~i~0#1| 4294967296) 8)) v_ArrVal_43) |ULTIMATE.start_main_~#a~0#1.offset|) 1) 0)))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate04() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#x~0#1.offset", "~N~0", "ULTIMATE.start_main_#t~ret11#1", "ULTIMATE.start_main_~ret~0#1", "ULTIMATE.start_main_~#x~0#1.base"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_#t~ret11#1| 0) (= (select (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|) 0) 0) (= (select (select |#memory_int| |ULTIMATE.start_main_~#x~0#1.base|) 4) 0) (exists ((|v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1| Int)) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#x~0#1.base_BEFORE_CALL_1|) 4) 0)) (= |ULTIMATE.start_main_~#x~0#1.offset| 0) (= 2 ~N~0) (= |ULTIMATE.start_main_~ret~0#1| 0))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate05() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~#sum~0#1.base", "ULTIMATE.start_main_~a~0#1.offset", "ULTIMATE.start_main_~a~0#1.base", "~N~0", "ULTIMATE.start_main_~#sum~0#1.offset"),
		};
		final String formulaAsString = "(and (exists ((|ULTIMATE.start_main_~a~0#1.base| Int)) (and (not (= |ULTIMATE.start_main_~#sum~0#1.base| |ULTIMATE.start_main_~a~0#1.base|)) (<= (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 4) 0) (<= (select (select |#memory_int| |ULTIMATE.start_main_~#sum~0#1.base|) |ULTIMATE.start_main_~#sum~0#1.offset|) (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 4)))) (= |ULTIMATE.start_main_~a~0#1.offset| 0) (<= (select (select |#memory_int| |ULTIMATE.start_main_~#sum~0#1.base|) |ULTIMATE.start_main_~#sum~0#1.offset|) 0) (= |ULTIMATE.start_main_~i~0#1| 0) (= (select (select |#memory_int| |ULTIMATE.start_main_~#sum~0#1.base|) |ULTIMATE.start_main_~#sum~0#1.offset|) 0) (not (= |ULTIMATE.start_main_~#sum~0#1.base| |ULTIMATE.start_main_~a~0#1.base|)) (<= 2 ~N~0) (= 0 (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 4)) (<= (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 4) 0))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate06() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~a~0#1.offset", "ULTIMATE.start_main_~#sum~0#1.base", "ULTIMATE.start_main_~a~0#1.base", "~N~0", "ULTIMATE.start_main_~#sum~0#1.offset"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~a~0#1.offset| 0) (< (+ |ULTIMATE.start_main_~i~0#1| 1) (+ (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) |ULTIMATE.start_main_~a~0#1.offset|) (select (select |#memory_int| |ULTIMATE.start_main_~#sum~0#1.base|) |ULTIMATE.start_main_~#sum~0#1.offset|))) (<= 2 (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 0)) (not (= |ULTIMATE.start_main_~#sum~0#1.base| |ULTIMATE.start_main_~a~0#1.base|)) (<= 0 (select (select |#memory_int| |ULTIMATE.start_main_~#sum~0#1.base|) |ULTIMATE.start_main_~#sum~0#1.offset|)) (not (= ~N~0 (select (select |#memory_int| |ULTIMATE.start_main_~#sum~0#1.base|) |ULTIMATE.start_main_~#sum~0#1.offset|))) (<= ~N~0 1) (forall ((v_ArrVal_44 Int)) (or (< (+ |ULTIMATE.start_main_~i~0#1| 1) (+ (select (select (store |#memory_int| |ULTIMATE.start_main_~a~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (+ |ULTIMATE.start_main_~a~0#1.offset| (* |ULTIMATE.start_main_~i~0#1| 4)) v_ArrVal_44)) |ULTIMATE.start_main_~#sum~0#1.base|) |ULTIMATE.start_main_~#sum~0#1.offset|) (select (store (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (+ |ULTIMATE.start_main_~a~0#1.offset| (* |ULTIMATE.start_main_~i~0#1| 4)) v_ArrVal_44) |ULTIMATE.start_main_~a~0#1.offset|))) (< v_ArrVal_44 2))) (exists ((|ULTIMATE.start_main_~a~0#1.base| Int)) (and (<= (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 0) (select (select |#memory_int| |ULTIMATE.start_main_~#sum~0#1.base|) |ULTIMATE.start_main_~#sum~0#1.offset|)) (<= 2 (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 0)) (not (= |ULTIMATE.start_main_~#sum~0#1.base| |ULTIMATE.start_main_~a~0#1.base|)))) (<= |ULTIMATE.start_main_~i~0#1| 1))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate07() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~b~0#1.offset", "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~b~0#1.base"),
		};
		final String formulaAsString = "(and (or (<= (mod |ULTIMATE.start_main_~i~0#1| 4294967296) 2147483647) (forall ((v_ArrVal_160 Int)) (= (select (store (select |#memory_int| |ULTIMATE.start_main_~b~0#1.base|) (+ |ULTIMATE.start_main_~b~0#1.offset| (* (mod |ULTIMATE.start_main_~i~0#1| 4294967296) 8) (- 34359738368)) v_ArrVal_160) |ULTIMATE.start_main_~b~0#1.offset|) 1))) (or (forall ((v_ArrVal_160 Int)) (= (select (store (select |#memory_int| |ULTIMATE.start_main_~b~0#1.base|) (+ |ULTIMATE.start_main_~b~0#1.offset| (* (mod |ULTIMATE.start_main_~i~0#1| 4294967296) 8)) v_ArrVal_160) |ULTIMATE.start_main_~b~0#1.offset|) 1)) (< 2147483647 (mod |ULTIMATE.start_main_~i~0#1| 4294967296))))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate08() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~num~0#1", "ULTIMATE.start_main_~#array~0#1.base", "~ARR_SIZE~0", "ULTIMATE.start_main_~index1~0#1", "ULTIMATE.start_main_~#array~0#1.offset", "ULTIMATE.start_main_~sum~0#1"),
		};
		final String formulaAsString = "(and (<= ~ARR_SIZE~0 1) (= |ULTIMATE.start_main_~sum~0#1| 0) (<= 0 |ULTIMATE.start_main_~index1~0#1|) (< |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) (= (+ |ULTIMATE.start_main_~num~0#1| 1) 0) (exists ((|v_ULTIMATE.start_main_~#array~0#1.offset_BEFORE_CALL_1| Int) (|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1| Int)) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_1|) |v_ULTIMATE.start_main_~#array~0#1.offset_BEFORE_CALL_1|) 0)) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) |ULTIMATE.start_main_~#array~0#1.offset|) 0))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate09() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~num~0#1", "ULTIMATE.start_main_~#array~0#1.base", "~ARR_SIZE~0", "ULTIMATE.start_main_~index1~0#1", "ULTIMATE.start_main_~sum~0#1", "ULTIMATE.start_main_~#array~0#1.offset"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_5| Int)) (and (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_5|) (* ~ARR_SIZE~0 4)) 0) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_5|) (+ (* ~ARR_SIZE~0 4) 4)) 0) (<= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_5|) 0) 0) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_5|) 4) 0))) (<= |ULTIMATE.start_main_~sum~0#1| 0) (< 1 ~ARR_SIZE~0) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 4) 0) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (* ~ARR_SIZE~0 4)) 0) (<= 0 |ULTIMATE.start_main_~index1~0#1|) (< |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) (= |ULTIMATE.start_main_~#array~0#1.offset| 0) (= (+ |ULTIMATE.start_main_~num~0#1| 1) 0) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* ~ARR_SIZE~0 4) 4)) 0) (<= ~ARR_SIZE~0 2) (<= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) 0))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate10() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~#array~0#1.base", "~ARR_SIZE~0", "ULTIMATE.start_main_~sum~0#1", "ULTIMATE.start_main_~#array~0#1.offset"),
		};
		final String formulaAsString = "(and (<= |ULTIMATE.start_main_~sum~0#1| 0) (or (and (or (and (exists ((|ULTIMATE.start_main_~index1~0#1| Int) (|ULTIMATE.start_main_~index2~0#1| Int)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* |ULTIMATE.start_main_~index1~0#1| (* ~ARR_SIZE~0 4)) (* |ULTIMATE.start_main_~index2~0#1| 4))) 1) (< |ULTIMATE.start_main_~index2~0#1| ~ARR_SIZE~0) (<= 0 |ULTIMATE.start_main_~index1~0#1|) (<= 0 |ULTIMATE.start_main_~index2~0#1|) (< |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0))) (<= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) 0)) (exists ((|ULTIMATE.start_main_~index1~0#1| Int)) (and (<= (* |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 0) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* |ULTIMATE.start_main_~index1~0#1| (* ~ARR_SIZE~0 4)) (* (* (- 1) |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 4))) 1) (<= 0 |ULTIMATE.start_main_~index1~0#1|) (< |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0)))) (exists ((|v_ULTIMATE.start_main_~row~0#1_25| Int)) (and (< 1 (+ ~ARR_SIZE~0 (* |v_ULTIMATE.start_main_~row~0#1_25| ~ARR_SIZE~0))) (<= ~ARR_SIZE~0 (+ |v_ULTIMATE.start_main_~row~0#1_25| 1)) (<= (+ ~ARR_SIZE~0 (* |v_ULTIMATE.start_main_~row~0#1_25| ~ARR_SIZE~0)) 2))) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 4) 0)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) 0) (exists ((|ULTIMATE.start_main_~index1~0#1| Int) (|ULTIMATE.start_main_~index2~0#1| Int)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* |ULTIMATE.start_main_~index1~0#1| (* ~ARR_SIZE~0 4)) (* |ULTIMATE.start_main_~index2~0#1| 4))) 1) (< |ULTIMATE.start_main_~index2~0#1| ~ARR_SIZE~0) (<= 0 |ULTIMATE.start_main_~index1~0#1|) (<= 0 |ULTIMATE.start_main_~index2~0#1|) (< |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0))) (exists ((v_prenex_1 Int) (|v_ULTIMATE.start_main_~column~0#1_29| Int)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* (* ~ARR_SIZE~0 4) v_prenex_1) (* |v_ULTIMATE.start_main_~column~0#1_29| 4))) 0) (<= ~ARR_SIZE~0 (+ |v_ULTIMATE.start_main_~column~0#1_29| 1)) (<= v_prenex_1 1) (<= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* (* ~ARR_SIZE~0 4) v_prenex_1) (- 4) (* |v_ULTIMATE.start_main_~column~0#1_29| 4))) 0) (< |v_ULTIMATE.start_main_~column~0#1_29| ~ARR_SIZE~0) (<= ~ARR_SIZE~0 (+ v_prenex_1 1))))) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 4) 0) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) 0) (exists ((|ULTIMATE.start_main_~index1~0#1| Int) (v_prenex_1 Int) (|ULTIMATE.start_main_~index2~0#1| Int)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* |ULTIMATE.start_main_~index1~0#1| (* ~ARR_SIZE~0 4)) (* |ULTIMATE.start_main_~index2~0#1| 4))) 1) (< |ULTIMATE.start_main_~index2~0#1| ~ARR_SIZE~0) (<= 0 |ULTIMATE.start_main_~index1~0#1|) (<= v_prenex_1 1) (<= 0 |ULTIMATE.start_main_~index2~0#1|) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* (* ~ARR_SIZE~0 4) v_prenex_1) (* (* |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 4) 4 (* |ULTIMATE.start_main_~index2~0#1| 4) (* 4 (* (- 1) ~ARR_SIZE~0 v_prenex_1)))) 0) (< (+ |ULTIMATE.start_main_~index2~0#1| (* |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 1) (+ ~ARR_SIZE~0 (* ~ARR_SIZE~0 v_prenex_1))) (<= ~ARR_SIZE~0 (+ v_prenex_1 1))))) (and (or (and (exists ((|v_ULTIMATE.start_main_~row~0#1_25| Int)) (and (< 1 (+ ~ARR_SIZE~0 (* |v_ULTIMATE.start_main_~row~0#1_25| ~ARR_SIZE~0))) (<= ~ARR_SIZE~0 (+ |v_ULTIMATE.start_main_~row~0#1_25| 1)) (<= (+ ~ARR_SIZE~0 (* |v_ULTIMATE.start_main_~row~0#1_25| ~ARR_SIZE~0)) 2))) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 4) 0) (exists ((v_prenex_1 Int) (|v_ULTIMATE.start_main_~column~0#1_29| Int)) (<= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* (* ~ARR_SIZE~0 4) v_prenex_1) (- 4) (* |v_ULTIMATE.start_main_~column~0#1_29| 4))) 0))) (and (exists ((|v_ULTIMATE.start_main_~row~0#1_25| Int)) (and (< 1 (+ ~ARR_SIZE~0 (* |v_ULTIMATE.start_main_~row~0#1_25| ~ARR_SIZE~0))) (<= ~ARR_SIZE~0 (+ |v_ULTIMATE.start_main_~row~0#1_25| 1)) (<= (+ ~ARR_SIZE~0 (* |v_ULTIMATE.start_main_~row~0#1_25| ~ARR_SIZE~0)) 2))) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 4) 0)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 4) 0) (exists ((v_prenex_1 Int)) (and (< 1 (+ ~ARR_SIZE~0 (* ~ARR_SIZE~0 v_prenex_1))) (<= ~ARR_SIZE~0 (+ v_prenex_1 1)) (<= (+ ~ARR_SIZE~0 (* ~ARR_SIZE~0 v_prenex_1)) 2)))) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 4) 0) (exists ((v_prenex_1 Int) (|v_ULTIMATE.start_main_~column~0#1_29| Int)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* (* ~ARR_SIZE~0 4) v_prenex_1) (* |v_ULTIMATE.start_main_~column~0#1_29| 4))) 0) (<= ~ARR_SIZE~0 (+ |v_ULTIMATE.start_main_~column~0#1_29| 1)) (<= v_prenex_1 1) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* (* ~ARR_SIZE~0 4) v_prenex_1) (- 4) (* |v_ULTIMATE.start_main_~column~0#1_29| 4))) 0) (< |v_ULTIMATE.start_main_~column~0#1_29| ~ARR_SIZE~0) (<= ~ARR_SIZE~0 (+ v_prenex_1 1)))))) (exists ((|ULTIMATE.start_main_~index1~0#1| Int)) (and (<= (* |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 0) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* |ULTIMATE.start_main_~index1~0#1| (* ~ARR_SIZE~0 4)) (* (* (- 1) |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 4))) 1) (<= 0 |ULTIMATE.start_main_~index1~0#1|) (< |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0)))) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 4) 0) (or (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) 0) (or (and (exists ((|ULTIMATE.start_main_~index1~0#1| Int) (|ULTIMATE.start_main_~index2~0#1| Int)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* |ULTIMATE.start_main_~index1~0#1| (* ~ARR_SIZE~0 4)) (* |ULTIMATE.start_main_~index2~0#1| 4))) 1) (< |ULTIMATE.start_main_~index2~0#1| ~ARR_SIZE~0) (<= 0 |ULTIMATE.start_main_~index1~0#1|) (<= 0 |ULTIMATE.start_main_~index2~0#1|) (< |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0))) (exists ((v_prenex_1 Int) (|v_ULTIMATE.start_main_~column~0#1_29| Int)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* (* ~ARR_SIZE~0 4) v_prenex_1) (* |v_ULTIMATE.start_main_~column~0#1_29| 4))) 0) (<= ~ARR_SIZE~0 (+ |v_ULTIMATE.start_main_~column~0#1_29| 1)) (<= v_prenex_1 1) (<= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* (* ~ARR_SIZE~0 4) v_prenex_1) (- 4) (* |v_ULTIMATE.start_main_~column~0#1_29| 4))) 0) (< |v_ULTIMATE.start_main_~column~0#1_29| ~ARR_SIZE~0) (<= ~ARR_SIZE~0 (+ v_prenex_1 1))))) (exists ((|ULTIMATE.start_main_~index1~0#1| Int)) (and (<= 0 |ULTIMATE.start_main_~index1~0#1|) (< |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) (exists ((|ULTIMATE.start_main_~index2~0#1| Int)) (and (exists ((v_prenex_1 Int)) (and (<= (+ ~ARR_SIZE~0 (* ~ARR_SIZE~0 v_prenex_1)) (+ |ULTIMATE.start_main_~index2~0#1| (* |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 1)) (<= v_prenex_1 1) (<= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* (* ~ARR_SIZE~0 4) v_prenex_1) (- 4) (* (* |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 4) (* |ULTIMATE.start_main_~index2~0#1| 4) (* 4 (* (- 1) ~ARR_SIZE~0 v_prenex_1)))) 0) (<= ~ARR_SIZE~0 (+ v_prenex_1 1)))) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* |ULTIMATE.start_main_~index1~0#1| (* ~ARR_SIZE~0 4)) (* |ULTIMATE.start_main_~index2~0#1| 4))) 1) (< |ULTIMATE.start_main_~index2~0#1| ~ARR_SIZE~0) (<= 0 |ULTIMATE.start_main_~index2~0#1|))))))) (exists ((|ULTIMATE.start_main_~index1~0#1| Int)) (and (<= (* |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 0) (exists ((v_prenex_1 Int)) (and (<= (+ ~ARR_SIZE~0 (* ~ARR_SIZE~0 v_prenex_1)) 1) (<= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* (* (- 1) |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 4) (* (* ~ARR_SIZE~0 4) v_prenex_1) (- 4) (* (* |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 4) (* 4 (* (- 1) ~ARR_SIZE~0 v_prenex_1)))) 0) (<= ~ARR_SIZE~0 (+ v_prenex_1 1)))) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* |ULTIMATE.start_main_~index1~0#1| (* ~ARR_SIZE~0 4)) (* (* (- 1) |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 4))) 1) (<= 0 |ULTIMATE.start_main_~index1~0#1|) (< |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0))) (and (exists ((v_prenex_1 Int) (|v_ULTIMATE.start_main_~column~0#1_29| Int)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* (* ~ARR_SIZE~0 4) v_prenex_1) (* |v_ULTIMATE.start_main_~column~0#1_29| 4))) 0) (<= ~ARR_SIZE~0 (+ |v_ULTIMATE.start_main_~column~0#1_29| 1)) (<= v_prenex_1 1) (<= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* (* ~ARR_SIZE~0 4) v_prenex_1) (- 4) (* |v_ULTIMATE.start_main_~column~0#1_29| 4))) 0) (< |v_ULTIMATE.start_main_~column~0#1_29| ~ARR_SIZE~0) (<= ~ARR_SIZE~0 (+ v_prenex_1 1)))) (exists ((|ULTIMATE.start_main_~index1~0#1| Int)) (and (<= (* |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 0) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* |ULTIMATE.start_main_~index1~0#1| (* ~ARR_SIZE~0 4)) (* (* (- 1) |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) 4))) 1) (<= 0 |ULTIMATE.start_main_~index1~0#1|) (< |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0))))))) (= |ULTIMATE.start_main_~#array~0#1.offset| 0))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate11() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~num~0#1", "ULTIMATE.start_main_~#array~0#1.base", "~ARR_SIZE~0", "ULTIMATE.start_main_~index1~0#1", "ULTIMATE.start_main_~index2~0#1", "ULTIMATE.start_main_~sum~0#1", "ULTIMATE.start_main_~#array~0#1.offset"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~sum~0#1| 0) (< |ULTIMATE.start_main_~index2~0#1| ~ARR_SIZE~0) (exists ((|v_ULTIMATE.start_main_~column~0#1_30| Int) (|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_2| Int)) (and (<= ~ARR_SIZE~0 (+ |v_ULTIMATE.start_main_~column~0#1_30| 1)) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_2|) 0) 0) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_2|) 4) 0) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_2|) (+ (* ~ARR_SIZE~0 4) (* |v_ULTIMATE.start_main_~column~0#1_30| 4))) 0) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_2|) (+ (* ~ARR_SIZE~0 4) (- 4) (* |v_ULTIMATE.start_main_~column~0#1_30| 4))) 0) (< |v_ULTIMATE.start_main_~column~0#1_30| ~ARR_SIZE~0))) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 4) 0) (<= 0 |ULTIMATE.start_main_~index1~0#1|) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) 0) (<= 0 |ULTIMATE.start_main_~index2~0#1|) (< |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) (= |ULTIMATE.start_main_~#array~0#1.offset| 0) (= (+ |ULTIMATE.start_main_~num~0#1| 1) 0) (exists ((|v_ULTIMATE.start_main_~column~0#1_31| Int)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* ~ARR_SIZE~0 4) (- 4) (* |v_ULTIMATE.start_main_~column~0#1_31| 4))) 0) (< |v_ULTIMATE.start_main_~column~0#1_31| ~ARR_SIZE~0) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* ~ARR_SIZE~0 4) (* |v_ULTIMATE.start_main_~column~0#1_31| 4))) 0) (<= ~ARR_SIZE~0 (+ |v_ULTIMATE.start_main_~column~0#1_31| 1)))) (<= ~ARR_SIZE~0 2))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate12() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~num~0#1", "ULTIMATE.start_main_~#array~0#1.base", "~ARR_SIZE~0", "ULTIMATE.start_main_~index1~0#1", "ULTIMATE.start_main_~index2~0#1", "ULTIMATE.start_main_~sum~0#1", "ULTIMATE.start_main_~#array~0#1.offset"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~sum~0#1| 0) (< |ULTIMATE.start_main_~index2~0#1| ~ARR_SIZE~0) (exists ((|v_ULTIMATE.start_main_~column~0#1_30| Int) (|v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_2| Int)) (and (<= ~ARR_SIZE~0 (+ |v_ULTIMATE.start_main_~column~0#1_30| 1)) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_2|) 0) 0) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_2|) 4) 0) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_2|) (+ (* ~ARR_SIZE~0 4) (* |v_ULTIMATE.start_main_~column~0#1_30| 4))) 0) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array~0#1.base_BEFORE_CALL_2|) (+ (* ~ARR_SIZE~0 4) (- 4) (* |v_ULTIMATE.start_main_~column~0#1_30| 4))) 0) (< |v_ULTIMATE.start_main_~column~0#1_30| ~ARR_SIZE~0))) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 4) 0) (<= 0 |ULTIMATE.start_main_~index1~0#1|) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) 0) 0) (<= 0 |ULTIMATE.start_main_~index2~0#1|) (< |ULTIMATE.start_main_~index1~0#1| ~ARR_SIZE~0) (= |ULTIMATE.start_main_~#array~0#1.offset| 0) (= (+ |ULTIMATE.start_main_~num~0#1| 1) 0) (exists ((|v_ULTIMATE.start_main_~column~0#1_31| Int)) (and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* ~ARR_SIZE~0 4) (- 4) (* |v_ULTIMATE.start_main_~column~0#1_31| 4))) 0) (< |v_ULTIMATE.start_main_~column~0#1_31| ~ARR_SIZE~0) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array~0#1.base|) (+ (* ~ARR_SIZE~0 4) (* |v_ULTIMATE.start_main_~column~0#1_31| 4))) 0) (<= ~ARR_SIZE~0 (+ |v_ULTIMATE.start_main_~column~0#1_31| 1)))) (<= ~ARR_SIZE~0 2))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate13() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~num~0#1", "~ARR_SIZE~0", "ULTIMATE.start_main_~#array1~0#1.offset", "ULTIMATE.start_main_~#array2~0#1.offset", "ULTIMATE.start_main_~#array2~0#1.base", "ULTIMATE.start_main_~index~0#1", "ULTIMATE.start_main_~sum~0#1", "ULTIMATE.start_main_~#array1~0#1.base"),
		};
		final String formulaAsString = "(and (= (select (select |#memory_int| |ULTIMATE.start_main_~#array2~0#1.base|) 0) 0) (= |ULTIMATE.start_main_~#array2~0#1.offset| 0) (<= ~ARR_SIZE~0 1) (= |ULTIMATE.start_main_~sum~0#1| 0) (<= 0 |ULTIMATE.start_main_~index~0#1|) (exists ((|v_ULTIMATE.start_main_~#array1~0#1.base_BEFORE_CALL_1| Int) (|v_ULTIMATE.start_main_~#array2~0#1.base_BEFORE_CALL_1| Int)) (and (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array1~0#1.base_BEFORE_CALL_1|) 0) 0) (= (select (select |#memory_int| |v_ULTIMATE.start_main_~#array2~0#1.base_BEFORE_CALL_1|) 0) 0) (not (= |v_ULTIMATE.start_main_~#array2~0#1.base_BEFORE_CALL_1| |v_ULTIMATE.start_main_~#array1~0#1.base_BEFORE_CALL_1|)))) (< |ULTIMATE.start_main_~index~0#1| ~ARR_SIZE~0) (= (+ |ULTIMATE.start_main_~num~0#1| 1) 0) (= |ULTIMATE.start_main_~#array1~0#1.offset| 0) (not (= |ULTIMATE.start_main_~#array2~0#1.base| |ULTIMATE.start_main_~#array1~0#1.base|)) (= (select (select |#memory_int| |ULTIMATE.start_main_~#array1~0#1.base|) 0) 0))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate13renamed() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "M"),
				new FunDecl(SmtSortUtils::getIntSort, "A", "S", "B", "C", "D", "E", "F", "G"),
		};
		final String formulaAsString = "(and (= (select (select |M| |D|) 0) 0) (= |C| 0) (<= S 1) (= |F| 0) (<= 0 |E|) (exists ((|X| Int) (|Y| Int)) (and (= (select (select |M| |X|) 0) 0) (= (select (select |M| |Y|) 0) 0) (not (= |Y| |X|)))) (< |E| S) (= (+ |A| 1) 0) (= |B| 0) (not (= |D| |G|)) (= (select (select |M| |G|) 0) 0))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	//false
	public void sgiCandidate13renamedmodified() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "M"),
				new FunDecl(SmtSortUtils::getIntSort, "A", "S", "B", "C", "D", "E", "F", "G"),
		};
		final String formulaAsString = "(and (= |C| 0) (<= S 1) (= |F| 0) (<= 0 |E|) (exists ((|X| Int) (|Y| Int)) (and (= (select (select |M| |X|) 0) 0) (= (select (select |M| |Y|) 0) 0) (not (= |Y| |X|)))) (< |E| S) (= (+ |A| 1) 0) (= |B| 0) (not (= |D| |G|)) (= (select (select |M| |G|) 0) 0))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, false, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate14() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~i~0#1", "ULTIMATE.start_main_~a~0#1.offset", "ULTIMATE.start_main_~a~0#1.base", "~SIZE~0"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~a~0#1.offset| 0) (or (<= ~SIZE~0 |ULTIMATE.start_main_~i~0#1|) (= (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (+ |ULTIMATE.start_main_~a~0#1.offset| (* |ULTIMATE.start_main_~i~0#1| 4))) 0)) (forall ((|v_ULTIMATE.start_main_~i~0#1_73| Int)) (or (< |ULTIMATE.start_main_~i~0#1| (+ |v_ULTIMATE.start_main_~i~0#1_73| 1)) (< |v_ULTIMATE.start_main_~i~0#1_73| 3) (= (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (+ |ULTIMATE.start_main_~a~0#1.offset| (* |v_ULTIMATE.start_main_~i~0#1_73| 4))) 0))) (forall ((|v_ULTIMATE.start_main_~i~0#1_73| Int)) (or (< |v_ULTIMATE.start_main_~i~0#1_73| (+ |ULTIMATE.start_main_~i~0#1| 1)) (<= ~SIZE~0 |v_ULTIMATE.start_main_~i~0#1_73|) (= (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (+ |ULTIMATE.start_main_~a~0#1.offset| (* |v_ULTIMATE.start_main_~i~0#1_73| 4))) 0))) (= (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 12) 0) (forall ((|v_ULTIMATE.start_main_~i~0#1_73| Int)) (or (< |v_ULTIMATE.start_main_~i~0#1_73| 3) (<= ~SIZE~0 |v_ULTIMATE.start_main_~i~0#1_73|) (= (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) (+ |ULTIMATE.start_main_~a~0#1.offset| (* |v_ULTIMATE.start_main_~i~0#1_73| 4))) 0))))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate15() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~sn~0#1"),
		};
		final String formulaAsString = "(or (forall ((|ULTIMATE.start_main_~n~0#1| Int)) (= (mod |ULTIMATE.start_main_~sn~0#1| 4294967296) (mod (div (mod (+ |ULTIMATE.start_main_~n~0#1| (* |ULTIMATE.start_main_~n~0#1| |ULTIMATE.start_main_~n~0#1|)) 4294967296) 2) 4294967296))) (= (mod |ULTIMATE.start_main_~sn~0#1| 4294967296) 0))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate16() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#valid"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~list~0#1.offset", "ULTIMATE.start_main_~end~0#1.base", "ULTIMATE.start_main_~list~0#1.base"),
		};
		final String formulaAsString = "(and (forall ((v_arrayElimCell_11 Int)) (or (forall ((v_ArrVal_605 (Array Int Int)) (v_ArrVal_606 (Array Int Int))) (or (= (select (select (store (store |#memory_int| |ULTIMATE.start_main_~end~0#1.base| v_ArrVal_606) v_arrayElimCell_11 v_ArrVal_605) |ULTIMATE.start_main_~list~0#1.base|) (+ |ULTIMATE.start_main_~list~0#1.offset| 8)) 1) (forall ((v_ArrVal_607 (Array Int Int)) (v_arrayElimCell_12 Int)) (= (select (select (store (store (store |#memory_int| |ULTIMATE.start_main_~end~0#1.base| v_ArrVal_606) v_arrayElimCell_11 v_ArrVal_607) v_arrayElimCell_12 v_ArrVal_605) |ULTIMATE.start_main_~list~0#1.base|) (+ |ULTIMATE.start_main_~list~0#1.offset| 8)) 1)))) (not (= (select |#valid| v_arrayElimCell_11) 0)))) (or (not (= (select |#valid| |ULTIMATE.start_main_~end~0#1.base|) 0)) (forall ((v_ArrVal_605 (Array Int Int)) (v_ArrVal_607 (Array Int Int)) (v_arrayElimCell_12 Int)) (= (select (select (store (store |#memory_int| |ULTIMATE.start_main_~end~0#1.base| v_ArrVal_607) v_arrayElimCell_12 v_ArrVal_605) |ULTIMATE.start_main_~list~0#1.base|) (+ |ULTIMATE.start_main_~list~0#1.offset| 8)) 1))) (forall ((v_arrayElimCell_11 Int)) (or (= |ULTIMATE.start_main_~end~0#1.base| v_arrayElimCell_11) (forall ((v_ArrVal_605 (Array Int Int)) (v_ArrVal_606 (Array Int Int))) (= (select (select (store (store |#memory_int| |ULTIMATE.start_main_~end~0#1.base| v_ArrVal_606) v_arrayElimCell_11 v_ArrVal_605) |ULTIMATE.start_main_~list~0#1.base|) (+ |ULTIMATE.start_main_~list~0#1.offset| 8)) 1)) (not (= (select |#valid| v_arrayElimCell_11) 0)))))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate17() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#valid"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~list~0#1.offset", "ULTIMATE.start_main_~end~0#1.base", "ULTIMATE.start_main_~list~0#1.base"),
		};
		final String formulaAsString = "(and (forall ((v_arrayElimCell_11 Int)) (or (forall ((v_ArrVal_605 (Array Int Int)) (v_ArrVal_606 (Array Int Int))) (or (= (select (select (store (store |#memory_int| |ULTIMATE.start_main_~end~0#1.base| v_ArrVal_606) v_arrayElimCell_11 v_ArrVal_605) |ULTIMATE.start_main_~list~0#1.base|) (+ |ULTIMATE.start_main_~list~0#1.offset| 8)) 1) (forall ((v_ArrVal_607 (Array Int Int)) (v_arrayElimCell_12 Int)) (= (select (select (store (store (store |#memory_int| |ULTIMATE.start_main_~end~0#1.base| v_ArrVal_606) v_arrayElimCell_11 v_ArrVal_607) v_arrayElimCell_12 v_ArrVal_605) |ULTIMATE.start_main_~list~0#1.base|) (+ |ULTIMATE.start_main_~list~0#1.offset| 8)) 1)))) (not (= (select |#valid| v_arrayElimCell_11) 0)))) (or (not (= (select |#valid| |ULTIMATE.start_main_~end~0#1.base|) 0)) (forall ((v_ArrVal_605 (Array Int Int)) (v_ArrVal_607 (Array Int Int)) (v_arrayElimCell_12 Int)) (= (select (select (store (store |#memory_int| |ULTIMATE.start_main_~end~0#1.base| v_ArrVal_607) v_arrayElimCell_12 v_ArrVal_605) |ULTIMATE.start_main_~list~0#1.base|) (+ |ULTIMATE.start_main_~list~0#1.offset| 8)) 1))) (forall ((v_arrayElimCell_11 Int)) (or (= |ULTIMATE.start_main_~end~0#1.base| v_arrayElimCell_11) (forall ((v_ArrVal_605 (Array Int Int)) (v_ArrVal_606 (Array Int Int))) (= (select (select (store (store |#memory_int| |ULTIMATE.start_main_~end~0#1.base| v_ArrVal_606) v_arrayElimCell_11 v_ArrVal_605) |ULTIMATE.start_main_~list~0#1.base|) (+ |ULTIMATE.start_main_~list~0#1.offset| 8)) 1)) (not (= (select |#valid| v_arrayElimCell_11) 0)))))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate18() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#valid"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int", "#memory_$Pointer$.base", "#memory_$Pointer$.offset"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~l~0#1.offset", "ULTIMATE.start_main_~l~0#1.base"),
		};
		final String formulaAsString = "(and (= (select (select |#memory_$Pointer$.offset| |ULTIMATE.start_main_~l~0#1.base|) 0) 0) (= |ULTIMATE.start_main_~l~0#1.offset| 0) (= (select |#valid| |ULTIMATE.start_main_~l~0#1.base|) 1) (not (= (select (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~l~0#1.base|) 0) |ULTIMATE.start_main_~l~0#1.base|)) (or (not (= (select (select |#memory_int| |ULTIMATE.start_main_~l~0#1.base|) 8) 2)) (not (= (select (select |#memory_int| |ULTIMATE.start_main_~l~0#1.base|) 4) 0))) (forall ((v_ArrVal_272 (Array Int Int)) (|v_ULTIMATE.start_main_~l~0#1.base_13| Int)) (or (not (= (select (select (store |#memory_int| |v_ULTIMATE.start_main_~l~0#1.base_13| v_ArrVal_272) |ULTIMATE.start_main_~l~0#1.base|) (+ |ULTIMATE.start_main_~l~0#1.offset| 8)) 2)) (not (= (select |#valid| |v_ULTIMATE.start_main_~l~0#1.base_13|) 0)) (not (= (select (select (store |#memory_int| |v_ULTIMATE.start_main_~l~0#1.base_13| v_ArrVal_272) |ULTIMATE.start_main_~l~0#1.base|) (+ |ULTIMATE.start_main_~l~0#1.offset| 4)) 0)))) (or (not (= (select (select |#memory_int| (select (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~l~0#1.base|) 0)) 4) 0)) (not (= (select (select |#memory_int| (select (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~l~0#1.base|) 0)) 8) 2))))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate19() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#valid"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int", "#memory_$Pointer$.base", "#memory_$Pointer$.offset"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_check_queue_~n~0#1.offset", "ULTIMATE.start_check_queue_~n~0#1.base", "#StackHeapBarrier", "ULTIMATE.start_main_~#queue~0#1.base", "ULTIMATE.start_main_~#queue~0#1.offset"),
		};
		final String formulaAsString = "(and (= (select |#valid| |ULTIMATE.start_main_~#queue~0#1.base|) 1) (< 0 (+ |ULTIMATE.start_check_queue_~n~0#1.offset| 1)) (= (select (select |#memory_$Pointer$.offset| |ULTIMATE.start_main_~#queue~0#1.base|) |ULTIMATE.start_main_~#queue~0#1.offset|) 0) (= (select |#valid| (select (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~#queue~0#1.base|) 0)) 1) (not (= |ULTIMATE.start_main_~#queue~0#1.base| |ULTIMATE.start_check_queue_~n~0#1.base|)) (= |ULTIMATE.start_check_queue_~n~0#1.offset| 0) (= |ULTIMATE.start_main_~#queue~0#1.offset| 0) (= (select |#valid| |ULTIMATE.start_check_queue_~n~0#1.base|) 1) (< |#StackHeapBarrier| |ULTIMATE.start_main_~#queue~0#1.base|) (<= 1 (select (select |#memory_int| (select (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~#queue~0#1.base|) 0)) 4)) (forall ((v_ArrVal_515 (Array Int Int)) (v_ArrVal_514 (Array Int Int)) (v_ArrVal_517 (Array Int Int)) (v_ArrVal_516 (Array Int Int)) (v_ArrVal_524 Int) (v_ArrVal_522 (Array Int Int)) (v_ArrVal_521 (Array Int Int))) (or (< 0 (select (select (store (store |#memory_int| v_ArrVal_524 v_ArrVal_517) |ULTIMATE.start_main_~#queue~0#1.base| v_ArrVal_514) (select (select (store (store |#memory_$Pointer$.base| v_ArrVal_524 (store v_ArrVal_516 8 (select (select (store |#memory_$Pointer$.base| v_ArrVal_524 v_ArrVal_516) |ULTIMATE.start_main_~#queue~0#1.base|) |ULTIMATE.start_main_~#queue~0#1.offset|))) |ULTIMATE.start_main_~#queue~0#1.base| (store (select (store |#memory_$Pointer$.base| v_ArrVal_524 v_ArrVal_521) |ULTIMATE.start_main_~#queue~0#1.base|) |ULTIMATE.start_main_~#queue~0#1.offset| v_ArrVal_524)) v_ArrVal_524) 8)) (+ (select (select (store (store |#memory_$Pointer$.offset| v_ArrVal_524 (store v_ArrVal_515 8 (select (select (store |#memory_$Pointer$.offset| v_ArrVal_524 v_ArrVal_515) |ULTIMATE.start_main_~#queue~0#1.base|) |ULTIMATE.start_main_~#queue~0#1.offset|))) |ULTIMATE.start_main_~#queue~0#1.base| (store (select (store |#memory_$Pointer$.offset| v_ArrVal_524 v_ArrVal_522) |ULTIMATE.start_main_~#queue~0#1.base|) |ULTIMATE.start_main_~#queue~0#1.offset| 0)) v_ArrVal_524) 8) 4))) (<= |#StackHeapBarrier| v_ArrVal_524) (not (= (select |#valid| v_ArrVal_524) 0)))) (= (select (select |#memory_$Pointer$.offset| |ULTIMATE.start_main_~#queue~0#1.base|) 0) 0) (<= (+ |#StackHeapBarrier| 1) |ULTIMATE.start_main_~#queue~0#1.base|) (<= |ULTIMATE.start_check_queue_~n~0#1.offset| 0) (<= 1 (select (select |#memory_int| |ULTIMATE.start_check_queue_~n~0#1.base|) 4)) (= (select (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~#queue~0#1.base|) 0) |ULTIMATE.start_check_queue_~n~0#1.base|) (= (select (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~#queue~0#1.base|) |ULTIMATE.start_main_~#queue~0#1.offset|) |ULTIMATE.start_check_queue_~n~0#1.base|) (not (= |ULTIMATE.start_main_~#queue~0#1.base| (select (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~#queue~0#1.base|) 0))))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate20() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_$Pointer$.base", "#memory_$Pointer$.offset"),
				new FunDecl(SmtSortUtils::getIntSort, "~#mutexes~0.base", "ULTIMATE.start_foo_~m2~0#1.base", "~#mutexes~0.offset"),
		};
		final String formulaAsString = "(and (exists ((v_DerPreprocessor_1 (Array Int Int))) (and (= 3 (select v_DerPreprocessor_1 0)) (not (= |ULTIMATE.start_foo_~m2~0#1.base| (select (select (store |#memory_$Pointer$.base| 3 v_DerPreprocessor_1) (select (select |#memory_$Pointer$.base| 3) 0)) 0))) (= (select (select (store |#memory_$Pointer$.base| 3 v_DerPreprocessor_1) (select (select |#memory_$Pointer$.base| 3) 0)) 8) 3) (not (= 3 (select (select (store |#memory_$Pointer$.base| 3 v_DerPreprocessor_1) (select (select |#memory_$Pointer$.base| 3) 0)) 0))) (not (= (select (select |#memory_$Pointer$.base| 3) 0) (select (select (store |#memory_$Pointer$.base| 3 v_DerPreprocessor_1) (select (select |#memory_$Pointer$.base| 3) 0)) 0))) (= 3 (select (select (store |#memory_$Pointer$.base| 3 v_DerPreprocessor_1) (select (select |#memory_$Pointer$.base| 3) 0)) 4)))) (not (= (select (select |#memory_$Pointer$.base| 3) 0) |ULTIMATE.start_foo_~m2~0#1.base|)) (= |~#mutexes~0.base| 3) (not (= (select (select |#memory_$Pointer$.base| 3) 0) 3)) (= |~#mutexes~0.offset| 0) (exists ((__ldv_list_add_~next.offset Int)) (and (= (select (select |#memory_$Pointer$.base| 3) 0) (select (select |#memory_$Pointer$.base| 3) (+ __ldv_list_add_~next.offset 4))) (= (select (select |#memory_$Pointer$.offset| 3) (+ __ldv_list_add_~next.offset 4)) 4))) (not (= 3 |ULTIMATE.start_foo_~m2~0#1.base|)) (= (select (select |#memory_$Pointer$.offset| 3) 0) 4))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate21() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_$Pointer$.base"),
				new FunDecl(SmtSortUtils::getIntSort, "__ldv_list_add_#in~new.base", "~#drvlist~0.offset", "__ldv_list_add_#in~prev.base", "~#drvlist~0.base", "__ldv_list_add_#in~prev.offset"),
		};
		final String formulaAsString = "(and (= |~#drvlist~0.offset| 0) (or (and (or (and (exists ((v_DerPreprocessor_7 (Array Int Int)) (v_DerPreprocessor_8 (Array Int Int))) (and (= (select (store (store (store (store (store |#memory_$Pointer$.base| |__ldv_list_add_#in~prev.base| v_DerPreprocessor_7) |__ldv_list_add_#in~new.base| v_DerPreprocessor_8) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_7) |__ldv_list_add_#in~new.base| v_DerPreprocessor_8) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_7) |__ldv_list_add_#in~new.base|) v_DerPreprocessor_8) (= |__ldv_list_add_#in~new.base| (select v_DerPreprocessor_7 |__ldv_list_add_#in~prev.offset|)))) (exists ((v_DerPreprocessor_3 (Array Int Int)) (v_DerPreprocessor_2 (Array Int Int))) (and (= v_DerPreprocessor_2 (select (store (store (store (store (store |#memory_$Pointer$.base| |__ldv_list_add_#in~prev.base| v_DerPreprocessor_3) |__ldv_list_add_#in~new.base| v_DerPreprocessor_2) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_3) |__ldv_list_add_#in~new.base| v_DerPreprocessor_2) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_3) |__ldv_list_add_#in~new.base|)) (= |__ldv_list_add_#in~new.base| (select v_DerPreprocessor_3 |__ldv_list_add_#in~prev.offset|))))) (exists ((v_DerPreprocessor_1 (Array Int Int)) (v_DerPreprocessor_3 (Array Int Int)) (v_DerPreprocessor_2 (Array Int Int)) (v_DerPreprocessor_10 (Array Int Int)) (__ldv_list_add_~next.base Int) (v_DerPreprocessor_9 (Array Int Int)) (v_DerPreprocessor_11 (Array Int Int))) (and (= (select (store (store (store (store (store (store |#memory_$Pointer$.base| __ldv_list_add_~next.base v_DerPreprocessor_1) |__ldv_list_add_#in~new.base| v_DerPreprocessor_2) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_3) __ldv_list_add_~next.base v_DerPreprocessor_1) |__ldv_list_add_#in~new.base| v_DerPreprocessor_2) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_3) __ldv_list_add_~next.base) (select (store (store (store (store (store (store |#memory_$Pointer$.base| __ldv_list_add_~next.base v_DerPreprocessor_9) |__ldv_list_add_#in~new.base| v_DerPreprocessor_10) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_11) __ldv_list_add_~next.base v_DerPreprocessor_9) |__ldv_list_add_#in~new.base| v_DerPreprocessor_10) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_11) __ldv_list_add_~next.base)) (= |__ldv_list_add_#in~new.base| (select v_DerPreprocessor_3 |__ldv_list_add_#in~prev.offset|)) (= (select (store (store (store (store (store (store |#memory_$Pointer$.base| __ldv_list_add_~next.base v_DerPreprocessor_1) |__ldv_list_add_#in~new.base| v_DerPreprocessor_2) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_3) __ldv_list_add_~next.base v_DerPreprocessor_1) |__ldv_list_add_#in~new.base| v_DerPreprocessor_2) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_3) |__ldv_list_add_#in~new.base|) v_DerPreprocessor_2) (= v_DerPreprocessor_9 (select (store (store (store (store (store (store |#memory_$Pointer$.base| __ldv_list_add_~next.base v_DerPreprocessor_9) |__ldv_list_add_#in~new.base| v_DerPreprocessor_10) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_11) __ldv_list_add_~next.base v_DerPreprocessor_9) |__ldv_list_add_#in~new.base| v_DerPreprocessor_10) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_11) __ldv_list_add_~next.base)) (= v_DerPreprocessor_1 (select (store (store (store (store (store (store |#memory_$Pointer$.base| __ldv_list_add_~next.base v_DerPreprocessor_1) |__ldv_list_add_#in~new.base| v_DerPreprocessor_2) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_3) __ldv_list_add_~next.base v_DerPreprocessor_1) |__ldv_list_add_#in~new.base| v_DerPreprocessor_2) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_3) __ldv_list_add_~next.base)) (= (select (store (store (store (store (store (store |#memory_$Pointer$.base| __ldv_list_add_~next.base v_DerPreprocessor_9) |__ldv_list_add_#in~new.base| v_DerPreprocessor_10) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_11) __ldv_list_add_~next.base v_DerPreprocessor_9) |__ldv_list_add_#in~new.base| v_DerPreprocessor_10) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_11) |__ldv_list_add_#in~new.base|) v_DerPreprocessor_10) (= (select (store (store (store (store (store (store |#memory_$Pointer$.base| __ldv_list_add_~next.base v_DerPreprocessor_9) |__ldv_list_add_#in~new.base| v_DerPreprocessor_10) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_11) __ldv_list_add_~next.base v_DerPreprocessor_9) |__ldv_list_add_#in~new.base| v_DerPreprocessor_10) |__ldv_list_add_#in~prev.base| v_DerPreprocessor_11) __ldv_list_add_~next.base) (select |#memory_$Pointer$.base| __ldv_list_add_~next.base)) (= |__ldv_list_add_#in~new.base| (select v_DerPreprocessor_11 |__ldv_list_add_#in~prev.offset|))))) (= (select (select |#memory_$Pointer$.base| |__ldv_list_add_#in~prev.base|) |__ldv_list_add_#in~prev.offset|) |__ldv_list_add_#in~new.base|)) (and (not (= |__ldv_list_add_#in~new.base| |__ldv_list_add_#in~prev.base|)) (= (select (select |#memory_$Pointer$.base| |__ldv_list_add_#in~prev.base|) |__ldv_list_add_#in~prev.offset|) |__ldv_list_add_#in~new.base|))) (= 4 |~#drvlist~0.base|))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate22() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_$Pointer$.base", "#memory_$Pointer$.offset"),
				new FunDecl(SmtSortUtils::getIntSort, "~#mutexes~0.base", "ULTIMATE.start_foo_~m2~0#1.base", "~#mutexes~0.offset"),
		};
		final String formulaAsString = "(and (not (= (select (select |#memory_$Pointer$.base| 3) 0) |ULTIMATE.start_foo_~m2~0#1.base|)) (= |~#mutexes~0.base| 3) (not (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| 3) 0)) 0) (select (select |#memory_$Pointer$.base| 3) 0))) (not (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| 3) 0)) 0) |ULTIMATE.start_foo_~m2~0#1.base|)) (= |~#mutexes~0.offset| 0) (not (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| 3) 0)) 0) 3)) (not (= 3 |ULTIMATE.start_foo_~m2~0#1.base|)) (= (select (select |#memory_$Pointer$.offset| 3) 0) 4) (exists ((__ldv_list_add_~next.offset Int)) (= (select (select |#memory_$Pointer$.base| 3) 0) (select (select |#memory_$Pointer$.base| 3) (+ __ldv_list_add_~next.offset 4)))) (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| 3) 0)) 4) 3) (= (select (select |#memory_$Pointer$.base| (select (select |#memory_$Pointer$.base| 3) 0)) 8) 3))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate23() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#valid"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~t~0#1.base", "ULTIMATE.start_main_~a~0#1.offset", "ULTIMATE.start_main_~a~0#1.base", "ULTIMATE.start_main_~p~0#1.base", "ULTIMATE.start_main_~p~0#1.offset"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~a~0#1.offset| 0) (not (= |ULTIMATE.start_main_~a~0#1.base| |ULTIMATE.start_main_~p~0#1.base|)) (forall ((v_ArrVal_624 (Array Int Int)) (|v_ULTIMATE.start_main_~p~0#1.base_55| Int)) (or (= (select (select (store (store |#memory_int| |ULTIMATE.start_main_~p~0#1.base| v_ArrVal_624) |v_ULTIMATE.start_main_~p~0#1.base_55| (store (select (store |#memory_int| |ULTIMATE.start_main_~p~0#1.base| v_ArrVal_624) |v_ULTIMATE.start_main_~p~0#1.base_55|) 0 3)) |ULTIMATE.start_main_~a~0#1.base|) |ULTIMATE.start_main_~a~0#1.offset|) 1) (= 3 (select (select (store (store |#memory_int| |ULTIMATE.start_main_~p~0#1.base| v_ArrVal_624) |v_ULTIMATE.start_main_~p~0#1.base_55| (store (select (store |#memory_int| |ULTIMATE.start_main_~p~0#1.base| v_ArrVal_624) |v_ULTIMATE.start_main_~p~0#1.base_55|) 0 3)) |ULTIMATE.start_main_~a~0#1.base|) |ULTIMATE.start_main_~a~0#1.offset|)))) (= (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 0) 1) (forall ((v_ArrVal_620 Int) (v_ArrVal_624 (Array Int Int)) (|v_ULTIMATE.start_main_~p~0#1.base_55| Int)) (or (= (select (select (store (store (store |#memory_int| |ULTIMATE.start_main_~p~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~p~0#1.base|) (+ |ULTIMATE.start_main_~p~0#1.offset| 4) v_ArrVal_620)) |ULTIMATE.start_main_~t~0#1.base| v_ArrVal_624) |v_ULTIMATE.start_main_~p~0#1.base_55| (store (select (store (store |#memory_int| |ULTIMATE.start_main_~p~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~p~0#1.base|) (+ |ULTIMATE.start_main_~p~0#1.offset| 4) v_ArrVal_620)) |ULTIMATE.start_main_~t~0#1.base| v_ArrVal_624) |v_ULTIMATE.start_main_~p~0#1.base_55|) 0 3)) |ULTIMATE.start_main_~a~0#1.base|) |ULTIMATE.start_main_~a~0#1.offset|) 3) (= (select (select (store (store (store |#memory_int| |ULTIMATE.start_main_~p~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~p~0#1.base|) (+ |ULTIMATE.start_main_~p~0#1.offset| 4) v_ArrVal_620)) |ULTIMATE.start_main_~t~0#1.base| v_ArrVal_624) |v_ULTIMATE.start_main_~p~0#1.base_55| (store (select (store (store |#memory_int| |ULTIMATE.start_main_~p~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~p~0#1.base|) (+ |ULTIMATE.start_main_~p~0#1.offset| 4) v_ArrVal_620)) |ULTIMATE.start_main_~t~0#1.base| v_ArrVal_624) |v_ULTIMATE.start_main_~p~0#1.base_55|) 0 3)) |ULTIMATE.start_main_~a~0#1.base|) |ULTIMATE.start_main_~a~0#1.offset|) 1))) (= (select |#valid| |ULTIMATE.start_main_~a~0#1.base|) 1))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate24() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#valid"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_$Pointer$.base", "#memory_$Pointer$.offset"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~a~0#1.offset", "ULTIMATE.start_main_~a~0#1.base", "ULTIMATE.start_main_~p~0#1.base", "ULTIMATE.start_main_~p~0#1.offset"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~a~0#1.offset| 0) (= (select (select |#memory_$Pointer$.base| |ULTIMATE.start_main_~a~0#1.base|) 4) |ULTIMATE.start_main_~p~0#1.base|) (not (= |ULTIMATE.start_main_~a~0#1.base| |ULTIMATE.start_main_~p~0#1.base|)) (forall ((v_ArrVal_183 (Array Int Int))) (= (select (select (store |#memory_$Pointer$.base| |ULTIMATE.start_main_~p~0#1.base| v_ArrVal_183) |ULTIMATE.start_main_~a~0#1.base|) (+ |ULTIMATE.start_main_~a~0#1.offset| 4)) |ULTIMATE.start_main_~p~0#1.base|)) (= (select (select |#memory_$Pointer$.offset| |ULTIMATE.start_main_~a~0#1.base|) 4) 0) (forall ((v_ArrVal_178 (Array Int Int))) (= |ULTIMATE.start_main_~p~0#1.offset| (select (select (store |#memory_$Pointer$.offset| |ULTIMATE.start_main_~p~0#1.base| v_ArrVal_178) |ULTIMATE.start_main_~a~0#1.base|) (+ |ULTIMATE.start_main_~a~0#1.offset| 4)))) (= |ULTIMATE.start_main_~p~0#1.offset| 0) (= (select |#valid| |ULTIMATE.start_main_~a~0#1.base|) 1))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate25() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~data_init~0#1", "ULTIMATE.start_sll_circular_create_~last~0#1.offset", "ULTIMATE.start_sll_circular_create_~head~0#1.offset", "ULTIMATE.start_sll_circular_create_~head~0#1.base"),
		};
		final String formulaAsString = "(and (forall ((|ULTIMATE.start_sll_circular_create_~new_head~0#1.base| Int)) (or (forall ((|ULTIMATE.start_sll_circular_create_~last~0#1.base| Int)) (or (forall ((v_ArrVal_387 Int) (v_ArrVal_383 (Array Int Int)) (v_ArrVal_396 (Array Int Int))) (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 4)))) (= |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| |ULTIMATE.start_sll_circular_create_~last~0#1.base|))) (= |ULTIMATE.start_sll_circular_create_~head~0#1.base| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base|))) (forall ((|ULTIMATE.start_sll_circular_create_~new_head~0#1.base| Int)) (or (forall ((|ULTIMATE.start_sll_circular_create_~last~0#1.base| Int)) (or (= |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| |ULTIMATE.start_sll_circular_create_~last~0#1.base|) (forall ((v_ArrVal_387 Int) (v_ArrVal_383 (Array Int Int)) (v_ArrVal_396 (Array Int Int))) (or (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) 4)) (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 4))))))) (= |ULTIMATE.start_sll_circular_create_~head~0#1.base| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base|))) (forall ((|ULTIMATE.start_sll_circular_create_~new_head~0#1.base| Int)) (or (= |ULTIMATE.start_sll_circular_create_~head~0#1.base| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base|) (forall ((|ULTIMATE.start_sll_circular_create_~last~0#1.base| Int)) (or (= |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| |ULTIMATE.start_sll_circular_create_~last~0#1.base|) (forall ((v_ArrVal_387 Int) (v_ArrVal_383 (Array Int Int)) (v_ArrVal_396 (Array Int Int))) (or (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) 4)) (= (select v_ArrVal_396 4) |ULTIMATE.start_main_~data_init~0#1|) (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 4))))))))) (or (= |ULTIMATE.start_sll_circular_create_~last~0#1.offset| 0) (and (forall ((|ULTIMATE.start_sll_circular_create_~new_head~0#1.base| Int)) (or (forall ((v_ArrVal_387 Int) (v_ArrVal_383 (Array Int Int)) (|ULTIMATE.start_sll_circular_create_~last~0#1.base| Int) (v_ArrVal_396 (Array Int Int))) (or (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) 4)) (= (select v_ArrVal_396 4) |ULTIMATE.start_main_~data_init~0#1|) (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 4))))) (= |ULTIMATE.start_sll_circular_create_~head~0#1.base| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base|))) (forall ((|ULTIMATE.start_sll_circular_create_~new_head~0#1.base| Int)) (or (forall ((v_ArrVal_387 Int) (v_ArrVal_383 (Array Int Int)) (|ULTIMATE.start_sll_circular_create_~last~0#1.base| Int) (v_ArrVal_396 (Array Int Int))) (or (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) 4)) (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 4))))) (= |ULTIMATE.start_sll_circular_create_~head~0#1.base| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base|))) (forall ((|ULTIMATE.start_sll_circular_create_~new_head~0#1.base| Int)) (or (= |ULTIMATE.start_sll_circular_create_~head~0#1.base| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base|) (forall ((v_ArrVal_387 Int) (v_ArrVal_383 (Array Int Int)) (|ULTIMATE.start_sll_circular_create_~last~0#1.base| Int) (v_ArrVal_396 (Array Int Int))) (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 4)))))))) (or (= |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 0) (and (forall ((|ULTIMATE.start_sll_circular_create_~last~0#1.base| Int) (|ULTIMATE.start_sll_circular_create_~new_head~0#1.base| Int)) (or (= |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| |ULTIMATE.start_sll_circular_create_~last~0#1.base|) (forall ((v_ArrVal_387 Int) (v_ArrVal_383 (Array Int Int)) (v_ArrVal_396 (Array Int Int))) (or (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) 4)) (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 4))))))) (forall ((|ULTIMATE.start_sll_circular_create_~last~0#1.base| Int) (|ULTIMATE.start_sll_circular_create_~new_head~0#1.base| Int)) (or (= |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| |ULTIMATE.start_sll_circular_create_~last~0#1.base|) (forall ((v_ArrVal_387 Int) (v_ArrVal_383 (Array Int Int)) (v_ArrVal_396 (Array Int Int))) (or (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) 4)) (= (select v_ArrVal_396 4) |ULTIMATE.start_main_~data_init~0#1|) (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 4))))))) (forall ((|ULTIMATE.start_sll_circular_create_~last~0#1.base| Int) (|ULTIMATE.start_sll_circular_create_~new_head~0#1.base| Int)) (or (forall ((v_ArrVal_387 Int) (v_ArrVal_383 (Array Int Int)) (v_ArrVal_396 (Array Int Int))) (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 4)))) (= |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| |ULTIMATE.start_sll_circular_create_~last~0#1.base|))) (or (= |ULTIMATE.start_sll_circular_create_~last~0#1.offset| 0) (and (forall ((v_ArrVal_387 Int) (v_ArrVal_383 (Array Int Int)) (|ULTIMATE.start_sll_circular_create_~last~0#1.base| Int) (v_ArrVal_396 (Array Int Int)) (|ULTIMATE.start_sll_circular_create_~new_head~0#1.base| Int)) (or (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) 4)) (= (select v_ArrVal_396 4) |ULTIMATE.start_main_~data_init~0#1|) (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 4))))) (forall ((v_ArrVal_387 Int) (v_ArrVal_383 (Array Int Int)) (|ULTIMATE.start_sll_circular_create_~last~0#1.base| Int) (v_ArrVal_396 (Array Int Int)) (|ULTIMATE.start_sll_circular_create_~new_head~0#1.base| Int)) (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 4)))) (forall ((v_ArrVal_387 Int) (v_ArrVal_383 (Array Int Int)) (|ULTIMATE.start_sll_circular_create_~last~0#1.base| Int) (v_ArrVal_396 (Array Int Int)) (|ULTIMATE.start_sll_circular_create_~new_head~0#1.base| Int)) (or (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) 4)) (= |ULTIMATE.start_main_~data_init~0#1| (select (select (store (store (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base| (store (select (store |#memory_int| |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_383) |ULTIMATE.start_sll_circular_create_~last~0#1.base|) |ULTIMATE.start_sll_circular_create_~last~0#1.offset| v_ArrVal_387)) |ULTIMATE.start_sll_circular_create_~new_head~0#1.base| v_ArrVal_396) |ULTIMATE.start_sll_circular_create_~head~0#1.base|) (+ |ULTIMATE.start_sll_circular_create_~head~0#1.offset| 4))))))))))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate26() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#valid"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~a~0#1.offset", "ULTIMATE.start_main_~t~0#1.base", "ULTIMATE.start_main_~a~0#1.base", "ULTIMATE.start_main_~flag~0#1", "ULTIMATE.start_main_~p~0#1.base", "ULTIMATE.start_main_~p~0#1.offset"),
		};
		final String formulaAsString = "(and (= |ULTIMATE.start_main_~a~0#1.offset| 0) (not (= |ULTIMATE.start_main_~a~0#1.base| |ULTIMATE.start_main_~p~0#1.base|)) (= (select (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|) 0) 1) (forall ((|v_ULTIMATE.start_main_~t~0#1.base_7| Int)) (or (forall ((v_ArrVal_76 (Array Int Int)) (v_ArrVal_75 Int)) (= (select (select (store (store |#memory_int| |ULTIMATE.start_main_~p~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~p~0#1.base|) (+ |ULTIMATE.start_main_~p~0#1.offset| 4) v_ArrVal_75)) |v_ULTIMATE.start_main_~t~0#1.base_7| v_ArrVal_76) |ULTIMATE.start_main_~a~0#1.base|) |ULTIMATE.start_main_~a~0#1.offset|) 1)) (not (= (select |#valid| |v_ULTIMATE.start_main_~t~0#1.base_7|) 0)))) (forall ((v_ArrVal_76 (Array Int Int)) (v_ArrVal_75 Int)) (= (select (select (store (store |#memory_int| |ULTIMATE.start_main_~p~0#1.base| (store (select |#memory_int| |ULTIMATE.start_main_~p~0#1.base|) (+ |ULTIMATE.start_main_~p~0#1.offset| 4) v_ArrVal_75)) |ULTIMATE.start_main_~t~0#1.base| v_ArrVal_76) |ULTIMATE.start_main_~a~0#1.base|) |ULTIMATE.start_main_~a~0#1.offset|) 1)) (= (select |#valid| |ULTIMATE.start_main_~a~0#1.base|) 1) (= (select |#valid| |ULTIMATE.start_main_~a~0#1.base|) |ULTIMATE.start_main_~flag~0#1|))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate27() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "old(#valid)", "#valid"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int", "#memory_$Pointer$.base", "#memory_$Pointer$.offset", "old(#memory_$Pointer$.offset)", "old(#memory_int)", "old(#memory_$Pointer$.base)"),
				new FunDecl(SmtSortUtils::getIntSort, "~head~0.offset", "~head~0.base", "insert_list_#in~k", "old(~head~0.base)", "insert_list_~l.base", "insert_list_~l.offset", "insert_list_~k", "old(~head~0.offset)"),
		};
		final String formulaAsString = "(and (<= ~head~0.offset 0) (= |#memory_$Pointer$.offset| (store |old(#memory_$Pointer$.offset)| ~head~0.base (select |#memory_$Pointer$.offset| ~head~0.base))) (= |#memory_int| (store |old(#memory_int)| insert_list_~l.base (select |#memory_int| insert_list_~l.base))) (= |insert_list_#in~k| insert_list_~k) (= |old(~head~0.base)| (select (select |#memory_$Pointer$.base| ~head~0.base) 4)) (= (store |old(#valid)| insert_list_~l.base 1) |#valid|) (= (store |old(#valid)| ~head~0.base 1) |#valid|) (= (store |old(#memory_$Pointer$.base)| ~head~0.base (select |#memory_$Pointer$.base| ~head~0.base)) |#memory_$Pointer$.base|) (= (store |old(#memory_$Pointer$.base)| insert_list_~l.base (select |#memory_$Pointer$.base| insert_list_~l.base)) |#memory_$Pointer$.base|) (= (select |old(#valid)| insert_list_~l.base) 0) (= ~head~0.offset 0) (< 0 (+ ~head~0.offset 1)) (exists ((v_ArrVal_1075 (Array Int Int))) (= |#memory_int| (store |old(#memory_int)| insert_list_~l.base v_ArrVal_1075))) (exists ((v_ArrVal_1075 (Array Int Int))) (= (store |old(#memory_int)| ~head~0.base v_ArrVal_1075) |#memory_int|)) (= |#memory_int| (store |old(#memory_int)| ~head~0.base (select |#memory_int| ~head~0.base))) (= |old(~head~0.base)| (select (select |#memory_$Pointer$.base| insert_list_~l.base) 4)) (= insert_list_~l.offset 0) (= (select |#valid| ~head~0.base) 1) (= (select (select |#memory_$Pointer$.offset| insert_list_~l.base) 4) |old(~head~0.offset)|) (= (select |#valid| insert_list_~l.base) 1) (= |old(~head~0.offset)| (select (select |#memory_$Pointer$.offset| ~head~0.base) 4)) (= (select |old(#valid)| ~head~0.base) 0) (= |insert_list_#in~k| (select (select |#memory_int| ~head~0.base) 0)) (= |#memory_$Pointer$.offset| (store |old(#memory_$Pointer$.offset)| insert_list_~l.base (select |#memory_$Pointer$.offset| insert_list_~l.base))) (= |insert_list_#in~k| (select (select |#memory_int| insert_list_~l.base) 0)))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate28() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~y~0#1", "ULTIMATE.start_main_~x~0#1"),
		};
		final String formulaAsString = "(or (and (<= (+ 2 |ULTIMATE.start_main_~x~0#1|) 0) (<= |ULTIMATE.start_main_~y~0#1| 0)) (exists ((|v_ULTIMATE.start_main_~x~0#1_15| Int)) (and (<= 0 (* |v_ULTIMATE.start_main_~x~0#1_15| |ULTIMATE.start_main_~y~0#1|)) (<= (+ |ULTIMATE.start_main_~x~0#1| 1) |v_ULTIMATE.start_main_~x~0#1_15|) (<= |v_ULTIMATE.start_main_~x~0#1_15| 0) (not (= |v_ULTIMATE.start_main_~x~0#1_15| 0)))) (and (< 0 |ULTIMATE.start_main_~x~0#1|) (<= 0 (* |ULTIMATE.start_main_~x~0#1| |ULTIMATE.start_main_~y~0#1|))) (and (<= |ULTIMATE.start_main_~y~0#1| 2147483647) (<= 0 (* |ULTIMATE.start_main_~x~0#1| |ULTIMATE.start_main_~y~0#1|))))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate29() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_~a~0#1.offset", "ULTIMATE.start_main_~a~0#1.base", "ULTIMATE.start_mkdup_~i~0#1", "ULTIMATE.start_mkdup_~a#1.base", "ULTIMATE.start_main_~n~0#1", "ULTIMATE.start_mkdup_~a#1.offset", "ULTIMATE.start_mkdup_~n#1"),
		};
		final String formulaAsString = "(and (< |ULTIMATE.start_mkdup_~i~0#1| |ULTIMATE.start_mkdup_~n#1|) (= ((as const (Array Int Int)) 0) (select |#memory_int| |ULTIMATE.start_main_~a~0#1.base|)) (<= 0 |ULTIMATE.start_mkdup_~i~0#1|) (= |ULTIMATE.start_main_~a~0#1.base| |ULTIMATE.start_mkdup_~a#1.base|) (= |ULTIMATE.start_main_~a~0#1.offset| |ULTIMATE.start_mkdup_~a#1.offset|) (<= |ULTIMATE.start_mkdup_~n#1| |ULTIMATE.start_main_~n~0#1|) (exists ((|v_ULTIMATE.start_mkdup_~a#1.base_BEFORE_CALL_7| Int)) (= ((as const (Array Int Int)) 0) (select |#memory_int| |v_ULTIMATE.start_mkdup_~a#1.base_BEFORE_CALL_7|))))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void sgiCandidate30() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "#valid"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntIntSort, "#memory_int"),
				new FunDecl(SmtSortUtils::getIntSort, "ULTIMATE.start_main_#t~malloc15#1.base", "ULTIMATE.start_main_~n~0#1"),
		};
		final String formulaAsString = "(and (exists ((|v_ULTIMATE.start_main_#t~malloc15#1.base_BEFORE_CALL_1| Int)) (= (select |#valid| |v_ULTIMATE.start_main_#t~malloc15#1.base_BEFORE_CALL_1|) 1)) (< |ULTIMATE.start_main_~n~0#1| 1073741824) (= ((as const (Array Int Int)) 0) (select |#memory_int| |ULTIMATE.start_main_#t~malloc15#1.base|)) (= (select |#valid| |ULTIMATE.start_main_#t~malloc15#1.base|) 1) (< 1 |ULTIMATE.start_main_~n~0#1|))";
		final String expectedResultAsString = formulaAsString;
		QuantifierEliminationTest.runQuantifierEliminationTest(funDecls, formulaAsString, expectedResultAsString, true, mServices, mLogger, mMgdScript, mCsvWriter);
	}


	//@formatter:on
}