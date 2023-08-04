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

import org.hamcrest.MatcherAssert;
import org.hamcrest.core.IsEqual;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.StatisticsScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.CondisDepthCodeGenerator.CondisDepthCode;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;

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
	private static final long TEST_TIMEOUT_MILLISECONDS = 20_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
	private static final String SOLVER_COMMAND = "cvc4 --incremental --lang smt";
	// private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -t:12000 -memory:2024 -smt2 -in";
	// private static final String SOLVER_COMMAND = "INTERNAL_SMTINTERPOL:10000";

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
	public void ddaExample6() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x"), };
		final String formulaAsString = "(and (distinct x 1) (or (<= x 0) (> x 2) (= x 1)))";
		final String expectedResultAsString = "(and (not (= x 1)) (or (<= x 0) (< 2 x)))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void dda2TestExample01() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x", "y", "z"), };
		final String formulaAsString =
				"(or (and (or (> x 1) (= (+ y z) 1)) (<= y 2)) (and (< x 2) (or (< x 5) (>= z 2))))";
		final String expectedResultAsString = "(or (<= y 2) (< x 2))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.SIMPLIFY_DDA2,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	// simplify leaf to false in conjunction
	public void dda2TestExample04() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "Y", "X"), };
		final String formulaAsString = "(or (= Y 0) (and (= X 2) (>= X 5) (< X 8)))";
		final String expectedResultAsString = "(= Y 0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.SIMPLIFY_DDA2,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void alternativeRepresentations() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x", "y"), };
		final String formulaAsString = "(and (distinct y x) (or (<= x 0) (> x 2) (= x y)))";
		final String expectedResultAsString = "(and (not (= x y)) (or (<= x 0) (< 2 x)))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void distinctAndLess1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (not (= x 7.0)) (< x 7.0))";
		final String expectedResultAsString = "(< x 7.0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void distinctAndLess2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (not (= x 7.0)) (< x 8.0))";
		final String expectedResultAsString = "(and (< x 8.0) (not (= 7.0x)))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void distinctAndLeq1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (not (= x 7.0)) (<= x 6.0))";
		final String expectedResultAsString = "(<= x 6.0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void distinctAndLeq2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (not (= x 7.0)) (<= x 7.0))";
		final String expectedResultAsString = "(and (not (= x 7.0)) (<= x 7.0))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void distinctAndGt1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (not (= x 7.0)) (> x 7.0))";
		final String expectedResultAsString = "(< 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void distinctAndGt2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (not (= x 7.0)) (> x 8.0))";
		final String expectedResultAsString = "(< 8.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void distinctAndGeq1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (not (= x 7.0)) (>= x 8.0))";
		final String expectedResultAsString = "(<= 8.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void distinctAndGeq2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (not (= x 7.0)) (>= x 7.0))";
		final String expectedResultAsString = "(and (not (= 7.0 x)) (<= 7.0 x))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void eqAndLess1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (= x 7.0) (< x 7.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void eqAndLess2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (= x 7.0) (< x 8.0))";
		final String expectedResultAsString = "(= 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void eqAndLeq1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (= x 7.0) (<= x 6.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void eqAndLeq2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (= x 7.0) (<= x 7.0))";
		final String expectedResultAsString = "(= 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void eqAndGt1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (= x 7.0) (> x 7.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void eqAndGt2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (= x 7.0) (> x 6.0))";
		final String expectedResultAsString = "(= 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void eqAndGeq1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (= x 7.0) (>= x 8.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void eqAndGeq2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (= x 7.0) (>= x 7.0))";
		final String expectedResultAsString = "(= 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void geqAndLess1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (>= x 7.0) (< x 7.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void geqAndLess2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (>= x 7.0) (< x 8.0))";
		final String expectedResultAsString = "(and (< x 8.0) (<= 7.0 x))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void geqAndLeq1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (>= x 7.0) (<= x 6.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void geqAndLeq2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (>= x 7.0) (<= x 7.0))";
		final String expectedResultAsString = "(and (<= x 7.0) (<= 7.0 x))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void geqAndGt1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (>= x 7.0) (> x 7.0))";
		final String expectedResultAsString = "(< 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void geqAndGt2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (>= x 7.0) (> x 6.0))";
		final String expectedResultAsString = "(<= 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void geqAndGeq1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (>= x 7.0) (>= x 6.0))";
		final String expectedResultAsString = "(<= 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void geqAndGeq2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (>= x 7.0) (>= x 8.0))";
		final String expectedResultAsString = "(<= 8.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterAndLess1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (> x 7.0) (< x 7.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterAndLess2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (> x 7.0) (< x 8.0))";
		final String expectedResultAsString = "(and (< x 8.0) (< 7.0 x))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterAndLeq1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (> x 7.0) (<= x 7.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterAndLeq2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (> x 7.0) (<= x 8.0))";
		final String expectedResultAsString = "(and  (< 7.0 x) (<= x 8.0))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterAndGt1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (> x 7.0) (> x 8.0))";
		final String expectedResultAsString = "(< 8.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterAndGt2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (> x 7.0) (> x 6.0))";
		final String expectedResultAsString = "(< 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterAndGeq1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (> x 7.0) (>= x 7.0))";
		final String expectedResultAsString = "(< 7.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void greaterAndGeq2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (> x 7.0) (>= x 8.0))";
		final String expectedResultAsString = "(<= 8.0 x)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void leqAndLess1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (<= x 7.0) (< x 7.0))";
		final String expectedResultAsString = "(< x 7.0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void leqAndLess2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (<= x 7.0) (< x 6.0))";
		final String expectedResultAsString = "(< x 6.0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void leqAndLeq1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (<= x 7.0) (<= x 6.0))";
		final String expectedResultAsString = "(<= x 6.0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void leqAndLeq2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (<= x 7.0) (<= x 8.0))";
		final String expectedResultAsString = "(<= x 7.0)";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void leqAndGt1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (<= x 7.0) (> x 7.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void leqAndGt2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (<= x 7.0) (> x 6.0))";
		final String expectedResultAsString = "(and (<= x 7.0) (< 6.0 x))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void leqAndGeq1() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (<= x 7.0) (>= x 6.0))";
		final String expectedResultAsString = "(and (<= x 7.0) (<= 6.0 x))";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void leqAndGeq2() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "x"),
				new FunDecl(SmtSortUtils::getBoolSort, "A"), };
		final String formulaAsString = "(and (<= x 7.0) (>= x 8.0))";
		final String expectedResultAsString = "false";
		runSimplificationTest(funDecls, formulaAsString, expectedResultAsString, SimplificationTechnique.POLY_PAC,
				mServices, mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Benchmark from MCR. Quantifier elimination did not terminate.
	 */
	@Test
	public void mcrPthreadWmm01() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x0", "x1"), };
		final String formulaAsString =
				"(exists ((v_x1_32 Int) (v_x2_42 Int) (v_x1_28 Int) (v_x2_38 Int) (v_x2_60 Int) (v_x2_54 Int) (v_x1_41 Int) (v_x1_56 Int) (v_x0_46 Int) (v_x0_59 Int) (v_x3_53 Int)) (let ((.cse47 (+ v_x1_56 1)) (.cse4 (<= 0 v_x1_56)) (.cse2 (<= v_x1_56 0)) (.cse5 (<= 0 x1)) (.cse1 (<= x1 0))) (or (let ((.cse0 (<= v_x1_56 x1)) (.cse3 (<= x1 v_x1_56))) (and .cse0 .cse1 .cse2 .cse3 .cse4 .cse5 (let ((.cse23 (<= v_x2_42 v_x2_54)) (.cse52 (+ v_x2_38 1)) (.cse53 (+ v_x2_54 1)) (.cse29 (<= v_x2_42 0))) (let ((.cse22 (<= 0 v_x2_38)) (.cse7 (<= 0 v_x2_54)) (.cse49 (not .cse29)) (.cse48 (<= .cse53 v_x2_42)) (.cse50 (<= .cse52 v_x2_42)) (.cse51 (or (<= v_x2_42 v_x2_38) .cse23)) (.cse6 (<= v_x2_38 0)) (.cse32 (<= v_x2_54 0)) (.cse26 (<= 0 v_x2_42))) (or (let ((.cse8 (<= v_x2_38 v_x2_60)) (.cse9 (ite .cse48 (=> .cse49 (or .cse29 (ite (not .cse50) .cse6 .cse51))) .cse32)) (.cse10 (<= v_x2_60 0)) (.cse36 (<= v_x2_60 v_x2_38))) (and .cse6 .cse7 .cse8 .cse9 .cse1 .cse10 (let ((.cse11 (<= v_x1_41 v_x1_56))) (or (let ((.cse13 (<= v_x1_41 x1)) (.cse14 (<= v_x1_41 0)) (.cse15 (<= 0 v_x1_41)) (.cse12 (<= x1 v_x1_41)) (.cse16 (<= v_x1_56 v_x1_41))) (and .cse11 .cse0 .cse1 .cse3 .cse12 .cse5 (or (and .cse12 .cse13) (ite .cse14 (and (<= (+ v_x1_41 1) 0) .cse15) .cse14)) .cse16 .cse13 (let ((.cse17 (<= 0 v_x0_46))) (or (and (<= (+ v_x0_46 1) 0) .cse17) (let ((.cse33 (<= v_x0_46 0))) (and (let ((.cse44 (<= (+ x0 1) 0))) (let ((.cse18 (not .cse44)) (.cse40 (<= 0 x0))) (ite .cse18 (let ((.cse20 (<= x0 0))) (let ((.cse19 (not .cse20))) (or (ite .cse19 .cse20 (<= 1 x0)) (let ((.cse34 (<= 0 v_x0_59))) (let ((.cse37 (<= v_x0_46 x0)) (.cse42 (<= x0 v_x0_46)) (.cse45 (<= v_x0_46 v_x0_59)) (.cse46 (<= v_x0_59 v_x0_46)) (.cse38 (and (<= (+ v_x0_59 1) 0) .cse34))) (let ((.cse21 (or (and .cse45 .cse46 .cse17 .cse33) .cse38)) (.cse43 (ite .cse19 (or .cse42 .cse20) .cse17)) (.cse41 (ite .cse44 (or .cse37 .cse40) .cse33))) (and .cse21 (or (let ((.cse39 (<= v_x0_59 0))) (and (or (and (let ((.cse30 (+ v_x1_28 1)) (.cse35 (<= 0 v_x1_28))) (or (let ((.cse25 (<= v_x1_32 v_x2_42)) (.cse31 (and (<= (+ v_x1_32 1) 0) (<= 0 v_x1_32)))) (let ((.cse24 (or .cse25 .cse31)) (.cse28 (<= v_x1_28 v_x2_42)) (.cse27 (<= x1 v_x2_42))) (and (<= v_x2_42 v_x1_28) .cse8 .cse22 .cse23 .cse1 (<= 0 v_x2_60) .cse5 .cse24 .cse13 (<= v_x1_28 0) .cse6 .cse11 .cse7 (<= v_x2_42 x1) (or (and .cse25 .cse26 .cse1 .cse27 .cse5 .cse28) (and .cse1 .cse24 .cse5)) .cse27 .cse29 .cse14 .cse9 .cse15 (or (and (<= .cse30 v_x1_32) (<= v_x1_32 v_x1_28)) (and .cse1 .cse5 (<= x1 v_x1_32) (<= v_x1_32 x1)) .cse31) .cse10 .cse12 .cse28 (<= v_x2_54 v_x2_42) (<= v_x0_46 v_x2_54) .cse32 .cse17 .cse33 .cse34 (<= v_x2_42 v_x1_32) .cse26 .cse0 (<= v_x1_41 v_x2_54) .cse2 (<= v_x1_41 v_x2_42) .cse3 .cse4 (<= v_x2_42 v_x1_41) .cse35 .cse36 (or (and .cse1 .cse5) .cse27) .cse16 (<= v_x2_42 v_x1_56)))) (and (<= .cse30 0) .cse35))) .cse37 .cse20 (or .cse38 (and .cse21 .cse34 (or (ite .cse18 (and .cse21 .cse34 .cse39 .cse17) .cse40) .cse38) .cse17)) (<= v_x3_53 0) .cse32 .cse33 .cse17 .cse41 (<= 0 v_x3_53) .cse11 .cse42 .cse7 .cse34 .cse26 .cse39 .cse29 .cse16 .cse40 .cse43 (<= v_x3_53 v_x2_54)) .cse44) .cse34 .cse39 .cse45 .cse46 .cse17 .cse33)) .cse38) (or .cse44 (and .cse42 .cse37 .cse33 .cse17)) .cse43 .cse41 .cse33 .cse17)))) .cse44))) .cse40))) .cse33 .cse17)))))) (and (<= .cse47 v_x1_41) .cse11))) .cse5 .cse36 .cse29 .cse32)) (and (<= .cse52 0) .cse22) (and (<= .cse53 0) .cse7) (ite .cse49 (ite .cse48 (ite .cse50 .cse51 .cse6) .cse32) (and (<= (+ v_x2_42 1) 0) .cse26))))))) (ite .cse2 (and (<= .cse47 0) .cse4) .cse2) (ite .cse1 (and (<= (+ x1 1) 0) .cse5) .cse1))))";
		runSimplificationTest(funDecls, formulaAsString, null, SimplificationTechnique.POLY_PAC, mServices, mLogger,
				mMgdScript, mCsvWriter);
	}

	@Test
	public void mcrPthreadWmm02() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "~x~0", "~x$r_buff0_thd2~0",
				"~x$w_buff0_used~0", "~x$w_buff1_used~0", "~x$w_buff0~0", "~x$w_buff1~0", "~x$r_buff1_thd0~0"), };
		final String formulaAsString =
				"(forall ((~x$r_buff1_thd2~0 Int) (|P1Thread1of1ForFork0_#t~nondet35| Int)) (let ((.cse11 (= (mod ~x$r_buff0_thd2~0 256) 0)) (.cse19 (= (mod ~x$w_buff1_used~0 256) 0)) (.cse20 (= (mod ~x$r_buff1_thd2~0 256) 0))) (let ((.cse2 (= (mod ~x$w_buff0_used~0 256) 0)) (.cse21 (not .cse20)) (.cse18 (not .cse19)) (.cse13 (not .cse11))) (let ((.cse22 (or .cse18 .cse13)) (.cse14 (or .cse13 .cse21)) (.cse15 (not .cse2)) (.cse8 (= (mod |P1Thread1of1ForFork0_#t~nondet35| 256) 0))) (let ((.cse7 (not .cse8)) (.cse3 (and .cse11 .cse19)) (.cse4 (and .cse13 .cse15)) (.cse6 (and .cse11 .cse20)) (.cse1 (and .cse22 .cse14 .cse15))) (or (let ((.cse5 (or .cse2 .cse11))) (let ((.cse0 (let ((.cse16 (and .cse5 .cse13 .cse15))) (let ((.cse9 (let ((.cse17 (and .cse8 (or .cse7 (and (or .cse2 .cse16 .cse3 .cse6) .cse22 .cse14 .cse15))))) (and (or .cse7 (and (or (and (or .cse17 .cse4) (or .cse2 .cse11 (and (or .cse7 (and .cse18 (or .cse2 .cse19 .cse20) .cse21 .cse15)) .cse8))) .cse2 .cse3 .cse6) (or .cse17 .cse1))) (or .cse17 .cse8))))) (and (or .cse8 .cse9) (or .cse7 (and (or .cse2 .cse3 (let ((.cse10 (let ((.cse12 (and (or .cse7 (and (or .cse2 .cse16 .cse11 .cse6) .cse13 .cse14 .cse15)) .cse8))) (and (or .cse12 .cse8) (or .cse7 (and (or (and .cse5 (or .cse4 .cse12)) .cse2 .cse11 .cse6) (or .cse12 (and .cse13 .cse14 .cse15)))))))) (and (or .cse10 .cse4) (or .cse2 .cse11 .cse10))) .cse6) (or .cse1 .cse9)))))))) (and (or (and (or .cse0 .cse1) (or .cse2 .cse3 (and (or .cse4 .cse0) .cse5) .cse6)) .cse7) (or .cse0 .cse8)))) (let ((.cse25 (<= ~x$w_buff0~0 0)) (.cse26 (= 0 ~x$w_buff1~0)) (.cse27 (= ~x$r_buff1_thd0~0 0))) (let ((.cse31 (let ((.cse32 (let ((.cse33 (and (= ~x~0 1) .cse25 .cse26 .cse27))) (and (or .cse7 (and (or .cse2 .cse3 (and (or .cse33 .cse4) (or .cse2 .cse11 .cse33)) .cse6) (or .cse33 .cse1))) (or .cse33 .cse8))))) (and (or .cse7 (and (or .cse32 .cse1) (or .cse2 .cse3 (and (or .cse2 .cse11 .cse32) (or .cse4 .cse32)) .cse6))) (or .cse32 .cse8))))) (let ((.cse28 (or .cse31 .cse8))) (and (or .cse2 .cse3 (and (or .cse4 (and (or .cse7 (let ((.cse23 (let ((.cse24 (and .cse25 .cse26 (= ~x$w_buff1~0 1) .cse27))) (and (or .cse24 .cse8) (or (and (or .cse24 .cse1) (or .cse2 .cse3 (and (or .cse4 .cse24) (or .cse2 .cse11 .cse24)) .cse6)) .cse7))))) (and (or (and (or .cse1 .cse23) (or .cse2 .cse3 (and (or .cse2 .cse11 .cse23) (or .cse4 .cse23)) .cse6)) .cse7) (or .cse8 .cse23)))) .cse28)) (or .cse2 .cse11 (and (or .cse7 (let ((.cse29 (let ((.cse30 (and (= ~x$w_buff0~0 1) .cse25 .cse26 .cse27))) (and (or .cse7 (and (or .cse2 .cse3 .cse6 (and (or .cse2 .cse11 .cse30) (or .cse4 .cse30))) (or .cse30 .cse1))) (or .cse30 .cse8))))) (and (or .cse29 .cse8) (or .cse7 (and (or .cse2 .cse3 (and (or .cse2 .cse11 .cse29) (or .cse4 .cse29)) .cse6) (or .cse29 .cse1)))))) .cse28))) .cse6) (or (and (or .cse7 .cse31) .cse28) .cse1)))))))))))";
		runSimplificationTest(funDecls, formulaAsString, null, SimplificationTechnique.POLY_PAC, mServices, mLogger,
				mMgdScript, mCsvWriter);
	}

	@Test /////
	public void mcrPthreadWmm02Inner() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "~x$r_buff1_thd2~0",
				"P1Thread1of1ForFork0_#t~nondet35", "~x~0", "~x$r_buff0_thd2~0", "~x$w_buff0_used~0",
				"~x$w_buff1_used~0", "~x$w_buff0~0", "~x$w_buff1~0", "~x$r_buff1_thd0~0"), };
		final String formulaAsString =
				"(let ((.cse11 (= (mod ~x$r_buff0_thd2~0 256) 0)) (.cse19 (= (mod ~x$w_buff1_used~0 256) 0)) (.cse20 (= (mod ~x$r_buff1_thd2~0 256) 0))) (let ((.cse2 (= (mod ~x$w_buff0_used~0 256) 0)) (.cse21 (not .cse20)) (.cse18 (not .cse19)) (.cse13 (not .cse11))) (let ((.cse22 (or .cse18 .cse13)) (.cse14 (or .cse13 .cse21)) (.cse15 (not .cse2)) (.cse8 (= (mod |P1Thread1of1ForFork0_#t~nondet35| 256) 0))) (let ((.cse7 (not .cse8)) (.cse3 (and .cse11 .cse19)) (.cse4 (and .cse13 .cse15)) (.cse6 (and .cse11 .cse20)) (.cse1 (and .cse22 .cse14 .cse15))) (or (let ((.cse5 (or .cse2 .cse11))) (let ((.cse0 (let ((.cse16 (and .cse5 .cse13 .cse15))) (let ((.cse9 (let ((.cse17 (and .cse8 (or .cse7 (and (or .cse2 .cse16 .cse3 .cse6) .cse22 .cse14 .cse15))))) (and (or .cse7 (and (or (and (or .cse17 .cse4) (or .cse2 .cse11 (and (or .cse7 (and .cse18 (or .cse2 .cse19 .cse20) .cse21 .cse15)) .cse8))) .cse2 .cse3 .cse6) (or .cse17 .cse1))) (or .cse17 .cse8))))) (and (or .cse8 .cse9) (or .cse7 (and (or .cse2 .cse3 (let ((.cse10 (let ((.cse12 (and (or .cse7 (and (or .cse2 .cse16 .cse11 .cse6) .cse13 .cse14 .cse15)) .cse8))) (and (or .cse12 .cse8) (or .cse7 (and (or (and .cse5 (or .cse4 .cse12)) .cse2 .cse11 .cse6) (or .cse12 (and .cse13 .cse14 .cse15)))))))) (and (or .cse10 .cse4) (or .cse2 .cse11 .cse10))) .cse6) (or .cse1 .cse9)))))))) (and (or (and (or .cse0 .cse1) (or .cse2 .cse3 (and (or .cse4 .cse0) .cse5) .cse6)) .cse7) (or .cse0 .cse8)))) (let ((.cse25 (<= ~x$w_buff0~0 0)) (.cse26 (= 0 ~x$w_buff1~0)) (.cse27 (= ~x$r_buff1_thd0~0 0))) (let ((.cse31 (let ((.cse32 (let ((.cse33 (and (= ~x~0 1) .cse25 .cse26 .cse27))) (and (or .cse7 (and (or .cse2 .cse3 (and (or .cse33 .cse4) (or .cse2 .cse11 .cse33)) .cse6) (or .cse33 .cse1))) (or .cse33 .cse8))))) (and (or .cse7 (and (or .cse32 .cse1) (or .cse2 .cse3 (and (or .cse2 .cse11 .cse32) (or .cse4 .cse32)) .cse6))) (or .cse32 .cse8))))) (let ((.cse28 (or .cse31 .cse8))) (and (or .cse2 .cse3 (and (or .cse4 (and (or .cse7 (let ((.cse23 (let ((.cse24 (and .cse25 .cse26 (= ~x$w_buff1~0 1) .cse27))) (and (or .cse24 .cse8) (or (and (or .cse24 .cse1) (or .cse2 .cse3 (and (or .cse4 .cse24) (or .cse2 .cse11 .cse24)) .cse6)) .cse7))))) (and (or (and (or .cse1 .cse23) (or .cse2 .cse3 (and (or .cse2 .cse11 .cse23) (or .cse4 .cse23)) .cse6)) .cse7) (or .cse8 .cse23)))) .cse28)) (or .cse2 .cse11 (and (or .cse7 (let ((.cse29 (let ((.cse30 (and (= ~x$w_buff0~0 1) .cse25 .cse26 .cse27))) (and (or .cse7 (and (or .cse2 .cse3 .cse6 (and (or .cse2 .cse11 .cse30) (or .cse4 .cse30))) (or .cse30 .cse1))) (or .cse30 .cse8))))) (and (or .cse29 .cse8) (or .cse7 (and (or .cse2 .cse3 (and (or .cse2 .cse11 .cse29) (or .cse4 .cse29)) .cse6) (or .cse29 .cse1)))))) .cse28))) .cse6) (or (and (or .cse7 .cse31) .cse28) .cse1))))))))))";
		runSimplificationTest(funDecls, formulaAsString, null, SimplificationTechnique.POLY_PAC, mServices, mLogger,
				mMgdScript, mCsvWriter);
	}

	@Test
	public void missingConjuncts() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x"), };
		final String formulaAsString = "(and (<= x 11) (not (= (+ x (- 2)) 0)) (<= 11 x))";
		final String simplified = "(and (<= x 11) (<= 11 x))";
		runSimplificationTest(funDecls, formulaAsString, simplified, SimplificationTechnique.POLY_PAC, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void reqchecker_vacuity_test82() {
		final FunDecl[] funDecls =
				new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "Constraint_assumption_ct0_pc", "req1_ct0_pc"), };
		final String formulaAsString =
				"(and (= Constraint_assumption_ct0_pc 0) (let ((.cse2 (= (+ req1_ct0_pc (- 16)) 0)) (.cse1 (= (+ req1_ct0_pc (- 15)) 0)) (.cse6 (= (+ req1_ct0_pc (- 10)) 0)) (.cse4 (= (+ req1_ct0_pc (- 9)) 0))) (let ((.cse20 (not .cse4)) (.cse5 (= (+ req1_ct0_pc (- 6)) 0)) (.cse19 (not .cse6)) (.cse9 (= (+ req1_ct0_pc (- 8)) 0)) (.cse11 (= (+ req1_ct0_pc (- 14)) 0)) (.cse13 (= (+ req1_ct0_pc (- 13)) 0)) (.cse14 (= (+ req1_ct0_pc (- 5)) 0)) (.cse16 (= (+ req1_ct0_pc (- 12)) 0)) (.cse3 (= (+ req1_ct0_pc (- 2)) 0)) (.cse17 (= (+ req1_ct0_pc (- 11)) 0)) (.cse22 (not .cse1)) (.cse23 (not .cse2)) (.cse15 (= req1_ct0_pc 0)) (.cse10 (= (+ req1_ct0_pc (- 7)) 0)) (.cse12 (= (+ req1_ct0_pc (- 4)) 0)) (.cse18 (= (+ req1_ct0_pc (- 1)) 0))) (or (let ((.cse21 (or .cse23 .cse15 .cse5 .cse3)) (.cse7 (= (+ req1_ct0_pc (- 3)) 0)) (.cse0 (or .cse22 .cse15 .cse5 .cse3))) (and .cse0 (or .cse1 (and (or .cse2 (let ((.cse8 (or .cse4 .cse9 .cse10 .cse11 .cse12 .cse7 .cse13 .cse14 .cse15 .cse5 .cse6 .cse16 .cse3 .cse17 .cse18))) (and (or (not .cse3) .cse4 .cse5 .cse6 .cse7 (and .cse8 (or .cse1 .cse4 .cse9 .cse10 .cse2 .cse11 .cse12 .cse7 .cse13 .cse14 .cse15 .cse5 .cse6 .cse16 .cse3 .cse17 .cse18)) .cse18) (or (and .cse0 (or .cse1 (and (or .cse2 (and (or .cse4 (and (or .cse15 .cse5 .cse19) (or .cse5 .cse6 (and .cse8 .cse15)))) (or .cse15 .cse20 .cse5))) .cse21))) .cse3)))) .cse21)) .cse21 (or (and (or .cse1 .cse4 .cse9 .cse10 .cse11 .cse12 .cse7 .cse13 .cse14 .cse15 .cse5 .cse6 .cse16 .cse3 .cse17 .cse18) .cse0) .cse2))) (let ((.cse25 (or .cse23 .cse15 .cse10 .cse12 .cse18))) (let ((.cse24 (or .cse22 .cse15 .cse10 .cse12 .cse18)) (.cse26 (and .cse25 (or .cse4 .cse9 .cse10 .cse2 .cse11 .cse12 .cse13 .cse14 .cse15 .cse6 .cse16 .cse3 .cse17 .cse18)))) (and (or (and .cse24 (or .cse1 (and .cse25 (or (and (or .cse15 .cse20 .cse10 .cse12 .cse18) (or (and (or .cse5 .cse6 .cse3 .cse26) (or .cse15 .cse19 .cse10 .cse12 .cse18)) .cse4)) .cse2)))) .cse3) (or .cse3 (and .cse24 (or .cse1 .cse3 .cse26)))))) (= (+ req1_ct0_pc (- 17)) 0) (= (+ req1_ct0_pc (- 20)) 0) (= (+ req1_ct0_pc (- 19)) 0) (= (+ req1_ct0_pc (- 18)) 0)))))";
		final String simplified = null;
		runSimplificationTest(funDecls, formulaAsString, simplified, SimplificationTechnique.POLY_PAC, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void forester_heap_dll_optional() {
		final FunDecl[] funDecls = new FunDecl[] {
				new FunDecl(QuantifierEliminationTest::getBitvectorSort32, "main_~head~0.offset", "main_~head~0.base",
						"v_main_#t~malloc6.base_4", "main_#t~mem7.offset", "v_subst_6", "v_DerPreprocessor_6",
						"v_DerPreprocessor_7", "v_DerPreprocessor_8"),
				new FunDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "#valid"), };
		final String formulaAsString =
				"(or (not (= (_ bv0 1) (select |#valid| |v_main_#t~malloc6.base_4|))) (let ((.cse40 (bvadd (_ bv12 32) main_~head~0.offset))) (let ((.cse36 (= v_subst_6 .cse40)) (.cse35 (= |v_main_#t~malloc6.base_4| main_~head~0.base))) (let ((.cse23 (not (= (_ bv0 32) (bvadd v_DerPreprocessor_6 (_ bv4294967294 32))))) (.cse21 (and .cse36 .cse35)) (.cse22 (not (= (_ bv0 32) (bvadd v_DerPreprocessor_8 (_ bv4294967294 32))))) (.cse37 (= (bvadd v_subst_6 (_ bv12 32)) .cse40)) (.cse38 (= (bvadd v_subst_6 (_ bv8 32)) .cse40)) (.cse39 (= .cse40 (bvadd (_ bv4 32) |main_#t~mem7.offset|)))) (let ((.cse9 (and .cse39 .cse35)) (.cse3 (not .cse39)) (.cse4 (and .cse38 .cse35)) (.cse2 (not .cse38)) (.cse12 (not .cse37)) (.cse18 (or .cse21 .cse22)) (.cse0 (and .cse37 .cse35)) (.cse20 (or .cse21 .cse23)) (.cse16 (not .cse36)) (.cse8 (not .cse35))) (let ((.cse1 (or .cse2 .cse8 (let ((.cse34 (or .cse16 .cse8 .cse23))) (let ((.cse33 (and .cse20 .cse34))) (let ((.cse27 (or .cse0 .cse16 .cse8 .cse23)) (.cse29 (or (and .cse18 .cse34) .cse0)) (.cse30 (or .cse0 .cse33))) (and (or (let ((.cse28 (or .cse12 .cse16 .cse8 .cse23))) (let ((.cse26 (or .cse2 (and .cse28 .cse30) .cse8))) (and (or .cse9 (and .cse26 (or .cse4 (and .cse27 .cse28)))) (or .cse3 (and .cse26 (or (and .cse28 .cse29) .cse4)) .cse8)))) .cse4) (or .cse2 .cse8 (let ((.cse31 (or .cse12 .cse33 .cse8))) (let ((.cse32 (or .cse2 .cse8 (and .cse31 .cse30)))) (and (or (and (or (and .cse31 .cse27) .cse4) .cse32) .cse9) (or .cse3 (and .cse32 (or .cse4 (and .cse31 .cse29))) .cse8)))))))))))) (and (or .cse0 (and .cse1 (or (let ((.cse17 (not (= (_ bv0 32) (bvadd v_DerPreprocessor_7 (_ bv4294967294 32)))))) (let ((.cse19 (or .cse16 .cse8 .cse17))) (let ((.cse13 (and .cse20 .cse19))) (let ((.cse10 (or .cse0 .cse16 .cse8 .cse17)) (.cse6 (or .cse0 (and .cse18 .cse19))) (.cse11 (or .cse0 .cse13))) (and (or .cse2 (let ((.cse5 (or .cse12 .cse13 .cse8))) (let ((.cse7 (or .cse2 .cse8 (and .cse5 .cse11)))) (and (or .cse3 (and (or .cse4 (and .cse5 .cse6)) .cse7) .cse8) (or .cse9 (and .cse7 (or .cse4 (and .cse5 .cse10))))))) .cse8) (or (let ((.cse15 (or .cse12 .cse16 .cse8 .cse17))) (let ((.cse14 (or .cse2 (and .cse11 .cse15) .cse8))) (and (or .cse9 (and .cse14 (or .cse4 (and .cse10 .cse15)))) (or .cse3 .cse8 (and .cse14 (or .cse4 (and .cse15 .cse6))))))) .cse4)))))) .cse4))) (or .cse12 .cse8 (and .cse1 (or (and (or .cse4 (and (or .cse3 .cse8 (and (or .cse21 .cse0 .cse4 .cse22) (or .cse2 .cse21 .cse0 .cse8 .cse23))) (or .cse2 .cse21 .cse0 .cse9 .cse8 .cse23))) (or .cse2 .cse8 (let ((.cse25 (or .cse21 .cse12 .cse8 .cse23))) (let ((.cse24 (or .cse2 (and .cse25 (or .cse21 .cse0 .cse23)) .cse8))) (and (or (and (or .cse21 .cse12 .cse8 .cse4 .cse23) .cse24) .cse9) (or .cse3 .cse8 (and .cse24 (or (and (or .cse21 .cse0 .cse22) .cse25) .cse4)))))))) .cse4))))))))))";
		final String simplified = null;
		runSimplificationTest(funDecls, formulaAsString, simplified, SimplificationTechnique.POLY_PAC, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void rtinconsistency_test112() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "req1_ct0_X4", "req2_ct0_X4"),
				new FunDecl(SmtSortUtils::getIntSort, "req1_ct0_pc", "req2_ct0_pc"), };
		final String formulaAsString =
				"(let ((.cse32 (= 5 req1_ct0_pc)) (.cse22 (< 0.0 req1_ct0_X4))) (let ((.cse20 (= 6 req1_ct0_pc)) (.cse51 (and .cse32 .cse22))) (let ((.cse0 (= req2_ct0_pc 1)) (.cse50 (or .cse51 .cse22)) (.cse8 (not .cse20)) (.cse7 (= req2_ct0_pc 6)) (.cse43 (= req2_ct0_pc 4)) (.cse21 (= req2_ct0_pc 2)) (.cse15 (= req2_ct0_pc 3)) (.cse16 (= req2_ct0_pc 5))) (and (or .cse0 (let ((.cse39 (= 3 req1_ct0_pc)) (.cse38 (= req1_ct0_pc 4))) (let ((.cse40 (not .cse38)) (.cse41 (not .cse39))) (let ((.cse14 (not .cse43)) (.cse29 (not .cse16)) (.cse30 (not .cse15)) (.cse31 (and .cse40 .cse41))) (let ((.cse12 (or .cse31 .cse20 .cse32)) (.cse24 (< req2_ct0_X4 req1_ct0_X4)) (.cse26 (<= req2_ct0_X4 req1_ct0_X4)) (.cse33 (= req2_ct0_pc 0)) (.cse17 (and .cse14 .cse29 .cse30))) (let ((.cse47 (or .cse29 .cse15)) (.cse49 (or .cse43 .cse15 .cse17)) (.cse36 (not .cse7)) (.cse18 (or (and (or .cse33 .cse38 .cse14 .cse39) .cse29 (or (and (or (and .cse33 .cse21) .cse15) .cse30) .cse43)) .cse8)) (.cse13 (not .cse21)) (.cse34 (< 0.0 req2_ct0_X4)) (.cse35 (or .cse24 .cse26)) (.cse19 (and .cse12 .cse32 .cse22 .cse26))) (let ((.cse10 (and .cse18 (or .cse19 .cse20 (and .cse35 (or .cse31 .cse20 .cse32 (and .cse18 (or (and (or (and .cse14 (or .cse13 .cse43 .cse15 .cse17) .cse29 (or (and .cse35 (or (and .cse14 .cse29 (or .cse15 (and .cse33 .cse14)) .cse30) .cse31 .cse20 .cse32) .cse22) .cse21) .cse30) .cse31 .cse20 .cse32) .cse34 .cse35) .cse19 .cse20))) .cse50)))) (.cse44 (and .cse47 .cse49 .cse36)) (.cse25 (or .cse43 .cse15 .cse16 .cse17))) (let ((.cse37 (or (and .cse18 (or (and (or .cse33 (and .cse35 (or (and .cse34 .cse14 .cse29 .cse30) .cse31 .cse20 .cse32))) (or .cse43 .cse15 .cse16 (not .cse33) (and .cse14 (or (and .cse50 (or .cse40 .cse21 .cse32) .cse22) .cse51)))) .cse20)) (and .cse34 .cse21 .cse25))) (.cse11 (and .cse12 (or .cse44 .cse43) .cse21 .cse22)) (.cse9 (and (or .cse10 (and .cse21 (or (and (or .cse31 .cse20 .cse32 (and .cse14 .cse49 .cse29 .cse30)) .cse26) .cse43 .cse15))) .cse50 .cse22)) (.cse46 (and .cse20 (or .cse38 .cse39))) (.cse42 (not .cse32))) (let ((.cse1 (or (and (or .cse8 (and (or .cse21 (and (or .cse7 (and .cse29 .cse30)) (or .cse33 .cse24 .cse36 .cse16 .cse26))) (or .cse13 (and .cse47 .cse36)))) (or .cse20 (let ((.cse48 (or .cse31 .cse32))) (and (or .cse33 .cse7 (and (or .cse24 .cse21 .cse26) .cse48) .cse29) (or (and (or .cse36 (and .cse35 .cse40 .cse41 .cse42)) (or (and .cse48 .cse26) .cse33 .cse7 .cse21 .cse30)) .cse16))))) .cse43)) (.cse2 (or (and .cse12 (or .cse33 .cse24 .cse46 .cse26)) .cse21 .cse36 .cse16)) (.cse3 (or (and (or (and (or .cse9 .cse10 .cse11) .cse20) .cse43 .cse15) .cse21) .cse7 .cse9 .cse10)) (.cse4 (or .cse33 (let ((.cse45 (or .cse24 .cse46 .cse26))) (and .cse12 .cse45 (or .cse33 (and .cse12 .cse45)))) .cse21 .cse36 .cse16)) (.cse6 (or .cse7 (and (or .cse43 (and (or (and (or .cse44 .cse8) (or .cse43 (and .cse38 .cse32) .cse20 .cse15) .cse22) .cse9) .cse37 .cse25 .cse22)) .cse21) .cse10)) (.cse23 (or .cse33 .cse7 .cse14 .cse21 .cse16 (and (or .cse33 .cse38 .cse8 .cse39) (or (and .cse40 .cse26 .cse41 .cse42) .cse20)))) (.cse27 (or .cse7 (and .cse37 .cse22))) (.cse28 (or .cse33 (and .cse12 .cse35) .cse21 .cse36 .cse16))) (let ((.cse5 (or (and .cse1 .cse2 .cse3 .cse4 .cse6 .cse23 .cse27 .cse28 (or .cse33 (and .cse12 (or (and .cse1 .cse34 .cse2 .cse35 .cse3 .cse4 .cse6 .cse23 .cse27 .cse22 .cse28) (and .cse1 .cse2 .cse35 .cse3 .cse4 .cse6 .cse23 .cse27 .cse22 .cse28)) .cse35) .cse21 .cse16)) .cse36))) (and .cse1 .cse2 .cse3 .cse4 .cse5 .cse6 (or .cse7 (and (or .cse8 .cse9 .cse10 .cse11) .cse1 .cse2 (or .cse7 (and .cse1 .cse2 .cse3 .cse4 (or (and .cse12 (or .cse13 (and .cse14 (or .cse15 .cse16 .cse17))) (or (and .cse18 (or .cse19 .cse20)) .cse21) .cse22) (and .cse1 .cse2 .cse3 .cse4 (or .cse7 (and (or .cse7 (and .cse1 .cse2 .cse3 .cse4 .cse6 .cse23 (or .cse24 (and .cse21 .cse25 .cse22) .cse26) .cse27 .cse22 .cse28)) (or (and .cse14 .cse29 .cse30 .cse22) .cse31 .cse20 .cse32) .cse1 .cse2 .cse3 .cse4 .cse5 .cse6 .cse23 .cse27 .cse28)) .cse5 .cse6 .cse23 .cse27 .cse28)) .cse6 .cse23 .cse27 .cse28)) .cse3 .cse4 .cse5 .cse6 (or (and (or .cse15 .cse16) .cse21) .cse9 .cse10 .cse20) .cse23 .cse27 .cse28)) .cse23 .cse27 .cse22 .cse28))))))))))) (or (not .cse0) .cse7 (and (or .cse7 (and .cse8 .cse50 .cse22) .cse21 .cse15 .cse16) .cse8 (or .cse7 .cse51 .cse22)) .cse43 .cse21 .cse15 .cse16)))))";
		final String simplified = null;
		runSimplificationTest(funDecls, formulaAsString, simplified, SimplificationTechnique.POLY_PAC, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Do not add as test. Needs to much time at the moment.
	 */
	public void rtinconsistency_test112_MoreDifficult() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getRealSort, "req1_ct0_X4", "req2_ct0_X4"),
				new FunDecl(SmtSortUtils::getIntSort, "req1_ct0_pc", "req2_ct0_pc"), };
		final String formulaAsString =
				"(let ((.cse49 (= req2_ct0_pc 2)) (.cse28 (= req2_ct0_pc 4))) (let ((.cse41 (= req2_ct0_pc 3)) (.cse87 (not .cse28)) (.cse101 (not .cse49)) (.cse27 (= req2_ct0_pc 5))) (let ((.cse33 (= req2_ct0_pc 6)) (.cse25 (< req2_ct0_X4 req1_ct0_X4)) (.cse102 (or .cse87 (and .cse101 .cse27))) (.cse69 (not .cse41)) (.cse50 (= req2_ct0_pc 1))) (let ((.cse86 (and .cse101 .cse50)) (.cse85 (not .cse27)) (.cse91 (and .cse102 (or (and .cse49 .cse69) .cse28))) (.cse55 (and .cse33 .cse25)) (.cse7 (<= req2_ct0_X4 req1_ct0_X4)) (.cse4 (= 6 req1_ct0_pc))) (let ((.cse22 (= 5 req1_ct0_pc)) (.cse36 (= 2 req1_ct0_pc)) (.cse37 (= req1_ct0_pc 1)) (.cse34 (not .cse4)) (.cse107 (or .cse25 .cse7)) (.cse47 (or .cse50 .cse49 .cse27)) (.cse6 (< 0.0 req1_ct0_X4)) (.cse38 (= 3 req1_ct0_pc)) (.cse66 (and (or .cse33 .cse25) .cse27)) (.cse108 (or .cse91 .cse55 .cse7)) (.cse92 (or .cse86 .cse85)) (.cse53 (= req1_ct0_pc 4)) (.cse97 (not (= req1_ct0_pc 0))) (.cse40 (or .cse50 .cse49))) (let ((.cse57 (= req2_ct0_pc 0)) (.cse89 (and .cse97 .cse40)) (.cse35 (not .cse53)) (.cse80 (not .cse33)) (.cse30 (or .cse50 .cse49 .cse41)) (.cse51 (not .cse50)) (.cse52 (or .cse50 .cse49 .cse41 .cse27)) (.cse88 (or .cse66 (and (or (and .cse108 .cse40 .cse7) .cse27) .cse92) .cse55)) (.cse74 (not .cse38)) (.cse93 (or .cse66 (and (or (and .cse108 .cse40 .cse6 .cse7) .cse27) .cse92) .cse55)) (.cse46 (or (and .cse107 .cse47) .cse55)) (.cse9 (or .cse53 .cse36 .cse37 .cse34 .cse38)) (.cse105 (not .cse22)) (.cse90 (not .cse36)) (.cse83 (and .cse40 .cse6 .cse7)) (.cse82 (and .cse47 .cse40)) (.cse24 (or .cse33 .cse50 .cse49 .cse27))) (let ((.cse13 (or (and (or .cse55 (let ((.cse106 (or (and (or (and .cse107 (or .cse83 .cse33 .cse28 .cse50 .cse27) (or .cse82 .cse27) .cse47 .cse6 .cse24) .cse55) .cse6) .cse4))) (and (or .cse4 (and .cse106 .cse46 .cse9 .cse6 .cse24)) .cse106 .cse47 .cse9 (or .cse55 (and .cse107 (or (and (or .cse53 .cse36 .cse37 .cse38 .cse22) .cse40 .cse6 (or .cse53 (and (or .cse36 .cse37 .cse38) (or .cse105 (and .cse37 .cse90))) .cse38)) .cse27) .cse47))))) .cse6 .cse24) .cse4)) (.cse70 (or .cse53 (and (or (and .cse9 (or (and (or (let ((.cse103 (and .cse40 .cse6))) (and (or (let ((.cse100 (or .cse51 .cse33 (and (or .cse41 (and (or .cse103 .cse49 .cse27) (or .cse49 (and (or (let ((.cse104 (or .cse103 .cse27))) (and (or .cse49 (and .cse6 .cse104) .cse27) .cse104)) .cse41) .cse6) .cse27) .cse40 .cse6)) .cse52 .cse6) .cse28 .cse27))) (and .cse100 (or (and (or (and .cse101 (or (and .cse25 .cse6) .cse27)) .cse80) (or .cse33 (and (or (and (or (and .cse102 (or .cse28 (and (or .cse36 .cse37 .cse85) (or (and .cse30 .cse49) .cse27) (or (and (or (and .cse102 (or .cse28 (and .cse49 .cse6 (or .cse83 .cse41)))) .cse27) (or .cse85 (and .cse101 .cse25)) .cse6) .cse50) .cse100))) .cse50) .cse100) .cse4) .cse9))) .cse50))) .cse38) (or .cse33 (and (or .cse74 (and .cse97 .cse9 (or (and (or .cse6 .cse74) (or .cse103 .cse4 .cse74) .cse40 .cse9 .cse6 (or (and (or .cse4 .cse74 (and .cse40 .cse6 .cse24)) (or (and .cse40 .cse24) .cse4 .cse74) .cse40 .cse9 .cse6 .cse24) .cse4 .cse74)) .cse4))) .cse50 .cse6) .cse28 .cse49 .cse41 .cse27 .cse74))) .cse4) .cse88 (or .cse33 .cse28 (and .cse40 .cse50 .cse6 .cse24) .cse49 .cse41 .cse27 .cse74) .cse9 .cse6 .cse24 .cse93) .cse4)) .cse22) (or .cse105 (and (or .cse37 .cse38) .cse90))))) (.cse71 (or (and .cse90 (or .cse38 (let ((.cse94 (or .cse33 .cse28 .cse41 .cse89 .cse27)) (.cse99 (and .cse97 .cse40 .cse6))) (let ((.cse95 (or .cse33 .cse28 (and .cse94 .cse97 (or .cse99 .cse33 .cse28 .cse41 .cse27) .cse40 .cse6) .cse41 .cse27))) (and (or .cse38 (and (or .cse33 (let ((.cse98 (or .cse99 .cse33 .cse28 .cse4 .cse41 .cse27))) (let ((.cse96 (or (and (or (and .cse6 (or .cse33 (and .cse94 (or (and (or (and .cse94 .cse95 .cse9 .cse98 .cse6 (or .cse38 .cse6)) .cse4) .cse9) .cse38) .cse95 .cse97 .cse40 .cse6) .cse28 .cse41 .cse27)) .cse4) .cse9) .cse38))) (and (or (and (or .cse33 .cse28 .cse38 .cse41 .cse27 (and .cse94 .cse95 .cse96 .cse97 (or .cse33 .cse28 .cse38 .cse41 .cse27 (and .cse94 .cse95 .cse96 .cse97 .cse40 .cse6)) .cse40 .cse9 .cse98 .cse6)) .cse94 .cse95 .cse96 .cse6) .cse38) .cse94 .cse95 .cse96 .cse97 .cse40 .cse6))) .cse28 .cse38 .cse41 .cse27) .cse95 .cse6)) .cse95))))) .cse37 .cse35 .cse4 .cse22)) (.cse72 (or (and .cse88 (or (and (or (and (or .cse53 .cse33 .cse28 .cse49 .cse41 .cse27 .cse74 (and .cse40 .cse50)) (or .cse35 .cse4 (and (or .cse33 .cse37 .cse28 .cse89 .cse27) .cse90)) .cse9) .cse4 .cse22) (or (and (or .cse86 .cse80 .cse27) .cse40 (or .cse91 .cse50) .cse92) .cse33 .cse28 .cse41 .cse27) .cse9) .cse22) .cse6 .cse24 .cse93) .cse4)) (.cse75 (or .cse41 (and (or .cse53 .cse36 .cse50 .cse49 .cse74 (not .cse57)) .cse7))) (.cse23 (<= 0.0 req1_ct0_X4))) (let ((.cse39 (or .cse50 .cse49 .cse80)) (.cse32 (or .cse86 .cse87)) (.cse5 (or .cse33 .cse28 .cse50 .cse49 .cse41 .cse27)) (.cse20 (or (and .cse23 .cse22) .cse4 .cse6)) (.cse31 (or .cse50 .cse49 .cse69)) (.cse29 (or .cse85 .cse50 .cse49)) (.cse54 (or .cse55 (and .cse7 (or .cse57 .cse49) .cse75) .cse50 .cse49 .cse27)) (.cse58 (and (or (let ((.cse81 (or (and (or .cse83 .cse66) .cse47) .cse55))) (let ((.cse84 (or (and .cse81 (or .cse4 (and (or (and (or .cse66 (and .cse40 .cse7)) .cse47 .cse6) .cse55) .cse6 .cse24)) .cse9 .cse6 .cse24) .cse4))) (and .cse81 (or .cse82 .cse55 .cse27) (or (and .cse81 (or .cse83 .cse66 .cse55) .cse9 .cse6 .cse24 .cse84) .cse4) .cse9 .cse6 .cse24 .cse84))) .cse4) .cse13 .cse70 .cse9 .cse24 .cse71 .cse72)) (.cse10 (or .cse4 .cse6))) (let ((.cse0 (let ((.cse68 (or .cse55 (and (or .cse66 (and .cse7 (or .cse57 .cse66 .cse50 .cse49 .cse7))) .cse6))) (.cse73 (or (and (or .cse33 .cse27 (and .cse6 (or .cse57 .cse50 .cse49 .cse27))) .cse9 .cse6 .cse10) .cse4)) (.cse77 (or .cse57 .cse33 .cse50 .cse49 .cse27))) (let ((.cse60 (or (let ((.cse79 (or (and .cse73 (or .cse33 .cse6) .cse9 .cse6 .cse10 (or (and .cse6 .cse77) .cse28 .cse27)) .cse4))) (let ((.cse78 (or .cse4 (and .cse79 .cse9 .cse68 .cse6 .cse10)))) (and .cse78 (or .cse55 (and .cse79 (or .cse4 (and .cse79 .cse78 (or .cse80 .cse7) .cse9 .cse68 .cse6 .cse7 .cse10)) .cse9)) .cse9 .cse68 .cse6 .cse77 .cse10))) .cse4)) (.cse61 (or .cse57 .cse33 .cse58 .cse50 .cse49 .cse41 .cse27))) (let ((.cse59 (and (or (and .cse60 .cse9 .cse6 (or (let ((.cse76 (or (and .cse73 .cse9 .cse6 .cse10) .cse4))) (and (or (and (or (and .cse54 (or (and .cse54 .cse73 (or (and (or .cse57 (and (or .cse53 .cse36 .cse33 .cse28 .cse27 .cse74) .cse7)) (or .cse41 (and (or .cse53 .cse36 .cse28 .cse74) .cse7 .cse75)) .cse7) .cse41) .cse9 .cse6 .cse76 .cse7 .cse10) .cse4) .cse73 .cse9 .cse6 .cse7) .cse55) .cse9 .cse68 .cse6 .cse77 .cse10) .cse4) .cse9 .cse68 .cse6 .cse76 .cse10)) .cse4) .cse77 .cse10 .cse61) .cse4) .cse9 .cse61))) (or .cse59 (let ((.cse62 (and .cse70 .cse9 .cse24 .cse71 .cse72)) (.cse64 (or .cse33 (and .cse23 .cse47 (or (and .cse29 .cse47 (or .cse50 .cse49 .cse69 .cse27)) .cse7)))) (.cse63 (and .cse29 (or (and .cse40 .cse31) .cse27)))) (and (or .cse33 .cse59 (and .cse60 .cse9 .cse61) .cse28 .cse62 .cse50 .cse49 .cse41 .cse27) (or .cse53 .cse36 .cse37 .cse34 (and .cse23 (or .cse36 .cse37 (and (or .cse7 (and (or .cse28 (and (or .cse33 .cse63) .cse39)) .cse32)) .cse23 (or .cse36 .cse37 (and (or (and (or (and .cse64 .cse39) .cse28) .cse32) .cse7) .cse23 .cse24)) .cse24))) .cse38 .cse22) (or (and .cse20 (let ((.cse67 (and (or .cse4 (and .cse20 (or .cse33 (and .cse64 .cse47)) (or .cse33 .cse63 (and .cse27 .cse7)) .cse23 .cse22 .cse24 (or (and (or .cse63 .cse7) .cse23 .cse47 .cse24) .cse33))) .cse23 .cse22))) (or (let ((.cse65 (or .cse4 (and .cse20 (or (and .cse6 .cse7) (and .cse68 .cse6)) .cse6)))) (and .cse65 (or (and .cse46 .cse24) .cse4 (and .cse20 (or .cse4 (and .cse65 (or (and (or (and .cse20 .cse65 .cse6 (or .cse66 .cse55 .cse7)) .cse4) .cse5 .cse7) .cse62) .cse6) .cse67))) .cse6)) .cse4 .cse67))) .cse4)))))))) (.cse1 (or .cse57 .cse33 .cse58 .cse28 .cse50 .cse49 .cse41 .cse27))) (and .cse0 .cse1 (let ((.cse2 (or (and .cse9 .cse6 .cse10) .cse4)) (.cse12 (and .cse0 .cse1 .cse6 .cse7))) (let ((.cse11 (and (let ((.cse14 (and .cse2 (or (let ((.cse56 (or .cse57 .cse33 .cse28 .cse50 .cse49 .cse41 .cse27))) (and (or (and (or (and .cse54 .cse6 .cse7) .cse55) .cse0 .cse1 .cse9 .cse56 (or .cse55 .cse7) .cse6 .cse10) .cse4) .cse0 .cse1 .cse9 .cse56 (or (and .cse54 .cse0 .cse1 .cse6 .cse7) .cse55) .cse6 .cse10 (or .cse12 .cse55))) .cse4) .cse0 .cse1 .cse9))) (or .cse14 (let ((.cse17 (or (and .cse23 .cse0 .cse1 .cse22) .cse4 .cse6)) (.cse18 (or (and .cse0 .cse1 (or .cse33 (and .cse47 .cse24))) .cse14))) (let ((.cse26 (and .cse0 .cse1 (or .cse14 (and .cse20 .cse17 .cse23 .cse0 .cse1 .cse22 .cse24 .cse7 .cse18)))) (.cse21 (or .cse53 .cse38 .cse22))) (let ((.cse16 (or .cse14 (let ((.cse45 (or (let ((.cse48 (and .cse52 .cse47 .cse31))) (and (or (and (or .cse48 .cse41) .cse49 .cse31) .cse50) (or (and .cse29 (or (and (or .cse48 .cse33 .cse41) .cse31) .cse27)) .cse51))) .cse27))) (let ((.cse43 (or .cse14 (and .cse0 .cse1 (or (and (or .cse38 (and .cse23 .cse0 (or (and .cse35 .cse0 (or .cse36 .cse37 (and .cse23 .cse0 .cse1 .cse47 .cse24 (or (and (or (and .cse29 (or (and .cse31 (or (and .cse29 .cse45 .cse39 .cse40) .cse41)) .cse27)) .cse28) .cse32) .cse7)) .cse38) .cse1) (and .cse33 .cse7)) .cse1 .cse24)) .cse35) .cse34) .cse18)))) (and (or (and .cse20 .cse21 (let ((.cse44 (or .cse14 (and (or (and .cse46 .cse6 .cse24) .cse4) .cse0 .cse1 .cse6 .cse24 .cse18)))) (let ((.cse42 (or .cse14 (and .cse44 .cse20 .cse17 .cse43 .cse0 .cse1 .cse6 .cse18)))) (or (and (or .cse26 (and .cse25 .cse0 .cse1 .cse6 .cse42)) .cse27) (and .cse0 .cse1 (or .cse14 (and .cse17 .cse43 .cse0 (or (and (or .cse33 (and (or (and .cse29 (or (and .cse32 (or .cse28 (and .cse0 .cse1 (or (and .cse17 .cse43 (or (and .cse20 (or (and .cse44 .cse0 .cse1) .cse22)) .cse4) .cse0 .cse1 .cse18) .cse14) (or (and .cse23 .cse40 .cse22) (and .cse0 .cse1 .cse42)) (or (and .cse43 .cse0 .cse1 (or (and (or .cse14 (and (or .cse4 (and .cse20 .cse21 (or .cse33 (and .cse32 (or .cse28 (and .cse44 .cse29 .cse45 .cse0 .cse1 .cse6)))))) .cse17 .cse43 .cse0 .cse1 .cse18)) .cse0 .cse1) .cse4 (and (or .cse14 (and .cse17 .cse43 (or (and .cse20 .cse21 (or (and (or .cse41 (and .cse29 (or (and .cse32 (or .cse28 (and .cse29 .cse45 .cse23 .cse40 .cse24))) .cse27))) .cse31) .cse33)) .cse4) .cse0 .cse1 .cse18)) .cse0 .cse1 .cse22))) .cse14)))) .cse27)) .cse41) .cse31)) .cse20 .cse21) .cse4) .cse1 .cse18))))))) .cse4) .cse17 .cse43 .cse0 .cse1 .cse18))))) (.cse19 (or (and .cse35 (or (and .cse23 .cse0 .cse1) .cse38)) .cse34))) (let ((.cse15 (or .cse14 (and .cse16 .cse17 (or .cse34 (and .cse35 (or .cse36 .cse37 .cse38 (and (or .cse7 (and .cse32 (or .cse28 (and .cse29 (or (and (or (and .cse39 .cse40) .cse41) .cse31) .cse27))))) .cse23 .cse24)))) .cse0 .cse1 .cse18 .cse19)))) (and .cse15 .cse16 .cse17 .cse0 .cse1 .cse18 .cse19 (or (and .cse20 .cse21 (or (and (or .cse14 (and .cse15 (or (and .cse0 .cse1 .cse22 (or (and .cse20 .cse15 .cse17 .cse23 .cse0 .cse1 .cse24 .cse18 .cse19) .cse14)) (and .cse0 .cse1 (or .cse14 (and .cse20 .cse15 .cse17 .cse0 .cse1 .cse6 .cse24 .cse18 .cse19))) .cse4) .cse0 .cse1)) (or (and (or .cse25 .cse26 .cse7) .cse27) (and (or .cse28 (and .cse29 (or (and .cse30 .cse31) .cse27))) .cse32))) .cse33)) .cse4)))))))) .cse0 .cse1))) (or (and .cse2 (let ((.cse3 (and .cse13 .cse9))) (or .cse3 .cse4 (let ((.cse8 (or .cse11 (and .cse2 .cse0 (or .cse3 .cse12 .cse4) .cse1 .cse9 .cse5 .cse10)))) (and (or (and .cse2 (or .cse3 (and .cse0 .cse1 .cse5 .cse6 .cse7 .cse8) .cse4) .cse0 .cse1 .cse9 .cse5 .cse10) .cse11) .cse0 .cse1 (or .cse11 (and .cse2 .cse0 .cse1 .cse9 .cse5 .cse10)) .cse5 .cse6 .cse7 .cse8)))) .cse0 .cse1 .cse9 .cse5 .cse10) .cse11)))))))))))))";
		final String simplified = null;
		runSimplificationTest(funDecls, formulaAsString, simplified, SimplificationTechnique.POLY_PAC, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	// @Test
	// public void pthread_atomic_gcd_subformula_mod_true() {
	// final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "b"), };
	// final String formulaAsString =
	// "(= (mod (let ((.cse0 (mod b 4294967296))) (mod (mod (+ b .cse0) 4294967296) .cse0)) 4294967296) 0)";
	// final String simplified = null;
	// runSimplificationTest(funDecls, formulaAsString, simplified, SimplificationTechnique.POLY_PAC, mServices,
	// mLogger, mMgdScript, mCsvWriter);
	// }

	@Test
	public void constantFolding01() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x", "y", "z"), };
		final String formulaAsString = "(or (distinct x 1) (and (< y (* x x)) (< z (* x x))))";
		final String simplified = "(or (distinct x 1) (and (< y 1) (< z 1)))";
		runSimplificationTest(funDecls, formulaAsString, simplified, SimplificationTechnique.POLY_PAC, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	// @Test
	// public void bvToIntBadgerExists01() {
	// final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "m", "n"), };
	// final String formulaAsString =
	// "(and (<= (+ m 513 (* (div m 128) 512) (* 768 (div (+ n (- 128)) 256))) 0) (<= (div n 256) 0) (<= (+ 257 m (* 768
	// (div (+ m (* 128 (div (+ n (- 128)) 256))) 256))) 0) (<= (+ m (* 128 (div n 128)) 129 (* (div (+ (- 1) (div (+ n
	// (- 128)) 256)) 2) 256)) 0) (<= (+ m (* 128 (div n 128)) (* 128 (div (+ m (- 128)) 256)) 129 (* 128 (div (+ n (-
	// 128)) 256))) 0) (<= (+ (div (+ m (* 128 (div n 128)) (- 128)) 256) 2 (div (+ n (- 128)) 256)) 0) (<= (+ (* (div n
	// 256) 512) n (* (div m 128) 512)) 255) (<= (+ m (* 256 (div (+ m (* 128 (div n 128)) (- 128)) 256)) (* 256 (div n
	// 256)) 129) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div (+ m (* (div n 256) 128) (- 128)) 384)) 385)
	// 0) (<= (+ (div n 256) (div (+ m (- 256)) 512)) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) 385 (* 256 (div (+ m
	// (* 256 (div (+ n (- 128)) 256))) 512))) 0) (<= (+ m (* 128 (div n 128)) (* 256 (div (+ m (* 128 (div n 128)) (-
	// 128)) 256)) 129) 0) (<= (+ m (* (div n 256) 512) (* (div m 128) 512)) 383) (<= (+ m (* (div n 256) 128) 129 (*
	// 256 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256))) 0) (<= (+ 257 m (* 768 (div (+ m (- 128)) 256)) (* 768 (div
	// n 128))) 0) (<= (+ m (* (div (+ m (- 256) (* 256 (div n 128))) 512) 256) 1) 0) (<= (+ (* (div (+ m (- 256) (* 256
	// (div n 256))) 768) 4) (div n 256) 3) 0) (<= (+ m (* 256 (div n 256)) 385 (* (div (+ m (* 128 (div n 128)) (-
	// 128)) 256) 512)) 0) (<= (+ m (* 768 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) 513 (* 256 (div n 256))) 0)
	// (<= (+ (* 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) m 129 (* 256 (div n 128))) 0) (<= (+ m (* 256 (div n
	// 256)) (* (div (+ (- 2) (div n 256)) 3) 512) 385) 0) (<= (+ 257 n (* (div (+ m (* 256 (div n 256)) (- 128)) 512)
	// 512)) 0) (<= (+ m (* 256 (div (+ m (* (div n 256) 128) (- 128)) 384)) 1) 0) (<= (+ m 1 (* 768 (div (+ n (- 128))
	// 256))) 0) (<= (+ (div (+ m (- 256)) 512) 1) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div n 256)) (*
	// 256 (div m 128)) 129) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) 385 (* 256 (div (+ m (- 384)) 768))) 0) (<= (+
	// m (* (div (+ m (- 256)) 512) 512) 129) 0) (<= (+ m (* 256 (div n 256)) 385 (* (div (+ m (- 256) (* 256 (div n
	// 128))) 512) 512)) 0) (<= (+ m (* 128 (div n 128)) (* 256 (div (+ m (- 256)) 512)) 129) 0) (<= (+ (div n 256) 3 (*
	// (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 4)) 0) (<= (+ m (* 256 (div n 128)) (* 768 (div (+ n (- 128)) 256)))
	// 255) (<= (+ 3 (div (+ n (- 128)) 256) (* 3 (div (+ m (- 384)) 768))) 0) (<= (+ m (* 256 (div n 256)) 129 (* 256
	// (div (+ m (* 256 (div (+ n (- 128)) 256))) 512))) 0) (<= (+ m (* (div (+ m (- 256) (* 256 (div n 256))) 768) 512)
	// 385 (* 256 (div n 128))) 0) (<= (+ m (* (div n 256) 512) (* 256 (div (+ n (- 128)) 256)) (* (div m 128) 512) 1)
	// 0) (<= (+ 2 (div n 128) (* 2 (div (+ n (- 128)) 256)) (* 2 (div (+ m 128) 256))) 0) (<= (+ m (* (div (+ m (- 256)
	// (* 256 (div n 128))) 512) 256) (* (div n 256) 128) 129) 0) (<= (+ m (* (div (+ m (- 128)) 256) 512) 129) 0) (<=
	// (+ (div (+ m (* 256 (div n 256)) (- 128)) 512) 1) 0) (<= (+ m (* 256 (div (+ m (- 128)) 256)) (* 256 (div (+ n (-
	// 128)) 256)) (* 256 (div n 256)) 385) 0) (<= (+ 2 (div n 256) (div (+ n (- 128)) 256) (div (+ m (- 128)) 256)) 0)
	// (<= (+ 2 (div (+ n (- 128)) 256) (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 2)) 0) (<= (+ m (* 128 (div n
	// 128)) (* 256 (div (+ n (- 128)) 256)) 129 (* 256 (div (+ m 128) 256))) 0) (<= (+ 2 (div n 128) (* 2 (div (+ m (-
	// 512)) 1024))) 0) (<= (+ (* 256 (div (+ m (- 128)) 256)) n 129 (* 256 (div n 128))) 0) (<= (+ m (* (div n 256)
	// 384) (* 256 (div (+ m (- 128)) 256)) 129) 0) (<= (+ m (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 512) 385 (*
	// 256 (div n 128))) 0) (<= (+ (div n 256) (div (+ (- 2) (div n 256)) 3)) 0) (<= (+ (div (+ m (* 256 (div (+ n (-
	// 128)) 256))) 512) 1) 0) (<= (+ 2 (* 2 (div (+ m (- 128)) 256)) (div (+ n (- 128)) 256) (* 2 (div n 256))) 0) (<=
	// (+ 2 (div n 256) (* 2 (div n 128)) (* 2 (div (+ m (- 128)) 256))) 0) (<= (+ 2 (div n 256) (* 2 (div (+ m (- 256))
	// 512))) 0) (<= (+ (* 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) m (* 256 (div (+ n (- 128)) 256)) 385) 0)
	// (<= (+ (* (div n 256) 512) n) 255) (<= (+ (div n 256) 3 (* (div (+ (- 2) (div n 256)) 3) 4)) 0) (<= (+ m (* 256
	// (div n 128)) (* (div (+ n (- 128)) 256) 512)) 127) (<= (+ m 129 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 128)
	// (* 128 (div (+ n (- 128)) 256))) 0) (<= (+ m (* 128 (div n 128)) (* 256 (div n 256))) 127) (<= (+ m 513 (* 256
	// (div n 128)) (* 768 (div (+ m (- 256) (* 256 (div n 256))) 768))) 0) (<= (+ (div n 256) 3 (* (div (+ m (* 256
	// (div (+ n (- 128)) 256))) 512) 4)) 0) (<= (+ m (* 128 (div n 128)) (* 256 (div (+ n (- 128)) 256))) 127) (<= (+ m
	// (* (div n 256) 128) (* 128 (div (+ n (- 128)) 256)) 1) 0) (<= (+ m (* (div n 256) 384) (* 256 (div m 128))) 127)
	// (<= (+ (* 256 (div (+ n (- 128)) 256)) n) 127) (<= (+ m (* 256 (div n 256)) (* (div (+ m 128) 256) 512) 385 (*
	// (div (+ n (- 128)) 256) 512)) 0) (<= (+ m (* (div n 256) 512) (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (-
	// 128)) 256) 512)) 0) (<= (+ m (* 128 (div n 128)) 129 (* 256 (div (+ m (* 256 (div n 256)) (- 128)) 512))) 0) (<=
	// (+ (* 256 (div (+ (- 2) (div n 256)) 3)) m (* 128 (div n 128)) 129) 0) (<= (+ m (* 128 (div n 128)) (* 256 (div
	// (+ n (- 128)) 256)) (* 256 (div m 128)) 129) 0) (<= (+ (* 2 (div (+ m (- 384)) 768)) 2 (div (+ n (- 128)) 256))
	// 0) (<= (+ m (* 256 (div (+ m (* 128 (div n 128)) (- 128)) 256)) 1) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256))
	// 385 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 256)) 0) (<= (+ (* 2 (div (+ (- 2) (div n 256)) 3)) 2 (div n
	// 256)) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) 385 (* 256 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256))) 0)
	// (<= (+ 3 (div n 128) (* (div (+ (- 2) (div n 256)) 3) 4)) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) 385 (* 256
	// (div (+ m (- 512)) 1024))) 0) (<= (+ 257 m (* 768 (div (+ m (- 128)) 256)) (* 768 (div n 256))) 0) (<= (+ m (*
	// 256 (div n 256)) (* (div m 128) 512) 385 (* (div (+ n (- 128)) 256) 512)) 0) (<= (+ (div n 256) 3 (* 4 (div (+ m
	// (- 384)) 768))) 0) (<= (+ 2 (div (+ m (- 512)) 1024) (div (+ n (- 128)) 256)) 0) (<= (+ (* 2 (div (+ m (* 256
	// (div (+ n (- 128)) 256))) 512)) 2 (div n 256)) 0) (<= (+ m (* (div n 256) 512) (* 256 (div (+ n (- 128)) 256)) 1)
	// 0) (<= (+ 257 m (* 768 (div (+ m 128) 256)) (* 768 (div (+ n (- 128)) 256))) 0) (<= (+ m (* 256 (div (+ n (-
	// 128)) 256)) 513 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 512)) 0) (<= (+ 257 n (* (div (+ m (* 128 (div n
	// 128)) (- 128)) 256) 512)) 0) (<= (+ m (* (div n 256) 128) 129 (* 256 (div (+ m (* (div n 256) 128) (- 128))
	// 384))) 0) (<= (+ 257 (* (div (+ m (- 128)) 256) 512) n (* (div n 128) 512)) 0) (<= (+ m (* 256 (div (+ n (- 128))
	// 256)) 513 (* (div (+ m (- 256) (* 256 (div n 128))) 512) 512)) 0) (<= (+ (div (+ m (- 128)) 256) (* 2 (div n
	// 256))) 0) (<= (+ (div (+ (- 1) (div (+ n (- 128)) 256)) 2) (div n 256)) 0) (<= (+ m (* 256 (div (+ n (- 128))
	// 256)) (* (div (+ m (- 256)) 512) 512) 513) 0) (<= (+ 3 (* 3 (div (+ m (* 256 (div n 256)) (- 128)) 512)) (div (+
	// n (- 128)) 256)) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ (- 2) (div n 256)) 3) 512)) 0) (<= (+
	// (* 256 (div (+ n (- 128)) 256)) (* 256 (div m 128)) n 129) 0) (<= (+ m (* 768 (div (+ m (- 512)) 1024)) 513 (*
	// 256 (div n 128))) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) 129 (* 256 (div (+ m 128) 256)) (* 256 (div n
	// 128))) 0) (<= (+ (div n 256) (* 2 (div (+ n (- 128)) 256))) 0) (<= (+ m (* (div (+ m 128) 256) 512) 385 (* 256
	// (div n 128)) (* (div (+ n (- 128)) 256) 512)) 0) (<= (+ (* 256 (div (+ m (- 128)) 256)) (* 256 (div n 256)) n
	// 129) 0) (<= (+ m (* 256 (div (+ m (* 128 (div n 128)) (- 128)) 256)) (* (div n 256) 128) 129) 0) (<= (+ (div n
	// 256) (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) 0) (<= (+ m 129 (* (div (+ m (* 256 (div (+ n (- 128))
	// 256))) 512) 512)) 0) (<= (+ m (* (div m 128) 512) (* 768 (div n 256))) 127) (<= (+ 2 (div n 256) (* (div (+ (- 1)
	// (div (+ n (- 128)) 256)) 2) 2)) 0) (<= (+ (div (+ m (- 256) (* 256 (div n 128))) 512) 2 (div (+ n (- 128)) 256))
	// 0) (<= (+ m (* (div n 256) 128) (* 128 (div m 128)) (* 128 (div (+ n (- 128)) 256)) 1) 0) (<= (+ m (* 256 (div (+
	// m (* 128 (div (+ n (- 128)) 256))) 256)) 1) 0) (<= (+ m (* 256 (div (+ m (- 384)) 768)) 1) 0) (<= (+ m (* 256
	// (div n 256))) 127) (<= (+ n 129 (* 256 (div (+ m (* (div n 256) 128) (- 128)) 384))) 0) (<= (+ 3 (* 3 (div (+ (-
	// 2) (div n 256)) 3)) (div (+ n (- 128)) 256)) 0) (<= (+ m (* (div (+ m (- 128)) 256) 512) 385 (* 256 (div n 128)))
	// 0) (<= (+ m 513 (* 256 (div n 256)) (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 768)) 0) (<= (+ (* 256 (div (+
	// (- 2) (div n 256)) 3)) m 1) 0) (<= (+ (* 3 (div (+ n (- 128)) 256)) 2 (* 2 (div (+ m 128) 256))) 0) (<= (+ n 129
	// (* 256 (div (+ m (- 512)) 1024))) 0) (<= (+ (* 2 (div (+ (- 2) (div n 256)) 3)) 2 (div (+ n (- 128)) 256)) 0) (<=
	// (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div (+ m 128) 256)) 1) 0) (<= (+ 3 (* 3 (div (+ m (- 256)) 512))
	// (div (+ n (- 128)) 256)) 0) (<= (+ m (* 256 (div (+ m (- 128)) 256)) (* (div n 256) 128) 129 (* 256 (div n 128)))
	// 0) (<= (+ (* 4 (div m 128)) (div n 256) 3 (* (div (+ n (- 128)) 256) 4)) 0) (<= (+ (* 2 (div (+ m (* 256 (div n
	// 256)) (- 128)) 512)) 2 (div n 128)) 0) (<= (+ 257 m (* (div (+ m (- 256) (* 256 (div n 128))) 512) 768)) 0) (<=
	// (+ 257 (* (div (+ m (- 128)) 256) 512) n) 0) (<= (+ m (* (div n 256) 384)) 127) (<= (+ (div (+ m (* 128 (div n
	// 128)) (- 128)) 256) 1) 0) (<= (+ (* (div (+ m (* (div n 256) 128) (- 128)) 384) 512) m 385 (* 256 (div n 128)))
	// 0) (<= (+ (div (+ n (- 128)) 256) (div m 128) 1) 0) (<= (+ m 129 (* (div (+ m 128) 256) 512) (* (div (+ n (-
	// 128)) 256) 512)) 0) (<= (+ (* (div (+ m 128) 256) 4) (div n 256) 3 (* (div (+ n (- 128)) 256) 4)) 0) (<= (+ (*
	// 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) n 129) 0) (<= (+ 3 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2)
	// 4) (div n 128)) 0) (<= (+ 2 (div (+ m (- 256)) 512) (div (+ n (- 128)) 256)) 0) (<= (+ (div (+ m (- 256) (* 256
	// (div n 128))) 512) (div n 256)) 0) (<= (+ (* 4 (div m 128)) 3 (div n 128) (* (div (+ n (- 128)) 256) 4)) 0) (<=
	// (+ (* 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) m 1) 0) (<= (+ 3 (div n 128) (* (div (+ m (- 128)) 256)
	// 4)) 0) (<= (+ (* 2 (div (+ m (- 384)) 768)) 2 (div n 256)) 0) (<= (+ m (* 256 (div (+ m (* 256 (div n 256)) (-
	// 128)) 512)) 1) 0) (<= (+ m 513 (* 256 (div n 256)) (* 768 (div m 128)) (* 768 (div (+ n (- 128)) 256))) 0) (<= (+
	// 3 (div (+ n (- 128)) 256) (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 3)) 0) (<= (+ (div n 256) 3 (* (div (+ m
	// (- 128)) 256) 4)) 0) (<= (+ m (* 256 (div (+ m (- 128)) 256)) (* (div n 256) 128) 129) 0) (<= (+ m (* (div n 256)
	// 512) (* 256 (div n 128))) 127) (<= (+ m (* 128 (div n 128)) 129 (* 256 (div (+ m (* (div n 256) 128) (- 128))
	// 384))) 0) (<= (+ 2 (div n 128) (div (+ n (- 128)) 256) (div (+ m (- 128)) 256)) 0) (<= (+ m (* (div n 256) 512))
	// 127) (<= (+ m 513 (* 768 (div (+ m (- 384)) 768)) (* 256 (div n 128))) 0) (<= (+ m (* 256 (div (+ m (* 128 (div n
	// 128)) (- 128)) 256)) 129 (* 256 (div n 128))) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) 385 (* 256 (div (+ m (*
	// 256 (div n 256)) (- 128)) 512))) 0) (<= (+ (div n 256) (div (+ m (* (div n 256) 128) (- 128)) 384)) 0) (<= (+ 2
	// (div n 256) (* 2 (div (+ m (- 128)) 256))) 0) (<= (+ m (* (div (+ (- 2) (div n 256)) 3) 512) 129) 0) (<= (+ (* 2
	// (div (+ m (* (div n 256) 128) (- 128)) 384)) 2 (div n 256)) 0) (<= (+ 2 (div (+ m 128) 256) (* 2 (div (+ n (-
	// 128)) 256))) 0) (<= (+ (div (+ m 128) 256) (div (+ n (- 128)) 256) 1) 0) (<= (+ m (* 256 (div n 256)) 129 (* 256
	// (div (+ m (- 384)) 768))) 0) (<= (+ m (* 256 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)) 1) 0) (<= (+ m 513
	// (* 256 (div n 256)) (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 768)) 0) (<= (+ (div (+ (- 1) (div (+ n (- 128))
	// 256)) 2) 2 (div (+ n (- 128)) 256)) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div m 128)) 1) 0) (<= (+
	// (* 256 (div (+ m (- 256)) 512)) n 129) 0) (<= (+ (div (+ (- 2) (div n 256)) 3) 1) 0) (<= (+ m (* (div (+ m (-
	// 384)) 768) 512) (* 256 (div n 256)) 385) 0) (<= (+ 2 (div n 256) (* 2 (div (+ m (- 256) (* 256 (div n 256)))
	// 768))) 0) (<= (+ (div (+ m (* (div n 256) 128) (- 128)) 384) 1) 0) (<= (+ 2 (* 2 (div n 128)) (* 2 (div (+ m (-
	// 128)) 256)) (div (+ n (- 128)) 256)) 0) (<= (+ 2 (div (+ n (- 128)) 256) (div (+ m (- 128)) 256)) 0) (<= (+ m 513
	// (* 256 (div n 128)) (* 768 (div (+ m (* 256 (div n 256)) (- 128)) 512))) 0) (<= (+ m (* 128 (div n 128)) 129 (*
	// 256 (div (+ m (- 384)) 768))) 0) (<= (+ m (* (div (+ m (* 128 (div (+ n (- 128)) 256))) 256) 512) 385 (* 256 (div
	// n 128))) 0) (<= (+ (* (div (+ m (- 512)) 1024) 4) (div n 256) 3) 0) (<= (+ m (* 768 (div (+ m (- 128)) 256)) 513
	// (* 768 (div n 256)) (* 256 (div n 128))) 0) (<= (+ (* (div (+ m (* (div n 256) 128) (- 128)) 384) 512) 257 n) 0)
	// (<= (+ m (* 256 (div n 256)) (* 256 (div (+ m (- 256)) 512)) 129) 0) (<= (+ m 513 (* 768 (div m 128)) (* 256 (div
	// n 128)) (* 768 (div (+ n (- 128)) 256))) 0) (<= (+ m 129 (* (div (+ n (- 128)) 256) 512)) 0) (<= (+ m (* 768 (div
	// (+ m (- 128)) 256)) 513 (* 256 (div n 256)) (* 768 (div n 128))) 0) (<= (+ m 385 (* 256 (div n 128)) (* (div (+ m
	// (- 256) (* 256 (div n 128))) 512) 512)) 0) (<= (+ m (* 256 (div (+ m (- 128)) 256)) 1) 0) (<= (+ (div (+ m (-
	// 512)) 1024) 1) 0) (<= (+ 3 (* 3 (div m 128)) (* (div (+ n (- 128)) 256) 4)) 0) (<= (+ 257 m (* 768 (div (+ m (-
	// 256) (* 256 (div n 256))) 768))) 0) (<= (+ m (* (div (+ m (- 256) (* 256 (div n 128))) 512) 256) (* 256 (div n
	// 256)) 129) 0) (<= (+ m (* 128 (div (+ m (- 128)) 256)) (* (div n 256) 128) 129 (* 128 (div (+ n (- 128)) 256)))
	// 0) (<= (+ 2 (div n 128) (* 2 (div (+ m (- 128)) 256))) 0) (<= (+ m (* (div n 256) 512) (* (div (+ m (- 128)) 256)
	// 512) 385 (* 256 (div n 128))) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div n 256)) 129 (* 256 (div (+
	// m 128) 256))) 0) (<= (+ 3 (* (div n 256) 3) (* 3 (div (+ m (- 128)) 256)) (div (+ n (- 128)) 256)) 0) (<= (+ (* 2
	// (div (+ (- 2) (div n 256)) 3)) 2 (div n 128)) 0) (<= (+ 2 (div n 256) (* (div (+ m (* 128 (div n 128)) (- 128))
	// 256) 2)) 0) (<= (+ (* (div n 256) 4) (div n 128)) 1) (<= (+ 257 (* (div (+ m (- 256) (* 256 (div n 256))) 768)
	// 512) n) 0) (<= (+ 257 n (* (div (+ m 128) 256) 512) (* (div (+ n (- 128)) 256) 512)) 0) (<= (+ (* (div (+ m (*
	// (div n 256) 128) (- 128)) 384) 512) m (* 256 (div (+ n (- 128)) 256)) 513) 0) (<= (+ 257 m (* (div (+ (- 1) (div
	// (+ n (- 128)) 256)) 2) 768)) 0) (<= (+ 2 (div (+ m (* (div n 256) 128) (- 128)) 384) (div (+ n (- 128)) 256)) 0)
	// (<= (+ m 129 (* 256 (div (+ m (- 384)) 768)) (* 256 (div n 128))) 0) (<= (+ m (* (div n 256) 128) 129 (* 256 (div
	// (+ m (- 384)) 768))) 0) (<= (+ (* (div (+ m (- 512)) 1024) 4) 3 (div n 128)) 0) (<= (+ (* 2 (div (+ m (* (div n
	// 256) 128) (- 128)) 384)) 2 (div n 128)) 0) (<= (+ m 129 (* 256 (div n 128)) (* 256 (div (+ m (* 256 (div (+ n (-
	// 128)) 256))) 512))) 0) (<= (+ (div n 256) 3 (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 4)) 0) (<= (+ (* 256
	// (div (+ (- 2) (div n 256)) 3)) n 129) 0) (<= (+ m (* (div (+ m (- 128)) 256) 512) 129 (* (div n 128) 512)) 0) (<=
	// (+ m (* 256 (div n 256)) (* (div (+ n (- 128)) 256) 512)) 127) (<= (+ m (* (div (+ (- 2) (div n 256)) 3) 512) 385
	// (* 256 (div n 128))) 0) (<= (+ m (* 256 (div (+ m (- 128)) 256)) (* 256 (div n 256)) 129) 0) (<= (+ 2 (div n 128)
	// (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 2)) 0) (<= (+ m 129 (* (div m 128) 512) (* (div (+ n (- 128)) 256)
	// 512)) 0) (<= (+ m (* (div (+ m (- 128)) 256) 512) (* 768 (div n 256)) 385) 0) (<= (+ 257 (* (div (+ m (* 128 (div
	// (+ n (- 128)) 256))) 256) 512) n) 0) (<= (+ (* 2 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)) 2 (div n 128))
	// 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) (* (div (+ m (- 256) (* 256 (div n 128))) 512) 256) 385) 0) (<= (+
	// 257 m (* 768 (div (+ m (* 256 (div n 256)) (- 128)) 512))) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) (* (div (+
	// m 128) 256) 128) 129) 0) (<= (+ n 129 (* 256 (div (+ m (- 384)) 768))) 0) (<= (+ 257 m (* 768 (div (+ m (- 384))
	// 768))) 0) (<= (+ (div n 128) (* 2 (div (+ n (- 128)) 256))) 0) (<= (+ m (* 256 (div (+ m (- 512)) 1024)) 1) 0)
	// (<= (+ 2 (* 2 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) (div (+ n (- 128)) 256)) 0) (<= (+ 2 (* (div n
	// 256) 3) (* 2 (div (+ m (- 128)) 256))) 0) (<= (+ (* 3 (div n 128)) 2 (* 2 (div (+ m (- 128)) 256))) 0) (<= (+ 257
	// m (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 768)) 0) (<= (+ 257 (* (div (+ m (- 384)) 768) 512) n) 0) (<= (+
	// m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (- 128)) 256) 512)) 0) (<= (+ (* 2 (div (+ m (* 256 (div n
	// 256)) (- 128)) 512)) 2 (div n 256)) 0) (<= (+ 2 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) (div (+ n (-
	// 128)) 256)) 0) (<= (+ (* (div (+ m (- 256) (* 256 (div n 128))) 512) 2) 2 (div n 256)) 0) (<= (+ (* 2 (div m
	// 128)) (* 3 (div (+ n (- 128)) 256)) 2) 0) (<= (+ m (* 128 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)) 129 (*
	// 128 (div (+ n (- 128)) 256))) 0) (<= (+ 2 (div (+ m (* 256 (div n 256)) (- 128)) 512) (div (+ n (- 128)) 256)) 0)
	// (<= (+ m (* 256 (div (+ m (- 128)) 256)) 129 (* (div n 128) 512)) 0) (<= (+ m (* 256 (div n 256)) (* (div (+ m (*
	// 256 (div n 256)) (- 128)) 512) 512) 385) 0) (<= (+ (div n 256) (div (+ m (- 512)) 1024)) 0) (<= (+ m (* 256 (div
	// (+ n (- 128)) 256)) (* (div n 256) 128)) 127) (<= (+ (* 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) m (*
	// (div n 256) 128) 129) 0) (<= (+ m 513 (* 256 (div n 256)) (* 768 (div (+ m 128) 256)) (* 768 (div (+ n (- 128))
	// 256))) 0) (<= (+ (* 2 (div m 128)) (div n 128) (* 2 (div n 256))) 0) (<= (+ m 129 (* (div (+ m (- 512)) 1024)
	// 512)) 0) (<= (+ (* (div (+ m (* (div n 256) 128) (- 128)) 384) 512) m 129) 0) (<= (+ m 513 (* 768 (div (+ m (*
	// 256 (div (+ n (- 128)) 256))) 512)) (* 256 (div n 128))) 0) (<= (+ (div n 128) (div (+ m (- 128)) 256) 1) 0) (<=
	// (+ m (* (div (+ m (- 256) (* 256 (div n 128))) 512) 128) 129 (* 128 (div (+ n (- 128)) 256))) 0) (<= (+ (div (+ m
	// (* 128 (div n 128)) (- 128)) 256) (div n 256)) 0) (<= (+ m 129 (* 256 (div (+ m (* 256 (div n 256)) (- 128))
	// 512)) (* 256 (div n 128))) 0) (<= (+ (div (+ m (- 384)) 768) 1) 0) (<= (+ 257 m (* 768 (div (+ m (- 256)) 512)))
	// 0) (<= (+ m (* (div (+ m (- 256)) 512) 128) 129 (* 128 (div (+ n (- 128)) 256))) 0) (<= (+ m (* 768 (div m 128))
	// (* 768 (div n 256))) 511) (<= (+ n 129 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 256)) 0) (<= (+ m 129 (* 256
	// (div (+ m (* (div n 256) 128) (- 128)) 384)) (* 256 (div n 128))) 0) (<= (+ 2 (div n 128) (* (div (+ (- 1) (div
	// (+ n (- 128)) 256)) 2) 2)) 0) (<= (+ 257 n (* (div m 128) 512) (* (div (+ n (- 128)) 256) 512)) 0) (<= (+ m 129
	// (* 256 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) (* 256 (div n 128))) 0) (<= (+ 2 (div (+ (- 2) (div n
	// 256)) 3) (div (+ n (- 128)) 256)) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div n 128))) 127) (<= (+ m
	// (* (div n 256) 512) (* 256 (div (+ m (- 128)) 256)) 129) 0) (<= (+ m 129 (* (div (+ m (* 128 (div n 128)) (-
	// 128)) 256) 128) (* 128 (div (+ n (- 128)) 256))) 0) (<= (+ m (* (div n 256) 128) 129 (* 256 (div (+ m (* 256 (div
	// (+ n (- 128)) 256))) 512))) 0) (<= (+ m 513 (* 256 (div n 128)) (* 768 (div (+ m 128) 256)) (* 768 (div (+ n (-
	// 128)) 256))) 0) (<= (+ m (* (div n 256) 1024) (* 768 (div m 128))) 255) (<= (+ 257 m (* 768 (div (+ (- 2) (div n
	// 256)) 3))) 0) (<= (+ (div n 256) (div (+ m (- 384)) 768)) 0) (<= (+ m (* (div n 256) 128) 129 (* (div (+ (- 1)
	// (div (+ n (- 128)) 256)) 2) 256)) 0) (<= (+ (* (div n 256) 4) (* 4 (div m 128)) (div n 128)) 1) (<= (+ 2 (* 2
	// (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) (div n 128)) 0) (<= (+ (div n 256) (div m 128)) 0) (<= (+ 3 (*
	// (div (+ m (- 256) (* 256 (div n 128))) 512) 3) (div (+ n (- 128)) 256)) 0) (<= (+ 2 (div n 256) (* 2 (div (+ n (-
	// 128)) 256)) (* 2 (div (+ m 128) 256))) 0) (<= (+ m (* 128 (div n 128)) (* (div (+ m (- 256) (* 256 (div n 128)))
	// 512) 256) 129) 0) (<= (+ (* (div (+ m (- 256) (* 256 (div n 128))) 512) 2) 2 (div (+ n (- 128)) 256)) 0) (<= (+ m
	// (* 256 (div n 256)) (* (div (+ m (* 128 (div (+ n (- 128)) 256))) 256) 512) 385) 0) (<= (+ (div (+ m (- 128))
	// 256) 1) 0) (<= (+ 2 (div n 128) (* 2 (div (+ m (- 128)) 256)) (* 2 (div n 256))) 0) (<= (+ m (* (div (+ m (- 256)
	// (* 256 (div n 256))) 768) 512) (* 256 (div n 256)) 385) 0) (<= (+ n 129 (* 256 (div (+ m (* 128 (div (+ n (-
	// 128)) 256))) 256))) 0) (<= (+ (* 256 (div (+ (- 2) (div n 256)) 3)) m (* 256 (div (+ n (- 128)) 256)) 385) 0) (<=
	// (+ m (* 256 (div n 256)) 129 (* 256 (div (+ m (* (div n 256) 128) (- 128)) 384))) 0) (<= (+ m 513 (* 256 (div n
	// 256)) (* 768 (div (+ m (* 256 (div n 256)) (- 128)) 512))) 0) (<= (+ m 513 (* (div (+ m 128) 256) 512) (* 768
	// (div (+ n (- 128)) 256))) 0) (<= (+ 2 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 2) (div (+ n (- 128)) 256)) 0)
	// (<= (+ 257 n (* (div (+ m (- 512)) 1024) 512)) 0) (<= (+ (* 3 (div (+ m (- 512)) 1024)) 3 (div (+ n (- 128))
	// 256)) 0) (<= (+ 3 (div (+ n (- 128)) 256) (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 3)) 0) (<= (+ 257 n (*
	// (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 512)) 0) (<= (+ (* 2 (div m 128)) 2 (div n 256) (* 2 (div (+ n (-
	// 128)) 256))) 0) (<= (+ (* 2 (div m 128)) (div (+ n (- 128)) 256) (* 2 (div n 256))) 0) (<= (+ m 129 (* 128 (div
	// (+ m (- 512)) 1024)) (* 128 (div (+ n (- 128)) 256))) 0) (<= (+ (div n 256) (div (+ m (* 256 (div (+ n (- 128))
	// 256))) 512)) 0) (<= (+ m (* 256 (div n 256)) 385 (* (div (+ m (- 512)) 1024) 512)) 0) (<= (+ (* 256 (div (+ m (-
	// 128)) 256)) n 129) 0) (<= (+ m 129 (* 128 (div (+ m (* 256 (div n 256)) (- 128)) 512)) (* 128 (div (+ n (- 128))
	// 256))) 0) (<= (+ (* (div n 256) 4) 3 (div n 128) (* (div (+ m (- 128)) 256) 4)) 0) (<= (+ (div n 256) 3 (* 4 (div
	// (+ m (* 128 (div (+ n (- 128)) 256))) 256))) 0) (<= (+ 3 (* 3 (div (+ m 128) 256)) (* (div (+ n (- 128)) 256) 4))
	// 0) (<= (+ m (* 768 (div (+ m (- 512)) 1024)) 513 (* 256 (div n 256))) 0) (<= (+ (* 3 (div (+ m (- 256) (* 256
	// (div n 256))) 768)) 3 (div (+ n (- 128)) 256)) 0) (<= (+ n 129 (* 256 (div (+ m (* 256 (div (+ n (- 128)) 256)))
	// 512))) 0) (<= (+ m (* 128 (div n 128)) 129 (* 256 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512))) 0) (<= (+ m
	// (* 256 (div (+ n (- 128)) 256)) (* 256 (div m 128)) 129 (* 256 (div n 128))) 0) (<= (+ n 129 (* 256 (div (+ m (*
	// 256 (div n 256)) (- 128)) 512))) 0) (<= (+ 3 (div n 128) (* (div (+ m (* (div n 256) 128) (- 128)) 384) 4)) 0)
	// (<= (+ m (* 768 (div (+ m (- 128)) 256)) 513 (* 256 (div n 128))) 0) (<= (+ m (* (div n 256) 128) 129 (* 256 (div
	// (+ m (- 512)) 1024))) 0) (<= (+ m 129 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 256) (* 256 (div n 128))) 0)
	// (<= (+ m 385 (* 256 (div (+ m 128) 256)) (* (div (+ n (- 128)) 256) 512)) 0) (<= (+ 2 (div (+ n (- 128)) 256)
	// (div (+ m (- 384)) 768)) 0) (<= (+ 257 (* (div (+ (- 2) (div n 256)) 3) 512) n) 0) (<= (+ m (* 768 (div (+ m (*
	// 128 (div (+ n (- 128)) 256))) 256)) 513 (* 256 (div n 128))) 0) (<= (+ m (* (div (+ m (- 384)) 768) 512) 129) 0)
	// (<= (+ 3 (* 3 (div (+ m (- 128)) 256)) (div (+ n (- 128)) 256)) 0) (<= (+ m (* 256 (div (+ m (- 128)) 256)) (*
	// (div n 128) 384) 129) 0) (<= (+ 257 m (* 768 (div m 128)) (* 768 (div (+ n (- 128)) 256))) 0) (<= (+ (* (div (+ m
	// 128) 256) 4) 3 (div n 128) (* (div (+ n (- 128)) 256) 4)) 0) (<= (+ (div n 256) (div (+ m (* 256 (div n 256)) (-
	// 128)) 512)) 0) (<= (+ 3 (* 4 (div (+ m (- 384)) 768)) (div n 128)) 0) (<= (+ m (* 128 (div n 128)) 129 (* 256
	// (div (+ m (- 512)) 1024))) 0) (<= (+ m (* 256 (div (+ m (- 128)) 256)) 129 (* 256 (div n 128))) 0) (<= (+ 3 (*
	// (div (+ m (* 256 (div n 256)) (- 128)) 512) 4) (div n 128)) 0) (<= (+ 2 (div (+ n (- 128)) 256) (div (+ m (* 128
	// (div (+ n (- 128)) 256))) 256)) 0) (<= (+ 2 (div (+ n (- 128)) 256) (* 2 (div (+ m (- 256) (* 256 (div n 256)))
	// 768))) 0) (<= (+ m 513 (* 256 (div n 256)) (* 768 (div (+ m (- 256) (* 256 (div n 256))) 768))) 0) (<= (+ (div (+
	// m (* 128 (div (+ n (- 128)) 256))) 256) 1) 0) (<= (+ (* 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) m (* 128
	// (div n 128)) 129) 0) (<= (+ m (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 512) (* 256 (div n 256)) 385) 0) (<=
	// (+ (div n 256) (* (div (+ n (- 128)) 256) 4)) 1) (<= (+ (* (div (+ m (- 256) (* 256 (div n 128))) 512) 2) 2 (div
	// n 128)) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div n 256)) 129) 0) (<= (+ m (* (div (+ m (- 384))
	// 768) 512) 385 (* 256 (div n 128))) 0) (<= (+ m (* (div n 256) 128) (* 256 (div (+ m (- 256)) 512)) 129) 0) (<= (+
	// m (* 256 (div n 256)) 129 (* 256 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256))) 0) (<= (+ m 129 (* (div (+ (-
	// 2) (div n 256)) 3) 128) (* 128 (div (+ n (- 128)) 256))) 0) (<= (+ m (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2)
	// 256) 1) 0) (<= (+ n (* (div (+ n (- 128)) 256) 512)) 255) (<= (+ 2 (div n 128) (* 2 (div (+ m (- 256) (* 256 (div
	// n 256))) 768))) 0) (<= (+ m 385 (* 256 (div n 128)) (* (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 512)) 0)
	// (<= (+ 2 (* 2 (div (+ m (- 128)) 256)) (div (+ n (- 128)) 256)) 0) (<= (+ (div (+ (- 1) (div (+ n (- 128)) 256))
	// 2) 1) 0) (<= (+ m 129 (* 256 (div (+ m (- 512)) 1024)) (* 256 (div n 128))) 0) (<= (+ (div n 256) (div (+ m 128)
	// 256) (div (+ n (- 128)) 256)) 0) (<= (+ (div (+ m (- 256) (* 256 (div n 128))) 512) 1) 0) (<= (+ m (* (div (+ m
	// (- 256) (* 256 (div n 256))) 768) 128) 129 (* 128 (div (+ n (- 128)) 256))) 0) (<= (+ (* 2 (div n 256)) (div m
	// 128)) 1) (<= (+ 2 (div n 128) (* 2 (div (+ m (- 256)) 512))) 0) (<= (+ 2 (* 2 (div (+ m (- 256)) 512)) (div (+ n
	// (- 128)) 256)) 0) (<= (+ 257 m (* 768 (div (+ m (- 512)) 1024))) 0) (<= (+ 2 (div n 256) (* 2 (div (+ m (* 128
	// (div (+ n (- 128)) 256))) 256))) 0) (<= (+ m (* 768 (div (+ m (* (div n 256) 128) (- 128)) 384)) 513 (* 256 (div
	// n 256))) 0) (<= (+ (div n 256) (div (+ m (- 256) (* 256 (div n 256))) 768)) 0) (<= (+ (div (+ m (- 256) (* 256
	// (div n 256))) 768) 1) 0) (<= (+ m 513 (* 768 (div (+ m (- 256)) 512)) (* 256 (div n 128))) 0) (<= (+ 257 m (* 768
	// (div (+ m (* (div n 256) 128) (- 128)) 384))) 0) (<= (+ m (* 256 (div n 256)) 129 (* 256 (div (+ m (- 512))
	// 1024))) 0) (<= (+ (* (div n 256) 3) (* 3 (div m 128)) (div (+ n (- 128)) 256)) 0) (<= (+ m 513 (* 256 (div n
	// 256)) (* (div (+ m (- 256) (* 256 (div n 128))) 512) 768)) 0) (<= (+ m 385 (* (div (+ m (* 128 (div n 128)) (-
	// 128)) 256) 512) (* 256 (div n 128))) 0) (<= (+ m (* 256 (div (+ m (- 256)) 512)) 129 (* 256 (div n 128))) 0) (<=
	// (+ m (* (div (+ m (- 256) (* 256 (div n 128))) 512) 256) 129 (* 256 (div n 128))) 0) (<= (+ (div n 128) (* 2 (div
	// n 256))) 0) (<= (+ m (* (div (+ m (- 256) (* 256 (div n 256))) 768) 512) (* 256 (div (+ n (- 128)) 256)) 513) 0)
	// (<= (+ (* 256 (div n 256)) n) 127) (<= (+ m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (* 128 (div n 128))
	// (- 128)) 256) 512)) 0) (<= (+ m (* (div n 256) 1024)) 255) (<= (+ m (* (div m 128) 512) 385 (* 256 (div n 128))
	// (* (div (+ n (- 128)) 256) 512)) 0) (<= (+ (* 2 (div m 128)) 2 (div n 128) (* 2 (div (+ n (- 128)) 256))) 0) (<=
	// (+ 3 (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 4) (div n 128)) 0) (<= (+ (* 2 (div (+ m (* (div n 256) 128)
	// (- 128)) 384)) 2 (div (+ n (- 128)) 256)) 0) (<= (+ m (* 256 (div n 256)) (* 768 (div (+ n (- 128)) 256))) 255)
	// (<= (+ (* (div (+ m (- 256) (* 256 (div n 128))) 512) 256) n 129) 0) (<= (+ m (* (div (+ m (- 256) (* 256 (div n
	// 256))) 768) 512) 129) 0) (<= (+ (div n 256) 3 (* (div (+ m (- 256) (* 256 (div n 128))) 512) 4)) 0) (<= (+ (div n
	// 256) (div n 128) (div (+ m (- 128)) 256)) 0) (<= (+ 2 (div (+ n (- 128)) 256) (* 2 (div (+ m (- 512)) 1024))) 0)
	// (<= (+ m (* 128 (div n 128)) (* 256 (div (+ m (- 128)) 256)) (* 256 (div n 256)) 129) 0) (<= (+ 257 (* (div (+ (-
	// 1) (div (+ n (- 128)) 256)) 2) 512) n) 0) (<= (+ (div n 256) 3 (* (div (+ m (* 256 (div n 256)) (- 128)) 512) 4))
	// 0) (<= (+ m (* 256 (div n 256)) (* 256 (div m 128)) (* 256 (div n 128))) 127) (<= (+ 2 (div n 256) (* 2 (div (+ m
	// (- 512)) 1024))) 0) (<= (+ m (* 256 (div m 128)) 385 (* (div (+ n (- 128)) 256) 512)) 0) (<= (+ m (* 256 (div (+
	// m (- 128)) 256)) (* 256 (div (+ n (- 128)) 256)) 385 (* 256 (div n 128))) 0) (<= (+ m (* 768 (div m 128)) (* 768
	// (div n 256)) (* 256 (div n 128))) 255) (<= (+ 3 (div n 128) (* (div (+ m (- 256)) 512) 4)) 0) (<= (+ m (* (div (+
	// m (* (div n 256) 128) (- 128)) 384) 128) 129 (* 128 (div (+ n (- 128)) 256))) 0) (<= (+ m (* (div (+ m (- 256))
	// 512) 512) 385 (* 256 (div n 128))) 0) (<= (+ (* 4 (div m 128)) (* 5 (div n 256))) 1) (<= (+ m (* 768 (div (+ m (-
	// 128)) 256)) 513 (* 256 (div n 256))) 0) (<= (+ 3 (* (div (+ m (- 128)) 256) 4) (* 5 (div n 256))) 0) (<= (+ m 513
	// (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 768) (* 256 (div n 128))) 0) (<= (+ m (* (div (+ m (- 256)) 512)
	// 512) (* 256 (div n 256)) 385) 0) (<= (+ m 385 (* (div (+ m (- 512)) 1024) 512) (* 256 (div n 128))) 0) (<= (+ 3
	// (div n 128) (* (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 4)) 0) (<= (+ (* (div n 256) 3) (div (+ n (- 128))
	// 256)) 0) (<= (+ m (* (div (+ m (- 128)) 256) 512) 385 (* 768 (div n 128))) 0) (<= (+ (* 256 (div n 256)) (* 256
	// (div m 128)) n) 127) (<= (+ 3 (div n 128) (* 4 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256))) 0) (<= (+ m 513
	// (* 768 (div (+ m (- 256)) 512)) (* 256 (div n 256))) 0) (<= (+ (* (div (+ m (- 256) (* 256 (div n 256))) 768) 4)
	// 3 (div n 128)) 0) (<= (+ 3 (div (+ n (- 128)) 256) (* 3 (div (+ m (* (div n 256) 128) (- 128)) 384))) 0) (<= (+ m
	// (* 256 (div n 256)) (* (div (+ m (- 128)) 256) 512) 385) 0) (<= (+ (div n 256) (div (+ n (- 128)) 256) 1) 0) (<=
	// (+ m (* (div n 256) 512) (* 256 (div m 128))) 127) (<= (+ m 129 (* (div (+ m (* 128 (div n 128)) (- 128)) 256)
	// 512)) 0) (<= (+ m (* 256 (div n 256)) 129 (* 256 (div (+ m (* 256 (div n 256)) (- 128)) 512))) 0) (<= (+ m (* 256
	// (div (+ n (- 128)) 256)) 513 (* (div (+ m (* 256 (div n 256)) (- 128)) 512) 512)) 0) (<= (+ 257 m (* 768 (div (+
	// m (* 256 (div (+ n (- 128)) 256))) 512))) 0) (<= (+ m (* 128 (div (+ m (- 384)) 768)) 129 (* 128 (div (+ n (-
	// 128)) 256))) 0) (<= (+ m 513 (* (div (+ m (- 256) (* 256 (div n 128))) 512) 768) (* 256 (div n 128))) 0) (<= (+
	// (* 2 (div m 128)) (* (div n 256) 3)) 0) (<= (+ m (* 768 (div (+ m (* (div n 256) 128) (- 128)) 384)) 513 (* 256
	// (div n 128))) 0) (<= (+ 3 (* 3 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)) (div (+ n (- 128)) 256)) 0) (<=
	// (+ (div n 256) 3 (* (div (+ m (- 256)) 512) 4)) 0) (<= (+ 2 (div (+ m (- 256) (* 256 (div n 256))) 768) (div (+ n
	// (- 128)) 256)) 0) (<= (+ m (* (div n 256) 512) (* (div (+ m (- 128)) 256) 512) 129) 0) (<= (+ (* 3 (div (+ m (*
	// 128 (div (+ n (- 128)) 256))) 256)) 3 (div (+ n (- 128)) 256)) 0) (<= (+ m 513 (* 256 (div n 256)) (* 768 (div (+
	// m (* 256 (div (+ n (- 128)) 256))) 512))) 0) (<= (+ m (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 512) 129) 0)
	// (<= (+ (* (div n 128) 4) (div n 256) 3 (* (div (+ m (- 128)) 256) 4)) 0) (<= (+ m (* 768 (div (+ (- 2) (div n
	// 256)) 3)) 513 (* 256 (div n 128))) 0) (<= (+ m (* 128 (div (+ m (- 128)) 256)) 129 (* 128 (div (+ n (- 128))
	// 256))) 0) (<= (+ (div (+ n (- 128)) 256) (* 2 (div n 256))) 0) (<= (+ m (* (div (+ m (* 128 (div (+ n (- 128))
	// 256))) 256) 512) 129) 0) (<= (+ m (* 768 (div (+ (- 2) (div n 256)) 3)) 513 (* 256 (div n 256))) 0) (<= (+ (* 5
	// (div n 128)) 3 (* (div (+ m (- 128)) 256) 4)) 0) (<= (+ (* 2 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)) 2
	// (div (+ n (- 128)) 256)) 0) (<= (+ (div n 256) (div (+ n (- 128)) 256) (div m 128) 1) 0) (<= (+ m (* 768 (div (+
	// m (- 128)) 256)) 513 (* (div n 256) 1024)) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div (+ m (* 128
	// (div n 128)) (- 128)) 256)) 385) 0) (<= (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div (+ m (- 256)) 512)) 385)
	// 0) (<= (+ m (* 128 (div n 128)) 129 (* 256 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256))) 0) (<= (+ m (* 256
	// (div (+ n (- 128)) 256)) 513 (* (div (+ m (- 512)) 1024) 512)) 0) (<= (+ m (* 256 (div n 256)) (* 256 (div n
	// 128))) 127) (<= (+ m (* 768 (div n 256)) (* 256 (div n 128))) 255) (<= (+ m (* 256 (div (+ n (- 128)) 256)) 513
	// (* (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 512)) 0) (<= (+ m 513 (* 256 (div n 256)) (* 768 (div (+ m (-
	// 384)) 768))) 0) (<= (+ (* (div (+ m (* (div n 256) 128) (- 128)) 384) 512) m (* 256 (div n 256)) 385) 0) (<= (+ m
	// (* 256 (div n 256)) 385 (* (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 512)) 0) (<= (+ m (* 256 (div (+ n (-
	// 128)) 256)) 513 (* (div (+ m (- 128)) 256) 512) (* (div n 128) 512)) 0) (<= (+ m (* 256 (div (+ m (- 128)) 256))
	// (* 256 (div (+ n (- 128)) 256)) 385) 0) (<= (+ (* 256 (div (+ m (* 128 (div n 128)) (- 128)) 256)) n 129) 0) (<=
	// (+ m (* 256 (div n 256)) 129 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 256)) 0) (<= (+ 257 m (* 768 (div (+ m
	// (- 128)) 256))) 0) (<= (+ 2 (* 2 (div (+ n (- 128)) 256)) (div m 128)) 0) (<= (+ m 129 (* (div (+ m (- 256) (*
	// 256 (div n 128))) 512) 512)) 0) (<= (+ m (* (div n 256) 512) (* (div m 128) 512) (* 256 (div n 128))) 127) (<= (+
	// m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (* 128 (div (+ n (- 128)) 256))) 256) 512)) 0) (<= (+ m (* 256
	// (div (+ n (- 128)) 256)) (* (div n 256) 128) 129 (* 256 (div (+ m 128) 256))) 0) (<= (+ (div n 128) (* (div (+ n
	// (- 128)) 256) 4)) 1) (<= (+ m (* 256 (div n 256)) (* 256 (div m 128))) 255) (<= (+ (div n 256) 3 (* (div (+ m (*
	// (div n 256) 128) (- 128)) 384) 4)) 0) (<= (+ m 129 (* (div (+ m (* 256 (div n 256)) (- 128)) 512) 512)) 0) (<= (+
	// (* 256 (div (+ (- 2) (div n 256)) 3)) m (* (div n 256) 128) 129) 0) (<= (+ m (* 256 (div (+ m (- 128)) 256)) (*
	// 256 (div n 256)) 129 (* 256 (div n 128))) 0) (<= (+ (* 3 (div n 128)) 3 (* 3 (div (+ m (- 128)) 256)) (div (+ n
	// (- 128)) 256)) 0) (<= (+ (* 256 (div (+ (- 2) (div n 256)) 3)) m (* 256 (div n 256)) 129) 0) (<= (+ 3 (div n 128)
	// (* (div (+ m (- 256) (* 256 (div n 128))) 512) 4)) 0) (<= (+ m (* 768 (div n 256))) 127) (<= (+ 257 n (* (div (+
	// m (- 256) (* 256 (div n 128))) 512) 512)) 0) (<= (+ (div n 256) (div (+ m (- 128)) 256) 1) 0) (<= (+ m (* 256
	// (div (+ n (- 128)) 256)) 129 (* 128 (div m 128))) 0) (<= (+ m (* 128 (div n 128)) (* 256 (div n 256)) (* 256 (div
	// m 128))) 127) (<= (+ m (* (div (+ m (* 256 (div n 256)) (- 128)) 512) 512) 385 (* 256 (div n 128))) 0) (<= (+ m
	// (* 256 (div (+ n (- 128)) 256)) (* (div n 256) 128) (* 256 (div m 128)) 129) 0) (<= (+ (* 256 (div (+ n (- 128))
	// 256)) n 129 (* 256 (div (+ m 128) 256))) 0) (<= (+ (* 2 (div (+ m (* 256 (div n 256)) (- 128)) 512)) 2 (div (+ n
	// (- 128)) 256)) 0) (<= (+ m (* (div (+ m (- 384)) 768) 512) (* 256 (div (+ n (- 128)) 256)) 513) 0) (<= (+ m (*
	// 256 (div (+ m (- 256)) 512)) 1) 0) (<= (+ m (* 128 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) 129 (* 128
	// (div (+ n (- 128)) 256))) 0) (<= (+ 257 (* (div n 256) 512) (* (div (+ m (- 128)) 256) 512) n) 0) (<= (+ 257 (*
	// (div (+ m (- 256)) 512) 512) n) 0) (<= (+ (* 2 (div (+ m (- 384)) 768)) 2 (div n 128)) 0) (<= (+ (* 256 (div (+ m
	// (- 256) (* 256 (div n 256))) 768)) m (* 256 (div n 256)) 129) 0) (<= (+ m (* 128 (div n 128)) (* 256 (div (+ m (-
	// 128)) 256)) 129) 0) (<= (+ m (* (div n 128) 1024) (* 768 (div (+ m (- 128)) 256)) 513) 0) (<= (+ m 513 (* (div (+
	// m (* 128 (div n 128)) (- 128)) 256) 768) (* 256 (div n 128))) 0) (<= (+ (* 256 (div (+ (- 2) (div n 256)) 3)) m
	// 129 (* 256 (div n 128))) 0) (<= (+ m (* 256 (div n 256)) (* (div (+ m (- 128)) 256) 512) 385 (* (div n 128) 512))
	// 0) (<= (+ m (* (div n 256) 128) 129 (* 256 (div (+ m (* 256 (div n 256)) (- 128)) 512))) 0))";
	// final String simplified =
	// "(and (<= (+ (div n 256) (div (+ n (- 128)) 256) 1) 0) (<= (+ 257 m (* 768 (div (+ m (- 128)) 256))) 0))";
	// runSimplificationTest(funDecls, formulaAsString, simplified, SimplificationTechnique.SIMPLIFY_DDA2, mServices,
	// mLogger, mMgdScript, mCsvWriter);
	// }

	/**
	 * Negation of {@link SimplificationTest#bvToIntBadgerExists01} Not a regression test because currently Z3 needs a
	 * lot of time.
	 */
	public void bvToIntBadgerForall01() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "m", "n"), };
		final String formulaAsString =
				"(or (< 0 (+ m 129 (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 128) (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ 257 m (* 768 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)))) (< 0 (+ (div (+ m (* (div n 256) 128) (- 128)) 384) 1)) (< 0 (+ m (* (div n 256) 512) (* (div (+ m (- 128)) 256) 512) 385 (* 256 (div n 128)))) (< 0 (+ (* 2 (div m 128)) (* (div n 256) 3))) (< 0 (+ m (* 256 (div (+ m (- 384)) 768)) 1)) (< 0 (+ (* 256 (div (+ m (- 128)) 256)) (* 256 (div n 256)) n 129)) (< 0 (+ m (* 256 (div n 256)) 129 (* 256 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)))) (< 0 (+ m (* 256 (div (+ m (- 128)) 256)) (* (div n 256) 128) 129)) (< 0 (+ (div n 128) (* 2 (div (+ n (- 128)) 256)))) (< 0 (+ m (* (div (+ m (- 128)) 256) 512) (* 768 (div n 256)) 385)) (< 0 (+ (* 3 (div (+ m (- 256) (* 256 (div n 256))) 768)) 3 (div (+ n (- 128)) 256))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (- 128)) 256) 512))) (< 0 (+ 3 (div (+ n (- 128)) 256) (* 3 (div (+ m (- 384)) 768)))) (< 0 (+ n 129 (* 256 (div (+ m (* 256 (div n 256)) (- 128)) 512)))) (< 0 (+ (* (div (+ m 128) 256) 4) (div n 256) 3 (* (div (+ n (- 128)) 256) 4))) (< 0 (+ m (* (div (+ m (- 256) (* 256 (div n 256))) 768) 512) (* 256 (div n 256)) 385)) (< 0 (+ m (* 256 (div (+ m (- 128)) 256)) 129 (* (div n 128) 512))) (< 0 (+ 257 (* (div (+ m (- 384)) 768) 512) n)) (< 0 (+ m (* (div (+ m (- 256)) 512) 512) 129)) (< 0 (+ m (* (div (+ m (- 384)) 768) 512) 129)) (< 0 (+ m 513 (* 768 (div m 128)) (* 256 (div n 128)) (* 768 (div (+ n (- 128)) 256)))) (< 0 (+ 257 n (* (div (+ m (- 512)) 1024) 512))) (< 0 (+ 2 (div (+ (- 2) (div n 256)) 3) (div (+ n (- 128)) 256))) (< 0 (+ 2 (div n 128) (div (+ n (- 128)) 256) (div (+ m (- 128)) 256))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* (div n 256) 128) 129 (* 256 (div (+ m 128) 256)))) (< 0 (+ 3 (* (div (+ m (* 256 (div n 256)) (- 128)) 512) 4) (div n 128))) (< 1 (+ (div n 256) (* (div (+ n (- 128)) 256) 4))) (< 0 (+ m (* 768 (div (+ m (- 128)) 256)) 513 (* 256 (div n 256)) (* 768 (div n 128)))) (< 0 (+ m (* 256 (div n 256)) (* (div (+ m 128) 256) 512) 385 (* (div (+ n (- 128)) 256) 512))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* (div (+ m (- 256)) 512) 512) 513)) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* (div (+ m (- 256) (* 256 (div n 128))) 512) 256) 385)) (< 0 (+ 2 (div (+ m (- 256) (* 256 (div n 256))) 768) (div (+ n (- 128)) 256))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 385 (* 256 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)))) (< 127 (+ m (* 768 (div n 256)))) (< 0 (+ (* 256 (div (+ m (- 256)) 512)) n 129)) (< 0 (+ 2 (div n 128) (* 2 (div (+ m (- 128)) 256)))) (< 0 (+ (div n 256) (div (+ m (* (div n 256) 128) (- 128)) 384))) (< 0 (+ 3 (div (+ n (- 128)) 256) (* 3 (div (+ m (* (div n 256) 128) (- 128)) 384)))) (< 0 (+ 257 n (* (div (+ m 128) 256) 512) (* (div (+ n (- 128)) 256) 512))) (< 0 (+ n 129 (* 256 (div (+ m (- 384)) 768)))) (< 0 (+ 257 n (* (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 512))) (< 0 (+ m (* (div (+ m 128) 256) 512) 385 (* 256 (div n 128)) (* (div (+ n (- 128)) 256) 512))) (< 0 (+ (* 2 (div (+ m (* (div n 256) 128) (- 128)) 384)) 2 (div n 128))) (< 0 (+ m 513 (* 256 (div n 256)) (* (div (+ m (- 256) (* 256 (div n 128))) 512) 768))) (< 0 (+ m (* 256 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)) 1)) (< 0 (+ (div n 256) 3 (* (div (+ m (- 128)) 256) 4))) (< 0 (+ 2 (div n 128) (* 2 (div (+ m (- 512)) 1024)))) (< 0 (+ m (* 128 (div n 128)) (* 256 (div (+ m (* 128 (div n 128)) (- 128)) 256)) 129)) (< 0 (+ (div (+ m (* 256 (div n 256)) (- 128)) 512) 1)) (< 0 (+ (div n 256) (div (+ m (- 512)) 1024))) (< 0 (+ m (* 256 (div n 256)) (* (div m 128) 512) 385 (* (div (+ n (- 128)) 256) 512))) (< 0 (+ (* (div (+ m (- 256) (* 256 (div n 128))) 512) 256) n 129)) (< 0 (+ m 513 (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 768) (* 256 (div n 128)))) (< 0 (+ 3 (div n 128) (* (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 4))) (< 0 (+ 2 (div (+ m (- 256)) 512) (div (+ n (- 128)) 256))) (< 0 (+ 257 m (* 768 (div (+ m (- 512)) 1024)))) (< 0 (+ (* 2 (div (+ m (- 384)) 768)) 2 (div n 128))) (< 0 (+ 257 m (* (div (+ m (- 256) (* 256 (div n 128))) 512) 768))) (< 0 (+ (* (div n 128) 4) (div n 256) 3 (* (div (+ m (- 128)) 256) 4))) (< 0 (+ m (* 128 (div n 128)) (* 256 (div (+ n (- 128)) 256)) (* 256 (div m 128)) 129)) (< 0 (+ (div n 128) (* 2 (div n 256)))) (< 0 (+ 2 (* 2 (div (+ m (- 256)) 512)) (div (+ n (- 128)) 256))) (< 0 (+ m (* 128 (div n 128)) 129 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 256))) (< 0 (+ 3 (div (+ n (- 128)) 256) (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 3))) (< 0 (+ m (* 256 (div (+ m (- 128)) 256)) (* 256 (div (+ n (- 128)) 256)) 385)) (< 0 (+ (* 2 (div m 128)) (div (+ n (- 128)) 256) (* 2 (div n 256)))) (< 0 (+ 257 (* (div (+ m (- 128)) 256) 512) n)) (< 0 (+ (* 256 (div (+ n (- 128)) 256)) (* 256 (div m 128)) n 129)) (< 0 (+ m (* 256 (div (+ m (* 128 (div n 128)) (- 128)) 256)) (* (div n 256) 128) 129)) (< 0 (+ 2 (div n 256) (div (+ n (- 128)) 256) (div (+ m (- 128)) 256))) (< 0 (+ 3 (div n 128) (* (div (+ m (- 256) (* 256 (div n 128))) 512) 4))) (< 0 (+ 2 (div n 128) (* 2 (div (+ m (- 256)) 512)))) (< 0 (+ (div n 256) 3 (* (div (+ m (* 256 (div n 256)) (- 128)) 512) 4))) (< 0 (+ m 129 (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 512))) (< 0 (+ m 513 (* 256 (div n 256)) (* 768 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)))) (< 0 (+ (div n 256) 3 (* 4 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)))) (< 0 (+ (div n 256) (div (+ m (* 256 (div (+ n (- 128)) 256))) 512))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ (- 2) (div n 256)) 3) 512))) (< 127 (+ m (* 128 (div n 128)) (* 256 (div (+ n (- 128)) 256)))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (- 512)) 1024) 512))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div (+ m (* (div n 256) 128) (- 128)) 384)) 385)) (< 0 (+ 257 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 512) n)) (< 0 (+ m (* 768 (div (+ m (* (div n 256) 128) (- 128)) 384)) 513 (* 256 (div n 128)))) (< 127 (+ m (* 256 (div n 256)))) (< 0 (+ m 385 (* 256 (div n 128)) (* (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 512))) (< 0 (+ m (* (div n 256) 128) 129 (* 256 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)))) (< 0 (+ m (* 128 (div n 128)) (* (div (+ m (- 256) (* 256 (div n 128))) 512) 256) 129)) (< 0 (+ m (* 256 (div n 256)) (* (div (+ m (- 128)) 256) 512) 385)) (< 0 (+ (* 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) m (* 128 (div n 128)) 129)) (< 0 (+ m 385 (* 256 (div n 128)) (* (div (+ m (- 256) (* 256 (div n 128))) 512) 512))) (< 255 (+ m (* 256 (div n 256)) (* 256 (div m 128)))) (< 0 (+ (* 2 (div (+ m (* 256 (div n 256)) (- 128)) 512)) 2 (div n 128))) (< 0 (+ 257 (* (div (+ m (* 128 (div (+ n (- 128)) 256))) 256) 512) n)) (< 0 (+ (* (div n 256) 3) (div (+ n (- 128)) 256))) (< 0 (+ m 513 (* 256 (div n 256)) (* 768 (div (+ m (* 256 (div n 256)) (- 128)) 512)))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div (+ m (* 128 (div n 128)) (- 128)) 256)) 385)) (< 0 (+ m (* (div (+ m (- 384)) 768) 512) (* 256 (div (+ n (- 128)) 256)) 513)) (< 127 (+ (* 256 (div (+ n (- 128)) 256)) n)) (< 0 (+ m (* (div (+ m (- 256)) 512) 512) (* 256 (div n 256)) 385)) (< 127 (+ m (* 128 (div n 128)) (* 256 (div n 256)))) (< 0 (+ (* 2 (div (+ (- 2) (div n 256)) 3)) 2 (div n 256))) (< 0 (+ 2 (div n 256) (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 2))) (< 0 (+ 3 (* 3 (div (+ m (- 256)) 512)) (div (+ n (- 128)) 256))) (< 0 (+ (div n 256) (div (+ m 128) 256) (div (+ n (- 128)) 256))) (< 0 (+ m (* (div n 256) 128) (* 128 (div m 128)) (* 128 (div (+ n (- 128)) 256)) 1)) (< 1 (+ (* (div n 256) 4) (* 4 (div m 128)) (div n 128))) (< 0 (+ m (* 128 (div (+ m (- 128)) 256)) (* (div n 256) 128) 129 (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ 2 (* 2 (div (+ m (- 128)) 256)) (div (+ n (- 128)) 256) (* 2 (div n 256)))) (< 255 (+ m (* 768 (div n 256)) (* 256 (div n 128)))) (< 255 (+ m (* 768 (div m 128)) (* 768 (div n 256)) (* 256 (div n 128)))) (< 0 (+ m (* (div (+ m (- 256) (* 256 (div n 128))) 512) 128) 129 (* 128 (div (+ n (- 128)) 256)))) (< 127 (+ m (* (div n 256) 384))) (< 0 (+ 2 (div (+ n (- 128)) 256) (* 2 (div (+ m (- 512)) 1024)))) (< 0 (+ m 513 (* 256 (div n 256)) (* 768 (div (+ m (- 256) (* 256 (div n 256))) 768)))) (< 0 (+ m (* 256 (div n 256)) (* (div (+ (- 2) (div n 256)) 3) 512) 385)) (< 0 (+ (div n 256) (div (+ n (- 128)) 256) 1)) (< 0 (+ 257 (* (div (+ (- 2) (div n 256)) 3) 512) n)) (< 0 (+ m (* (div n 256) 128) (* 256 (div (+ m (- 256)) 512)) 129)) (< 0 (+ 2 (div n 128) (* 2 (div (+ n (- 128)) 256)) (* 2 (div (+ m 128) 256)))) (< 0 (+ m (* 768 (div (+ m (- 128)) 256)) 513 (* 768 (div n 256)) (* 256 (div n 128)))) (< 0 (+ (* (div (+ m (- 512)) 1024) 4) 3 (div n 128))) (< 0 (+ (* 256 (div (+ (- 2) (div n 256)) 3)) m (* 256 (div (+ n (- 128)) 256)) 385)) (< 0 (+ m 513 (* 768 (div (+ m (- 256)) 512)) (* 256 (div n 128)))) (< 0 (+ m (* 256 (div (+ m (* 128 (div n 128)) (- 128)) 256)) (* 256 (div n 256)) 129)) (< 0 (+ m (* 256 (div (+ m (* 128 (div n 128)) (- 128)) 256)) 1)) (< 0 (+ 257 n (* (div (+ m (* 256 (div n 256)) (- 128)) 512) 512))) (< 0 (+ (* 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) n 129)) (< 0 (+ (* 256 (div (+ (- 2) (div n 256)) 3)) m 129 (* 256 (div n 128)))) (< 0 (+ 2 (div n 128) (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 2))) (< 0 (+ 2 (div (+ n (- 128)) 256) (* 2 (div (+ m (- 256) (* 256 (div n 256))) 768)))) (< 0 (+ m (* 128 (div n 128)) (* 256 (div (+ m (- 128)) 256)) 129)) (< 0 (+ (div (+ n (- 128)) 256) (* 2 (div n 256)))) (< 0 (+ (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 2 (div (+ n (- 128)) 256))) (< 0 (+ m 129 (* 256 (div n 128)) (* 256 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)))) (< 0 (+ (* (div (+ m (* (div n 256) 128) (- 128)) 384) 512) m 129)) (< 0 (+ (* (div (+ m (- 256) (* 256 (div n 256))) 768) 4) (div n 256) 3)) (< 0 (+ m (* 128 (div (+ m (- 384)) 768)) 129 (* 128 (div (+ n (- 128)) 256)))) (< 127 (+ m (* 256 (div n 256)) (* 256 (div n 128)))) (< 0 (+ (* 2 (div (+ m (- 384)) 768)) 2 (div (+ n (- 128)) 256))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div m 128)) 1)) (< 0 (+ 3 (* (div n 256) 3) (* 3 (div (+ m (- 128)) 256)) (div (+ n (- 128)) 256))) (< 1 (+ (div n 128) (* (div (+ n (- 128)) 256) 4))) (< 0 (+ m 1 (* 768 (div (+ n (- 128)) 256)))) (< 0 (+ m (* 256 (div (+ m (* 256 (div n 256)) (- 128)) 512)) 1)) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div (+ m (- 256)) 512)) 385)) (< 255 (+ (* (div n 256) 512) n (* (div m 128) 512))) (< 255 (+ m (* 256 (div n 128)) (* 768 (div (+ n (- 128)) 256)))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 385 (* 256 (div (+ m (- 512)) 1024)))) (< 0 (+ m (* (div (+ m (- 256)) 512) 128) 129 (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ 2 (div n 128) (* 2 (div (+ m (- 256) (* 256 (div n 256))) 768)))) (< 0 (+ (* 3 (div n 128)) 2 (* 2 (div (+ m (- 128)) 256)))) (< 0 (+ (div n 256) (div (+ n (- 128)) 256) (div m 128) 1)) (< 0 (+ 2 (div (+ n (- 128)) 256) (div (+ m (- 128)) 256))) (< 0 (+ 257 m (* 768 (div (+ m (- 128)) 256)) (* 768 (div n 128)))) (< 0 (+ m (* 768 (div (+ (- 2) (div n 256)) 3)) 513 (* 256 (div n 128)))) (< 0 (+ m (* 128 (div n 128)) (* 128 (div (+ m (- 128)) 256)) 129 (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ m (* (div (+ m (* 128 (div (+ n (- 128)) 256))) 256) 512) 385 (* 256 (div n 128)))) (< 0 (+ m (* 768 (div (+ m (- 128)) 256)) 513 (* 256 (div n 128)))) (< 127 (+ m (* (div n 256) 512))) (< 0 (+ (div n 256) (* 2 (div (+ n (- 128)) 256)))) (< 127 (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div n 128)))) (< 255 (+ m (* (div n 256) 1024))) (< 0 (+ 257 m (* 768 (div (+ m 128) 256)) (* 768 (div (+ n (- 128)) 256)))) (< 0 (+ (* 2 (div (+ (- 2) (div n 256)) 3)) 2 (div n 128))) (< 0 (+ m (* 128 (div n 128)) 129 (* 256 (div (+ m (* (div n 256) 128) (- 128)) 384)))) (< 127 (+ m (* 256 (div (+ n (- 128)) 256)) (* (div n 256) 128))) (< 0 (+ m 129 (* 128 (div (+ m (- 512)) 1024)) (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ m 129 (* (div (+ m 128) 256) 512) (* (div (+ n (- 128)) 256) 512))) (< 0 (+ m 129 (* (div (+ m (- 256) (* 256 (div n 128))) 512) 512))) (< 0 (+ m (* 256 (div n 256)) 129 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 256))) (< 0 (+ (* (div (+ m 128) 256) 4) 3 (div n 128) (* (div (+ n (- 128)) 256) 4))) (< 0 (+ m (* 256 (div (+ m (* 128 (div n 128)) (- 128)) 256)) 129 (* 256 (div n 128)))) (< 0 (+ 257 m (* 768 (div (+ m (* 256 (div n 256)) (- 128)) 512)))) (< 0 (+ (* 2 (div (+ m (* 256 (div n 256)) (- 128)) 512)) 2 (div (+ n (- 128)) 256))) (< 0 (+ m 385 (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 512) (* 256 (div n 128)))) (< 0 (+ 2 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) (div (+ n (- 128)) 256))) (< 0 (+ 257 m (* 768 (div (+ m (- 128)) 256)))) (< 0 (+ m (* 128 (div n 128)) (* 256 (div (+ m (- 256)) 512)) 129)) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 129 (* 256 (div (+ m 128) 256)) (* 256 (div n 128)))) (< 0 (+ m (* 256 (div n 256)) 129 (* 256 (div (+ m (- 512)) 1024)))) (< 0 (+ m (* 256 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) 1)) (< 0 (+ m 129 (* (div (+ (- 2) (div n 256)) 3) 128) (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ m (* (div (+ m (* 128 (div (+ n (- 128)) 256))) 256) 512) 129)) (< 0 (+ (* 2 (div m 128)) 2 (div n 256) (* 2 (div (+ n (- 128)) 256)))) (< 0 (+ (* 256 (div (+ m (* 128 (div n 128)) (- 128)) 256)) n 129)) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div n 256)) 129)) (< 0 (+ m (* (div n 256) 512) (* 256 (div (+ n (- 128)) 256)) 1)) (< 0 (+ 2 (div (+ m (* 256 (div n 256)) (- 128)) 512) (div (+ n (- 128)) 256))) (< 0 (+ m 513 (* (div m 128) 512) (* 768 (div (+ n (- 128)) 256)))) (< 0 (+ m (* (div n 128) 1024) (* 768 (div (+ m (- 128)) 256)) 513)) (< 0 (+ m (* (div (+ m (* (div n 256) 128) (- 128)) 384) 128) 129 (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ m (* 256 (div n 256)) (* 256 (div (+ m (- 256)) 512)) 129)) (< 127 (+ (* 256 (div n 256)) n)) (< 0 (+ 257 m (* 768 (div (+ m (* (div n 256) 128) (- 128)) 384)))) (< 0 (+ m (* 256 (div n 256)) (* (div (+ m (* 256 (div n 256)) (- 128)) 512) 512) 385)) (< 1 (+ (* (div n 256) 4) (div n 128))) (< 0 (+ (div n 256) (div (+ (- 2) (div n 256)) 3))) (< 0 (+ (div (+ m 128) 256) (div (+ n (- 128)) 256) 1)) (< 0 (+ m (* 256 (div n 256)) (* (div (+ m (- 128)) 256) 512) 385 (* (div n 128) 512))) (< 0 (+ m (* 256 (div n 256)) 385 (* (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 512))) (< 0 (+ 2 (div n 256) (* 2 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)))) (< 0 (+ 3 (div (+ n (- 128)) 256) (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 3))) (< 0 (+ m (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 512) 385 (* 256 (div n 128)))) (< 0 (+ m 129 (* 256 (div (+ m (- 512)) 1024)) (* 256 (div n 128)))) (< 0 (+ 2 (div (+ n (- 128)) 256) (div (+ m (- 384)) 768))) (< 0 (+ m 513 (* 256 (div n 256)) (* 768 (div m 128)) (* 768 (div (+ n (- 128)) 256)))) (< 0 (+ (* 256 (div (+ (- 2) (div n 256)) 3)) m (* (div n 256) 128) 129)) (< 0 (+ (* 3 (div (+ m (- 512)) 1024)) 3 (div (+ n (- 128)) 256))) (< 0 (+ 257 m (* 768 (div m 128)) (* 768 (div (+ n (- 128)) 256)))) (< 0 (+ m (* (div n 256) 128) 129 (* 256 (div (+ m (* (div n 256) 128) (- 128)) 384)))) (< 0 (+ (* (div (+ m (* (div n 256) 128) (- 128)) 384) 512) m (* 256 (div (+ n (- 128)) 256)) 513)) (< 0 (+ 2 (div (+ m 128) 256) (* 2 (div (+ n (- 128)) 256)))) (< 0 (+ 257 (* (div (+ m (- 256) (* 256 (div n 256))) 768) 512) n)) (< 0 (+ 3 (* 3 (div m 128)) (* (div (+ n (- 128)) 256) 4))) (< 0 (+ (div n 256) (div m 128))) (< 0 (+ (div (+ m (- 512)) 1024) 1)) (< 0 (+ (div (+ m (- 256)) 512) 1)) (< 0 (+ (div (+ m (- 384)) 768) 1)) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (* 256 (div n 256)) (- 128)) 512) 512))) (< 127 (+ m (* (div m 128) 512) (* 768 (div n 256)))) (< 0 (+ m 513 (* 256 (div n 256)) (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 768))) (< 0 (+ m (* 256 (div (+ m (- 128)) 256)) 1)) (< 0 (+ m 513 (* 256 (div n 128)) (* 768 (div (+ m 128) 256)) (* 768 (div (+ n (- 128)) 256)))) (< 0 (+ (div n 256) (div (+ m (- 256) (* 256 (div n 256))) 768))) (< 0 (+ m (* 256 (div (+ m (- 128)) 256)) (* 256 (div n 256)) 129 (* 256 (div n 128)))) (< 0 (+ 2 (div n 256) (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 2))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div n 256)) 129 (* 256 (div (+ m 128) 256)))) (< 0 (+ m (* 256 (div n 256)) 385 (* (div (+ m (- 512)) 1024) 512))) (< 0 (+ m (* 256 (div m 128)) 385 (* (div (+ n (- 128)) 256) 512))) (< 0 (+ (div n 256) (div (+ m (* 256 (div n 256)) (- 128)) 512))) (< 0 (+ m (* (div (+ m (- 256) (* 256 (div n 256))) 768) 512) 129)) (< 0 (+ (div (+ m (* 128 (div n 128)) (- 128)) 256) (div n 256))) (< 0 (+ 2 (div (+ n (- 128)) 256) (div (+ m (* 128 (div (+ n (- 128)) 256))) 256))) (< 0 (+ m (* (div (+ m (- 256) (* 256 (div n 128))) 512) 256) 1)) (< 0 (+ m (* 256 (div (+ m (- 128)) 256)) 129 (* 256 (div n 128)))) (< 0 (+ m (* 256 (div n 256)) 385 (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 512))) (< 0 (+ m (* 256 (div (+ m (- 512)) 1024)) 1)) (< 0 (+ m 513 (* 256 (div n 128)) (* 768 (div (+ m (* 256 (div n 256)) (- 128)) 512)))) (< 0 (+ (div n 256) 3 (* (div (+ m (- 256) (* 256 (div n 128))) 512) 4))) (< 0 (+ (* (div n 256) 3) (* 3 (div m 128)) (div (+ n (- 128)) 256))) (< 0 (+ m (* (div m 128) 512) 385 (* 256 (div n 128)) (* (div (+ n (- 128)) 256) 512))) (< 0 (+ (* (div (+ m (- 256) (* 256 (div n 128))) 512) 2) 2 (div (+ n (- 128)) 256))) (< 0 (+ m 513 (* (div (+ m (- 256) (* 256 (div n 128))) 512) 768) (* 256 (div n 128)))) (< 0 (+ (* 256 (div (+ m (- 128)) 256)) n 129 (* 256 (div n 128)))) (< 0 (+ m (* 256 (div n 256)) 129 (* 256 (div (+ m (* 256 (div n 256)) (- 128)) 512)))) (< 0 (+ m (* (div (+ m (- 128)) 256) 512) 385 (* 256 (div n 128)))) (< 255 (+ m (* 256 (div n 256)) (* 768 (div (+ n (- 128)) 256)))) (< 0 (+ 257 m (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 768))) (< 255 (+ m (* (div n 256) 1024) (* 768 (div m 128)))) (< 0 (+ (div n 256) (div n 128) (div (+ m (- 128)) 256))) (< 0 (+ 257 m (* 768 (div (+ m (- 128)) 256)) (* 768 (div n 256)))) (< 0 (+ (* 2 (div (+ (- 2) (div n 256)) 3)) 2 (div (+ n (- 128)) 256))) (< 0 (+ (div n 256) 3 (* (div (+ m (* (div n 256) 128) (- 128)) 384) 4))) (< 0 (+ 3 (* 3 (div (+ m (- 128)) 256)) (div (+ n (- 128)) 256))) (< 0 (+ 257 n (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 512))) (< 0 (+ m 129 (* 128 (div (+ m (* 256 (div n 256)) (- 128)) 512)) (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ m (* 768 (div (+ m (- 512)) 1024)) 513 (* 256 (div n 256)))) (< 0 (+ 3 (div n 128) (* (div (+ (- 2) (div n 256)) 3) 4))) (< 0 (+ 2 (div n 256) (* 2 (div (+ m (- 128)) 256)))) (< 0 (+ (* 2 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)) 2 (div n 256))) (< 0 (+ m 385 (* (div (+ m (- 512)) 1024) 512) (* 256 (div n 128)))) (< 0 (+ m (* (div (+ m (- 256)) 512) 512) 385 (* 256 (div n 128)))) (< 0 (+ m 129 (* (div m 128) 512) (* (div (+ n (- 128)) 256) 512))) (< 0 (+ 257 m (* 768 (div (+ m (- 256)) 512)))) (< 0 (+ 3 (div n 128) (* (div (+ m (- 256)) 512) 4))) (< 0 (+ 2 (div (+ m (- 512)) 1024) (div (+ n (- 128)) 256))) (< 0 (+ 2 (* 2 (div n 128)) (* 2 (div (+ m (- 128)) 256)) (div (+ n (- 128)) 256))) (< 0 (+ (div (+ n (- 128)) 256) (div m 128) 1)) (< 0 (+ m (* 768 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) 513 (* 256 (div n 128)))) (< 0 (+ (div (+ m (* 128 (div n 128)) (- 128)) 256) 1)) (< 0 (+ 3 (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 4) (div n 128))) (< 0 (+ (* 2 (div (+ m (* (div n 256) 128) (- 128)) 384)) 2 (div (+ n (- 128)) 256))) (< 0 (+ (div (+ m (- 256) (* 256 (div n 128))) 512) 2 (div (+ n (- 128)) 256))) (< 0 (+ (div n 256) 3 (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 4))) (< 0 (+ n 129 (* 256 (div (+ m (* (div n 256) 128) (- 128)) 384)))) (< 0 (+ (div n 256) (div (+ m (- 256)) 512))) (< 127 (+ m (* (div n 256) 512) (* (div m 128) 512) (* 256 (div n 128)))) (< 0 (+ (* 2 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)) 2 (div n 128))) (< 0 (+ m 129 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 128) (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ m (* 768 (div (+ (- 2) (div n 256)) 3)) 513 (* 256 (div n 256)))) (< 0 (+ 2 (div n 256) (* 2 (div (+ n (- 128)) 256)) (* 2 (div (+ m 128) 256)))) (< 0 (+ 2 (div (+ n (- 128)) 256) (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 2))) (< 127 (+ m (* 256 (div n 256)) (* (div (+ n (- 128)) 256) 512))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 385 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 256))) (< 0 (+ (* 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) m 1)) (< 0 (+ (* (div (+ m (* (div n 256) 128) (- 128)) 384) 512) m 385 (* 256 (div n 128)))) (< 0 (+ 2 (* 2 (div (+ n (- 128)) 256)) (div m 128))) (< 0 (+ m (* (div n 256) 512) (* 256 (div (+ n (- 128)) 256)) (* (div m 128) 512) 1)) (< 127 (+ m (* 256 (div n 128)) (* (div (+ n (- 128)) 256) 512))) (< 0 (+ (* 2 (div (+ m (* (div n 256) 128) (- 128)) 384)) 2 (div n 256))) (< 0 (+ 3 (div n 128) (* (div (+ m (- 128)) 256) 4))) (< 0 (+ (div n 256) (div (+ m (* 128 (div (+ n (- 128)) 256))) 256))) (< 0 (+ m (* 256 (div n 256)) 129 (* 256 (div (+ m (* (div n 256) 128) (- 128)) 384)))) (< 511 (+ m (* 768 (div m 128)) (* 768 (div n 256)))) (< 0 (+ 3 (* 3 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)) (div (+ n (- 128)) 256))) (< 0 (+ m (* 768 (div (+ m (- 128)) 256)) 513 (* 256 (div n 256)))) (< 0 (+ m (* 256 (div n 256)) 129 (* 256 (div (+ m (- 384)) 768)))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 129 (* 128 (div m 128)))) (< 0 (+ (div n 128) (div (+ m (- 128)) 256) 1)) (< 0 (+ m (* (div (+ m (- 128)) 256) 512) 129 (* (div n 128) 512))) (< 0 (+ m (* (div n 256) 512) (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (- 128)) 256) 512))) (< 0 (+ (* (div (+ m (- 256) (* 256 (div n 128))) 512) 2) 2 (div n 256))) (< 0 (+ (* (div (+ m (- 512)) 1024) 4) (div n 256) 3)) (< 0 (+ m (* (div (+ m (* 256 (div n 256)) (- 128)) 512) 512) 385 (* 256 (div n 128)))) (< 0 (+ (* 256 (div (+ n (- 128)) 256)) n 129 (* 256 (div (+ m 128) 256)))) (< 0 (+ (* 256 (div (+ (- 2) (div n 256)) 3)) n 129)) (< 0 (+ (* 2 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)) 2 (div (+ n (- 128)) 256))) (< 0 (+ m (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 512) 129)) (< 0 (+ n 129 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 256))) (< 0 (+ m (* 768 (div (+ m (* (div n 256) 128) (- 128)) 384)) 513 (* 256 (div n 256)))) (< 0 (+ (* 3 (div (+ n (- 128)) 256)) 2 (* 2 (div (+ m 128) 256)))) (< 0 (+ m (* 256 (div (+ m (- 128)) 256)) (* 256 (div n 256)) 129)) (< 0 (+ m (* 768 (div (+ m (- 512)) 1024)) 513 (* 256 (div n 128)))) (< 0 (+ 257 m (* 768 (div (+ (- 2) (div n 256)) 3)))) (< 0 (+ (div (+ m (- 256) (* 256 (div n 256))) 768) 1)) (< 0 (+ m (* (div n 256) 128) (* 128 (div (+ n (- 128)) 256)) 1)) (< 0 (+ (div (+ m (* 128 (div n 128)) (- 128)) 256) 2 (div (+ n (- 128)) 256))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div m 128)) 129 (* 256 (div n 128)))) (< 0 (+ (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 1)) (< 0 (+ m 129 (* (div (+ n (- 128)) 256) 512))) (< 0 (+ 2 (* 2 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) (div (+ n (- 128)) 256))) (< 0 (+ m (* (div n 256) 128) 129 (* 256 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)))) (< 127 (+ (* 256 (div n 256)) (* 256 (div m 128)) n)) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 385 (* 256 (div (+ m (- 384)) 768)))) (< 0 (+ (* 3 (div n 128)) 3 (* 3 (div (+ m (- 128)) 256)) (div (+ n (- 128)) 256))) (< 0 (+ (* 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) m (* (div n 256) 128) 129)) (< 127 (+ m (* (div n 256) 512) (* 256 (div n 128)))) (< 0 (+ (div n 256) 3 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 4))) (< 0 (+ m (* (div (+ (- 2) (div n 256)) 3) 512) 129)) (< 0 (+ 2 (div n 128) (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 2))) (< 0 (+ m 129 (* (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 512))) (< 0 (+ (* 2 (div (+ m (* 256 (div n 256)) (- 128)) 512)) 2 (div n 256))) (< 0 (+ m 513 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 768) (* 256 (div n 128)))) (< 0 (+ (* 2 (div m 128)) 2 (div n 128) (* 2 (div (+ n (- 128)) 256)))) (< 0 (+ 3 (* (div (+ m (- 128)) 256) 4) (* 5 (div n 256)))) (< 0 (+ (* (div n 256) 4) 3 (div n 128) (* (div (+ m (- 128)) 256) 4))) (< 0 (+ (* 2 (div (+ m (- 384)) 768)) 2 (div n 256))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 512))) (< 0 (+ (* (div (+ m (- 256) (* 256 (div n 256))) 768) 4) 3 (div n 128))) (< 0 (+ m (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 256) 1)) (< 0 (div n 256)) (< 0 (+ (div n 256) 3 (* (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 4))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (- 256) (* 256 (div n 128))) 512) 512))) (< 0 (+ n 129 (* 256 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)))) (< 0 (+ m (* (div n 256) 128) 129 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 256))) (< 0 (+ m (* 128 (div (+ m (- 128)) 256)) 129 (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ m (* 128 (div n 128)) (* 256 (div (+ n (- 128)) 256)) 129 (* 256 (div (+ m 128) 256)))) (< 0 (+ m (* (div (+ m (- 256) (* 256 (div n 256))) 768) 512) (* 256 (div (+ n (- 128)) 256)) 513)) (< 0 (+ m 129 (* (div (+ m (* 256 (div n 256)) (- 128)) 512) 512))) (< 0 (+ (* 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) m (* 256 (div n 256)) 129)) (< 0 (+ (* 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) m 129 (* 256 (div n 128)))) (< 0 (+ m (* 128 (div n 128)) 129 (* 256 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)))) (< 0 (+ m (* (div (+ m (- 256) (* 256 (div n 128))) 512) 256) (* (div n 256) 128) 129)) (< 0 (+ m 385 (* 256 (div (+ m 128) 256)) (* (div (+ n (- 128)) 256) 512))) (< 0 (+ 257 (* (div n 256) 512) (* (div (+ m (- 128)) 256) 512) n)) (< 0 (+ (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 1)) (< 0 (+ 3 (* 3 (div (+ (- 2) (div n 256)) 3)) (div (+ n (- 128)) 256))) (< 0 (+ m (* (div n 256) 512) (* 256 (div (+ m (- 128)) 256)) 129)) (< 0 (+ 257 m (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 768))) (< 255 (+ n (* (div (+ n (- 128)) 256) 512))) (< 0 (+ m 513 (* (div (+ m 128) 256) 512) (* 768 (div (+ n (- 128)) 256)))) (< 0 (+ (div n 256) 3 (* (div (+ m (- 256)) 512) 4))) (< 0 (+ (div (+ (- 2) (div n 256)) 3) 1)) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (* 128 (div (+ n (- 128)) 256))) 256) 512))) (< 0 (+ m (* 256 (div (+ m (- 128)) 256)) (* (div n 256) 128) 129 (* 256 (div n 128)))) (< 0 (+ m (* 128 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) 129 (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ m 129 (* 256 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) (* 256 (div n 128)))) (< 0 (+ m 513 (* 256 (div n 128)) (* 768 (div (+ m (- 256) (* 256 (div n 256))) 768)))) (< 0 (+ 2 (div n 256) (* 2 (div (+ m (- 256) (* 256 (div n 256))) 768)))) (< 0 (+ m (* 256 (div (+ m (- 256)) 512)) 129 (* 256 (div n 128)))) (< 0 (+ m (* (div n 256) 512) (* (div (+ m (- 128)) 256) 512) 129)) (< 0 (+ 2 (div n 256) (* 2 (div (+ m (- 512)) 1024)))) (< 0 (+ 2 (* (div n 256) 3) (* 2 (div (+ m (- 128)) 256)))) (< 0 (+ (div n 256) (div (+ m (- 128)) 256) 1)) (< 127 (+ m (* 256 (div n 256)) (* 256 (div m 128)) (* 256 (div n 128)))) (< 0 (+ m 129 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 256) (* 256 (div n 128)))) (< 0 (+ m (* 256 (div n 256)) 385 (* (div (+ m (- 256) (* 256 (div n 128))) 512) 512))) (< 0 (+ (* 256 (div (+ m (- 128)) 256)) n 129)) (< 0 (+ (* 5 (div n 128)) 3 (* (div (+ m (- 128)) 256) 4))) (< 0 (+ 3 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 4) (div n 128))) (< 0 (+ 257 m (* 768 (div (+ m (- 384)) 768)))) (< 0 (+ m (* (div (+ (- 2) (div n 256)) 3) 512) 385 (* 256 (div n 128)))) (< 0 (+ m (* 128 (div n 128)) (* 256 (div (+ m (- 128)) 256)) (* 256 (div n 256)) 129)) (< 0 (+ (* 256 (div (+ (- 2) (div n 256)) 3)) m 1)) (< 0 (+ m 513 (* 256 (div n 256)) (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 768))) (< 0 (+ (div (+ (- 1) (div (+ n (- 128)) 256)) 2) (div n 256))) (< 0 (+ 3 (div n 128) (* (div (+ m (* (div n 256) 128) (- 128)) 384) 4))) (< 0 (+ m 129 (* 256 (div (+ m (- 384)) 768)) (* 256 (div n 128)))) (< 0 (+ m (* (div (+ m (- 384)) 768) 512) (* 256 (div n 256)) 385)) (< 0 (+ m (* 128 (div n 128)) 129 (* 256 (div (+ m (- 512)) 1024)))) (< 0 (+ m (* (div n 256) 128) 129 (* 256 (div (+ m (- 384)) 768)))) (< 0 (+ (* 256 (div (+ m (- 256) (* 256 (div n 256))) 768)) m (* 256 (div (+ n (- 128)) 256)) 385)) (< 0 (+ m (* 256 (div (+ m (* (div n 256) 128) (- 128)) 384)) 1)) (< 0 (+ 257 n (* (div (+ m (- 256) (* 256 (div n 128))) 512) 512))) (< 0 (+ (div (+ m (- 128)) 256) (* 2 (div n 256)))) (< 0 (+ n 129 (* 256 (div (+ m (- 512)) 1024)))) (< 0 (+ m (* (div (+ m (- 256) (* 256 (div n 128))) 512) 256) (* 256 (div n 256)) 129)) (< 0 (+ m (* 128 (div n 128)) 129 (* 256 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)))) (< 127 (+ m (* (div n 256) 384) (* 256 (div m 128)))) (< 0 (+ (* (div (+ m (* (div n 256) 128) (- 128)) 384) 512) 257 n)) (< 0 (+ 2 (div n 256) (* 2 (div (+ m (- 256)) 512)))) (< 0 (+ 2 (div n 256) (* 2 (div n 128)) (* 2 (div (+ m (- 128)) 256)))) (< 0 (+ (div n 256) 3 (* (div (+ (- 2) (div n 256)) 3) 4))) (< 0 (+ 257 n (* (div m 128) 512) (* (div (+ n (- 128)) 256) 512))) (< 0 (+ 257 (* (div (+ m (- 256)) 512) 512) n)) (< 0 (+ m (* 256 (div (+ m (- 128)) 256)) (* 256 (div (+ n (- 128)) 256)) 385 (* 256 (div n 128)))) (< 0 (+ m (* (div (+ m (- 128)) 256) 512) 129)) (< 0 (+ 3 (* (div (+ m (- 256) (* 256 (div n 128))) 512) 3) (div (+ n (- 128)) 256))) (< 0 (+ (* 2 (div m 128)) (div n 128) (* 2 (div n 256)))) (< 0 (+ m (* 128 (div n 128)) 129 (* 256 (div (+ m (* 256 (div n 256)) (- 128)) 512)))) (< 0 (+ m (* 256 (div (+ m (- 128)) 256)) (* (div n 128) 384) 129)) (< 0 (+ m (* 768 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) 513 (* 256 (div n 256)))) (< 255 (+ (* (div n 256) 512) n)) (< 0 (+ (* (div (+ m (- 256) (* 256 (div n 128))) 512) 2) 2 (div n 128))) (< 0 (+ m (* 256 (div (+ m (- 128)) 256)) (* 256 (div (+ n (- 128)) 256)) (* 256 (div n 256)) 385)) (< 0 (+ (* 4 (div m 128)) (div n 256) 3 (* (div (+ n (- 128)) 256) 4))) (< 0 (+ m 513 (* 768 (div (+ m (- 384)) 768)) (* 256 (div n 128)))) (< 0 (+ m 513 (* 768 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)) (* 256 (div n 128)))) (< 0 (+ 3 (* 4 (div (+ m (- 384)) 768)) (div n 128))) (< 0 (+ m (* (div n 256) 128) 129 (* 256 (div (+ m (- 512)) 1024)))) (< 0 (+ n 129 (* 256 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)))) (< 127 (+ m (* 128 (div n 128)) (* 256 (div n 256)) (* 256 (div m 128)))) (< 0 (+ m (* (div (+ m (- 256) (* 256 (div n 128))) 512) 256) 129 (* 256 (div n 128)))) (< 0 (+ m (* 128 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)) 129 (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ m 129 (* 256 (div (+ m (* 256 (div n 256)) (- 128)) 512)) (* 256 (div n 128)))) (< 0 (+ (div (+ m (- 256) (* 256 (div n 128))) 512) 1)) (< 0 (+ 3 (* 3 (div (+ m (* 256 (div n 256)) (- 128)) 512)) (div (+ n (- 128)) 256))) (< 0 (+ 3 (* 3 (div (+ m 128) 256)) (* (div (+ n (- 128)) 256) 4))) (< 0 (+ m (* (div (+ m (- 256) (* 256 (div n 256))) 768) 128) 129 (* 128 (div (+ n (- 128)) 256)))) (< 0 (+ (div (+ m (- 128)) 256) 1)) (< 0 (+ (* 2 (div m 128)) (* 3 (div (+ n (- 128)) 256)) 2)) (< 0 (+ (div n 256) (div (+ m (- 384)) 768))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div n 256)) (* 256 (div m 128)) 129)) (< 0 (+ 2 (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 2) (div (+ n (- 128)) 256))) (< 0 (+ 2 (div n 128) (* 2 (div (+ m (- 128)) 256)) (* 2 (div n 256)))) (< 0 (+ m 513 (* 256 (div n 256)) (* 768 (div (+ m (- 384)) 768)))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (* 128 (div n 128)) (- 128)) 256) 512))) (< 0 (+ m (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 512) (* 256 (div n 256)) 385)) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* (div n 256) 128) (* 256 (div m 128)) 129)) (< 0 (+ (* (div (+ m (* (div n 256) 128) (- 128)) 384) 512) m (* 256 (div n 256)) 385)) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 385 (* 256 (div (+ m (* 256 (div n 256)) (- 128)) 512)))) (< 127 (+ m (* (div n 256) 512) (* 256 (div m 128)))) (< 0 (+ 257 (* (div (+ m (- 128)) 256) 512) n (* (div n 128) 512))) (< 1 (+ (* 2 (div n 256)) (div m 128))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (- 128)) 256) 512) (* (div n 128) 512))) (< 0 (+ (div (+ m (* 128 (div (+ n (- 128)) 256))) 256) 1)) (< 0 (+ (div n 256) 3 (* 4 (div (+ m (- 384)) 768)))) (< 0 (+ m (* (div n 256) 128) 129 (* 256 (div (+ m (* 256 (div n 256)) (- 128)) 512)))) (< 0 (+ 2 (* 2 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) (div n 128))) (< 383 (+ m (* (div n 256) 512) (* (div m 128) 512))) (< 0 (+ (* 256 (div (+ (- 2) (div n 256)) 3)) m (* 128 (div n 128)) 129)) (< 0 (+ m (* 768 (div (+ m (- 128)) 256)) 513 (* (div n 256) 1024))) (< 0 (+ 257 m (* 768 (div (+ m (- 256) (* 256 (div n 256))) 768)))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* 256 (div (+ m 128) 256)) 1)) (< 0 (+ m (* 256 (div n 256)) (* (div (+ m (* 128 (div (+ n (- 128)) 256))) 256) 512) 385)) (< 0 (+ m (* (div (+ m (- 128)) 256) 512) 385 (* 768 (div n 128)))) (< 0 (+ m (* 128 (div n 128)) 129 (* 256 (div (+ m (- 384)) 768)))) (< 0 (+ 2 (* 2 (div (+ m (- 128)) 256)) (div (+ n (- 128)) 256))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) (* (div (+ m 128) 256) 128) 129)) (< 0 (+ m 513 (* 768 (div (+ m (- 256)) 512)) (* 256 (div n 256)))) (< 0 (+ m (* (div (+ m (- 256) (* 256 (div n 256))) 768) 512) 385 (* 256 (div n 128)))) (< 0 (+ 3 (div n 128) (* 4 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)))) (< 0 (+ (* 4 (div m 128)) 3 (div n 128) (* (div (+ n (- 128)) 256) 4))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 385 (* 256 (div (+ m (* 256 (div (+ n (- 128)) 256))) 512)))) (< 0 (+ (div (+ m (- 256) (* 256 (div n 128))) 512) (div n 256))) (< 0 (+ m (* 256 (div (+ m (- 256)) 512)) 1)) (< 1 (+ (* 4 (div m 128)) (* 5 (div n 256)))) (< 0 (+ m (* 256 (div (+ n (- 128)) 256)) 513 (* (div (+ m (* 256 (div (+ n (- 128)) 256))) 512) 512))) (< 0 (+ m (* 256 (div n 256)) 129 (* 256 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)))) (< 0 (+ m 129 (* (div (+ m (- 512)) 1024) 512))) (< 0 (+ (* 256 (div (+ (- 2) (div n 256)) 3)) m (* 256 (div n 256)) 129)) (< 0 (+ m (* (div (+ m (- 384)) 768) 512) 385 (* 256 (div n 128)))) (< 0 (+ m (* (div n 256) 384) (* 256 (div (+ m (- 128)) 256)) 129)) (< 0 (+ (* 3 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)) 3 (div (+ n (- 128)) 256))) (< 0 (+ 2 (div (+ m (* (div n 256) 128) (- 128)) 384) (div (+ n (- 128)) 256))) (< 0 (+ m 129 (* 256 (div (+ m (* (div n 256) 128) (- 128)) 384)) (* 256 (div n 128)))) (< 0 (+ m 513 (* 256 (div n 256)) (* 768 (div (+ m 128) 256)) (* 768 (div (+ n (- 128)) 256)))) (< 0 (+ 257 m (* 768 (div (+ m (* 128 (div (+ n (- 128)) 256))) 256)))))";
		final String simplified =
				"(or (< 0 (+ 2 (div n 128) (* (div (+ (- 1) (div (+ n (- 128)) 256)) 2) 2))) (< 0 (+ (div (+ m (- 128)) 256) 1)))";
		runSimplificationTest(funDecls, formulaAsString, simplified, SimplificationTechnique.SIMPLIFY_DDA, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	@Test
	public void bvToIntFoxExists04AfterTir() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "v_y_3", "v", "m", "n") };
		final String formulaAsString =
				"(let ((.cse54 (* m (- 1)))) (let ((.cse53 (+ .cse54 127))) (let ((.cse32 (div (+ .cse54 255) 256)) (.cse16 (div .cse53 256)) (.cse18 (div .cse53 128))) (let ((.cse4 (* 768 v)) (.cse40 (* 128 .cse18)) (.cse27 (* 2 v_y_3)) (.cse29 (* 128 .cse16)) (.cse39 (* 256 .cse18)) (.cse10 (* 256 v)) (.cse34 (* .cse32 128)) (.cse5 (* v_y_3 512)) (.cse22 (* v 512)) (.cse41 (* 256 .cse16)) (.cse21 (* .cse32 256)) (.cse2 (* 256 v_y_3))) (let ((.cse0 (+ .cse21 .cse2 127)) (.cse9 (+ 383 .cse2)) (.cse13 (+ .cse41 127)) (.cse15 (+ .cse5 n .cse22)) (.cse37 (* v 4)) (.cse44 (+ 255 .cse2)) (.cse50 (+ .cse34 127)) (.cse51 (+ .cse10 383)) (.cse24 (+ n .cse22 .cse2)) (.cse19 (+ .cse39 .cse2 127)) (.cse6 (+ .cse29 127)) (.cse42 (+ .cse41 .cse2 127)) (.cse47 (* v 1024)) (.cse7 (+ v v_y_3)) (.cse30 (* v 128)) (.cse31 (* v_y_3 128)) (.cse38 (+ .cse27 .cse18)) (.cse43 (+ 255 .cse39 .cse2)) (.cse14 (+ .cse40 .cse2 127)) (.cse12 (+ n .cse22)) (.cse8 (+ .cse10 n)) (.cse20 (+ .cse10 n .cse2)) (.cse48 (+ .cse10 m)) (.cse25 (+ .cse4 n)) (.cse23 (* v_y_3 4)) (.cse35 (+ .cse5 .cse39 127)) (.cse3 (+ .cse39 127)) (.cse46 (+ .cse10 .cse5 n)) (.cse49 (+ .cse2 127)) (.cse1 (* 1280 v)) (.cse11 (+ .cse4 n .cse2)) (.cse26 (+ .cse40 127)) (.cse17 (* 2 v)) (.cse36 (+ n .cse2)) (.cse45 (* 3 v)) (.cse52 (* 3 v_y_3)) (.cse33 (+ .cse27 .cse18 1)) (.cse28 (* 768 v_y_3))) (and (<= n .cse0) (<= (+ .cse1 n .cse2) .cse3) (<= n (+ .cse4 .cse5 639)) (<= n .cse6) (<= 0 .cse7) (<= .cse8 .cse9) (<= n (+ .cse10 383 .cse2)) (<= .cse8 .cse0) (<= .cse11 .cse3) (<= .cse12 .cse13) (<= n .cse14) (<= .cse11 127) (<= .cse15 255) (<= 0 (+ v v_y_3 .cse16)) (<= .cse17 .cse18) (<= .cse12 .cse19) (<= .cse20 .cse13) (<= n (+ .cse10 .cse21 .cse2 127)) (<= .cse8 .cse13) (<= n (+ .cse5 .cse22 639)) (<= 0 (+ .cse17 .cse23 .cse18 1)) (<= .cse24 .cse3) (<= 0 .cse16) (<= .cse25 .cse19) (<= n .cse9) (<= .cse12 .cse26) (<= 0 (+ .cse27 v 1)) (<= n (+ .cse4 255 .cse21 .cse28)) (<= n (+ .cse29 .cse30 .cse31 127)) (<= .cse11 .cse13) (<= v (+ v_y_3 .cse16)) (<= 0 (+ .cse32 .cse27)) (<= .cse17 .cse33) (<= .cse24 127) (<= .cse20 .cse3) (<= .cse20 383) (<= n (+ .cse5 .cse21 .cse22 127)) (<= .cse24 .cse13) (<= n (+ .cse34 .cse2 127)) (<= .cse12 .cse35) (<= .cse36 255) (<= .cse20 .cse6) (<= n 127) (<= n (+ .cse10 .cse34 .cse2 127)) (<= n (+ .cse22 .cse2 639)) (<= n .cse19) (<= n (+ 383 .cse22)) (<= (+ .cse31 n (* v 384)) .cse6) (<= (+ .cse30 .cse31 n) .cse6) (<= 0 (+ .cse37 .cse23 .cse18 1)) (<= 0 .cse38) (<= m (+ .cse10 .cse2 127)) (<= .cse17 .cse16) (<= n .cse13) (<= n (+ .cse5 383 .cse22)) (<= (+ .cse5 n) 383) (<= .cse15 383) (<= .cse8 (+ 255 .cse39 .cse28)) (<= .cse8 127) (<= 0 .cse18) (<= n (+ .cse40 .cse10 .cse2 127)) (<= .cse36 (+ .cse10 511)) (<= n (+ .cse5 .cse41 255 .cse22)) (<= .cse8 .cse26) (<= n (+ .cse10 255 .cse2)) (<= n (+ .cse5 .cse39 .cse22 127)) (<= .cse8 .cse42) (<= .cse8 .cse35) (<= .cse8 (+ .cse41 255 .cse2)) (<= .cse8 .cse43) (<= .cse37 .cse18) (<= 0 (+ v v_y_3 1)) (<= .cse8 .cse44) (<= n (+ .cse5 383)) (<= (+ m .cse22) 127) (<= 0 (+ .cse32 .cse37 .cse23 1)) (<= 0 (+ .cse27 .cse16 .cse17 1)) (<= 0 (+ .cse45 .cse27 1)) (<= .cse46 383) (<= .cse12 127) (<= n (+ .cse10 .cse5 .cse39 127)) (<= n (+ .cse47 .cse5 639)) (<= 0 (+ .cse27 .cse16 1)) (<= n (+ .cse10 255)) (<= n .cse26) (<= (+ .cse47 n .cse2) .cse3) (<= n (+ .cse10 .cse5 383)) (<= .cse24 .cse6) (<= .cse48 .cse49) (<= 0 (+ .cse32 .cse17 .cse23 1)) (<= (+ .cse10 n .cse28) 383) (<= n .cse50) (<= n (+ .cse5 .cse21 127)) (<= n .cse44) (<= m (+ .cse5 255)) (<= n .cse51) (<= n (+ .cse4 511 .cse2)) (<= 0 (+ v 1)) (<= .cse8 .cse50) (<= n (+ .cse10 255 .cse39 .cse2)) (<= .cse36 .cse51) (<= .cse20 511) (<= v 0) (<= .cse24 .cse26) (<= .cse8 .cse19) (<= n (+ .cse4 767 .cse28)) (<= n (+ 383 .cse22 .cse2)) (<= .cse8 .cse6) (<= (+ .cse4 n .cse28) 383) (<= n .cse42) (<= n (+ .cse10 .cse41 255 .cse2)) (<= (+ .cse47 n) .cse3) (<= .cse20 127) (<= .cse7 0) (<= 0 (+ .cse27 .cse17 .cse18)) (<= n (+ .cse10 255 .cse39 .cse28)) (<= n (+ .cse10 511 .cse28)) (<= n 383) (<= (+ .cse30 n) (+ .cse29 .cse31 127)) (<= .cse17 .cse38) (<= .cse8 255) (<= n (+ .cse4 511 .cse28)) (<= v_y_3 0) (<= .cse25 .cse43) (<= 0 v) (<= n (+ .cse10 .cse2 639)) (<= .cse20 255) (<= 0 (+ .cse27 .cse17 .cse18 1)) (<= n (+ .cse10 511 .cse2)) (<= .cse8 .cse14) (<= (+ n .cse22 .cse28) 383) (<= n (+ .cse10 .cse5 .cse21 127)) (<= .cse12 .cse3) (<= .cse8 .cse3) (<= n (+ .cse10 .cse39 .cse2 127)) (<= n 255) (<= .cse20 .cse26) (<= .cse48 127) (<= .cse25 .cse3) (<= 0 (+ .cse23 .cse18 1)) (<= 0 (+ .cse52 v .cse16 1)) (<= 0 (+ v_y_3 .cse17 1)) (<= n (+ .cse5 .cse41 255)) (<= n .cse35) (<= n .cse3) (<= .cse46 255) (<= n (+ .cse10 .cse41 .cse2 127)) (<= m .cse49) (<= n (+ .cse4 255 .cse39 .cse28)) (<= m (+ .cse5 255 .cse22)) (<= n (+ 767 .cse1 .cse28)) (<= n (+ .cse4 .cse2 639)) (<= 0 v_y_3) (<= .cse11 .cse26) (<= 0 (+ .cse32 .cse27 .cse17)) (<= .cse36 383) (<= 0 (+ .cse45 .cse52 .cse16 1)) (<= 0 .cse33) (<= n (+ .cse10 255 .cse21 .cse28))))))))";
		final String simplified =
				"(let ((.cse0 (+ v v_y_3))) (and (<= 0 v) (<= .cse0 0) (<= 0 .cse0) (<= v (+ v_y_3 (div (+ (* m (- 1)) 127) 256))) (<= v 0) (<= (+ n (* v 256)) 127)))";
		runSimplificationTest(funDecls, formulaAsString, simplified, SimplificationTechnique.SIMPLIFY_DDA, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	/**
	 * Result is suboptimal with SIMPLIFY_DDA because we do not apply constant folding. Result is suboptimal with
	 * POLY_PAC because cannot simplify the atoms with `mod`. During the verification, the quantifier elimination
	 * simplified this formula insufficiently and SIMPLIFY_DDA could reduce the size furthermore. After dumping the
	 * formula this was not reproducible. (Quantifier elimination provided even a better result than SIMPLIFY_DDA
	 * because of the constant folding.)
	 */
	@Test
	public void creditSuisse01() {
		final FunDecl[] funDecls = new FunDecl[] { new FunDecl(SmtSortUtils::getIntSort, "x", "y", "z"), };
		final String formulaAsString =
				"(and (or (= (mod (+ x 1) 2) 0) (and (or (< (+ (div x 2) 1) 0) (< (* 2 z) (+ 2 x))) (or (< (+ 2 x) 0) (< x (+ 2 (* 2 z)))))) (<= x 2) (< 0 y) (= z 1) (or (and (or (< (+ x 1) 0) (< x (+ (* 2 z) 1))) (or (< (* 2 z) (+ 3 x)) (< (div (+ x 1) 2) 0))) (= (mod x 2) 0)))";
		final String simplified = "(and (= z 1) (< 0 y) (or (< (* 2 z) (+ 2 x)) (< (+ (div x 2) 1) 0)) (<= x 2))";
		runSimplificationTest(funDecls, formulaAsString, simplified, SimplificationTechnique.SIMPLIFY_DDA, mServices,
				mLogger, mMgdScript, mCsvWriter);
	}

	static void runSimplificationTest(final FunDecl[] funDecls, final String eliminationInputAsString,
			final String expectedResultAsString, final SimplificationTechnique simplificationTechnique,
			final IUltimateServiceProvider services, final ILogger logger, final ManagedScript mgdScript,
			final QuantifierEliminationTestCsvWriter csvWriter) {
		for (final FunDecl funDecl : funDecls) {
			funDecl.declareFuns(mgdScript.getScript());
		}
		final Term formulaAsTerm = TermParseUtils.parseTerm(mgdScript.getScript(), eliminationInputAsString);
		final Term letFree = new FormulaUnLet().transform(formulaAsTerm);
		final Term unf = new UnfTransformer(mgdScript.getScript()).transform(letFree);

		final String testId = ReflectionUtil.getCallerMethodName(3);
		csvWriter.reportEliminationBegin(letFree, testId);
		final ExtendedSimplificationResult esr =
				SmtUtils.simplifyWithStatistics(mgdScript, unf, services, simplificationTechnique);
		// final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(mgdScript, unf, services,
		// SimplificationTechnique.SIMPLIFY_DDA2);
		final Term result = esr.getSimplifiedTerm();
		logger.info("Simplified result: " + esr.getSimplifiedTerm());
		logger.info(esr.buildSizeReductionMessage());
		logger.info("CDC code input:  " + CondisDepthCode.of(unf));
		logger.info("CDC code output: " + CondisDepthCode.of(result));
		csvWriter.reportEliminationSuccess(result, testId, (StatisticsScript) mgdScript.getScript());
		if (expectedResultAsString != null) {
			final CommuhashNormalForm cnft = new CommuhashNormalForm(services, mgdScript.getScript());
			final Term cnfResult = cnft.transform(result);
			final Term expectedResultAsTerm = TermParseUtils.parseTerm(mgdScript.getScript(), expectedResultAsString);
			final Term cnfExpectedResultAsTerm = cnft.transform(expectedResultAsTerm);
			MatcherAssert.assertThat(cnfResult, IsEqual.equalTo(cnfExpectedResultAsTerm));
		}
		checkLogicalEquivalence(mgdScript.getScript(), result, formulaAsTerm);
	}

	private static void checkLogicalEquivalence(final Script script, final Term result, final Term input) {
		script.echo(new QuotedObject("Start correctness check for simplification."));
		final LBool lbool = SmtUtils.checkEquivalence(result, input, script);
		script.echo(new QuotedObject("Finished correctness check for simplification. Result: " + lbool));
		final String errorMessage;
		switch (lbool) {
		case SAT:
			errorMessage = "Not equivalent to expected result: " + result;
			break;
		case UNKNOWN:
			errorMessage = "Insufficient ressources for checking equivalence to expected result: " + result;
			break;
		case UNSAT:
			errorMessage = null;
			break;
		default:
			throw new AssertionError("unknown value " + lbool);
		}
		MatcherAssert.assertThat(errorMessage, lbool == LBool.UNSAT);
	}

}
