package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.IOException;

import org.hamcrest.MatcherAssert;
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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.StatisticsScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.egraph.EGraph;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class EGraphTest {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY = false;
	private static final long TEST_TIMEOUT_MILLISECONDS = 200_000_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
//	private static final String SOLVER_COMMAND = "cvc4 --incremental --lang smt";
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -memory:2024 -smt2 -in";
	// private static final String SOLVER_COMMAND = "INTERNAL_SMTINTERPOL:10000";

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private static QuantifierEliminationTestCsvWriter mCsvWriter;

	@BeforeClass
	public static void beforeAllTests() {
//		mCsvWriter = new QuantifierEliminationTestCsvWriter(SimplificationTest.class.getSimpleName());
	}

	@AfterClass
	public static void afterAllTests() {
//		if (WRITE_BENCHMARK_RESULTS_TO_WORKING_DIRECTORY) {
//			try {
////				mCsvWriter.writeCsv();
//			} catch (final IOException e) {
//				throw new AssertionError(e);
//			}
//		}
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
//		mCsvWriter.reportTestFinished();
	}

//	@Test
//	public void ddaExample6() {
//		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x"), };
//		final String formulaAsString = "(and (distinct x 1) (or (<= x 0) (> x 2) (= x 1)))";
//		final String expectedResultAsString = "(and (not (= x 1)) (or (< 2 x) (< x 1)))";
//		runEGraphTest(funDecls, formulaAsString, expectedResultAsString, mServices, mLogger, mMgdScript);
//	}

//	@Test
//	public void dda2TestExample01() {
//		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x", "y", "z"), };
//		final String formulaAsString =
//				"(or (and (or (> x 1) (= (+ y z) 1)) (<= y 2)) (and (< x 2) (or (< x 5) (>= z 2))))";
//		final String expectedResultAsString = "(or (< y 3) (< x 2))";
//		runEGraphTest(funDecls, formulaAsString, expectedResultAsString, mServices, mLogger, mMgdScript);
//	}

	@Test
	public void egraphTestExample01() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x", "y", "z"), };
		final String formulaAsString = "(and (= x y) (= y 5) (= (+ x 5) z))";
		final String expectedResultAsString = "(or (< y 3) (< x 2))";
		runEGraphTest(funDecls, formulaAsString, expectedResultAsString, mServices, mLogger, mMgdScript);
	}

	static void runEGraphTest(final FunDecl[] funDecls, final String eliminationInputAsString,
			final String expectedResultAsString, final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript) {
		for (final FunDecl funDecl : funDecls) {
			funDecl.declareFuns(mgdScript.getScript());
		}
		final Term formulaAsTerm = TermParseUtils.parseTerm(mgdScript.getScript(), eliminationInputAsString);
		final Term letFree = new FormulaUnLet().transform(formulaAsTerm);
		final Term unf = new UnfTransformer(mgdScript.getScript()).transform(letFree);

		final EGraph egraph = new EGraph(mgdScript, services);
		egraph.addFormula(unf);
	}

	private static boolean checkLogicalEquivalence(final Script script, final Term result, final Term input) {
		script.echo(new QuotedObject("Start correctness check for simplification."));
		final LBool lbool = SmtUtils.checkEquivalence(result, input, script);
		script.echo(new QuotedObject("Finished correctness check for simplification. Result: " + lbool));
		final String errorMessage;
		switch (lbool) {
		case SAT:
			errorMessage = "Not logically equivalent to expected result: " + result;
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
		return lbool == LBool.UNSAT;
	}
}