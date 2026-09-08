package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.IOException;
import java.util.ArrayList;

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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.StatisticsScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.egraph.EGraph;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.UnfTransformer;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class EGraphTest {

	/**
	 * Warning: each test will overwrite the SMT script of the preceding test.
	 */
	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final long TEST_TIMEOUT_MILLISECONDS = 200_000_000;
	private static final LogLevel LOG_LEVEL = LogLevel.INFO;
//	private static final String SOLVER_COMMAND = "cvc4 --incremental --lang smt";
	private static final String SOLVER_COMMAND = "z3 SMTLIB2_COMPLIANT=true -memory:2024 -smt2 -in";
	// private static final String SOLVER_COMMAND = "INTERNAL_SMTINTERPOL:10000";

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;

	@BeforeClass
	public static void beforeAllTests() {
	}

	@AfterClass
	public static void afterAllTests() {
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
	}

	private static record ExpectedRelation(String term1, String term2, EGraph.EquivalenceState relation) {
	}

	@Test
	// most basic transitivity test
	public void egraphTestExampleTransitivity() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x", "y", "z"), };
		final String formulaAsString = "(and (= x y) (= y 5))";
		final ArrayList<ExpectedRelation> expectedRelations = new ArrayList<>();
		expectedRelations.add(new ExpectedRelation("x", "5", EGraph.EquivalenceState.EQUAL));
		runEGraphTest(funDecls, formulaAsString, expectedRelations, mServices, mLogger, mMgdScript);
	}

	@Test
	// basic select congruence test with the same arrays and indices that are found to be equivalent
	public void egraphTestExampleSelectCongruence() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "i", "j", "x", "y"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "a"), };
		final String formulaAsString = "(and (= i (select a x)) (= x y) (= j (select a y)))";
		final ArrayList<ExpectedRelation> expectedRelations = new ArrayList<>();
		expectedRelations.add(new ExpectedRelation("i", "j", EGraph.EquivalenceState.EQUAL));
		expectedRelations.add(new ExpectedRelation("(select a x)", "(select a y)", EGraph.EquivalenceState.EQUAL));
		runEGraphTest(funDecls, formulaAsString, expectedRelations, mServices, mLogger, mMgdScript);
	}

	@Test
	// basic select congruence test with the same indices and arrays that are found to be equivalent
	public void egraphTestExampleSelectCongruence02() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "i", "j", "x"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "a", "b"), };
		final String formulaAsString = "(and (= i (select a x)) (= a b) (= j (select b x)))";
		final ArrayList<ExpectedRelation> expectedRelations = new ArrayList<>();
		expectedRelations.add(new ExpectedRelation("i", "j", EGraph.EquivalenceState.EQUAL));
		expectedRelations.add(new ExpectedRelation("(select a x)", "(select b x)", EGraph.EquivalenceState.EQUAL));
		runEGraphTest(funDecls, formulaAsString, expectedRelations, mServices, mLogger, mMgdScript);
	}

	@Test
	// basic select congruence test where both the indices and arrays are found to be equivalent
	public void egraphTestExampleSelectCongruence03() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "i", "j", "x", "y"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "a", "b"), };
		final String formulaAsString = "(and (= i (select a x)) (= a b) (= x y) (= j (select b y)))";
		final ArrayList<ExpectedRelation> expectedRelations = new ArrayList<>();
		expectedRelations.add(new ExpectedRelation("i", "j", EGraph.EquivalenceState.EQUAL));
		expectedRelations.add(new ExpectedRelation("(select a x)", "(select b y)", EGraph.EquivalenceState.EQUAL));
		runEGraphTest(funDecls, formulaAsString, expectedRelations, mServices, mLogger, mMgdScript);
	}

	@Test
	// nested select congruence test
	// note that replacing the variable j by y causes this test to fail
	public void egraphTestExampleSelectCongruence04p5() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x", "j"),
				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "a"), };
		final String formulaAsString = "(and (= x (select a x)) (= j (select a (select a x))))";
		final ArrayList<ExpectedRelation> expectedRelations = new ArrayList<>();
		expectedRelations.add(new ExpectedRelation("(select a (select a x))", "x", EGraph.EquivalenceState.EQUAL));
		runEGraphTest(funDecls, formulaAsString, expectedRelations, mServices, mLogger, mMgdScript);
	}

	@Test
	// most basic disequality test
	public void egraphTestExampleDistinct() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x", "y", "z"), };
		final String formulaAsString = "(and (distinct x y) (= y z))";
		final ArrayList<ExpectedRelation> expectedRelations = new ArrayList<>();
		expectedRelations.add(new ExpectedRelation("x", "z", EGraph.EquivalenceState.DISTINCT));
		runEGraphTest(funDecls, formulaAsString, expectedRelations, mServices, mLogger, mMgdScript);
	}

	@Test
	// basic disequality test to see if we are adding nonimplied disequalities
	public void egraphTestExampleDistinct02() {
		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "x", "y", "z"), };
		final String formulaAsString = "(and (distinct x y) (distinct x z)))";
		final ArrayList<ExpectedRelation> expectedRelations = new ArrayList<>();
		expectedRelations.add(new ExpectedRelation("y", "z", EGraph.EquivalenceState.UNKNOWN));
		runEGraphTest(funDecls, formulaAsString, expectedRelations, mServices, mLogger, mMgdScript);
	}

//	@Test
//	// select disequality test, where distinct values should imply distinct indices
//	// this is currently not detectable
//	public void egraphTestExampleDistinctSelect03() {
//		final FunDecl[] funDecls = { new FunDecl(SmtSortUtils::getIntSort, "i", "j", "x", "y"),
//				new FunDecl(QuantifierEliminationTest::getArrayIntIntSort, "a"), };
//		final String formulaAsString = "(and (= i (select a x)) (not (= i j)) (= j (select a y)))";
//		final ArrayList<ExpectedRelation> expectedRelations = new ArrayList<>();
//		expectedRelations.add(new ExpectedRelation("x", "y", EGraph.EquivalenceState.DISTINCT));
//		runEGraphTest(funDecls, formulaAsString, expectedRelations, mServices, mLogger, mMgdScript);
//	}

	static void runEGraphTest(final FunDecl[] funDecls, final String conjunctAsString,
			final ArrayList<ExpectedRelation> expectedRelations, final IUltimateServiceProvider services,
			final ILogger logger, final ManagedScript mgdScript) {
		for (final FunDecl funDecl : funDecls) {
			funDecl.declareFuns(mgdScript.getScript());
		}
		final Term formulaAsTerm = TermParseUtils.parseTerm(mgdScript.getScript(), conjunctAsString);
		final Term letFree = new FormulaUnLet().transform(formulaAsTerm);
		final Term unf = new UnfTransformer(mgdScript.getScript()).transform(letFree);

		final EGraph egraph = new EGraph(mgdScript, services);
		egraph.addFormula(unf);
		boolean allExpectedRelationsHold = true;
		for (final ExpectedRelation expectedRelation : expectedRelations) {
			final Term term1 = TermParseUtils.parseTerm(mgdScript.getScript(), expectedRelation.term1);
			final Term term2 = TermParseUtils.parseTerm(mgdScript.getScript(), expectedRelation.term2);
			final EGraph.EquivalenceState relationResult = egraph.getRelation(term1, term2);
			if (relationResult != expectedRelation.relation) {
				final String errorMessage = "Expected relation between " + term1 + " and " + term2 + ": "
						+ expectedRelation.relation + ", got: " + relationResult;
				MatcherAssert.assertThat(errorMessage, false);
				allExpectedRelationsHold = false;
			}
		}
		assert allExpectedRelationsHold;
	}
}