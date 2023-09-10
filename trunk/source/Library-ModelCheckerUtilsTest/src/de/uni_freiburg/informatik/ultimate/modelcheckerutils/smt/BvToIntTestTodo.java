package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.IOException;
import java.util.Set;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.experimental.categories.Category;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationConstrainer.ConstraintsForBitwiseOperations;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationManager;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.LoggingScriptForMainTrackBenchmarks;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.junitextension.categories.NoRegression;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 * @author Max Barth
 */
@Category(NoRegression.class)
public class BvToIntTestTodo {

	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_MAIN_TRACK_SCRIPT_IF_UNKNOWN_TO_FILE = false;

	private static final String SOLVER_COMMAND_Z3 =
			"z3 SMTLIB2_COMPLIANT=true -t:6000 -memory:2024 -smt2 -in smt.arith.solver=2";
	private static final String SOLVER_COMMAND_CVC4 = "cvc4 --incremental --print-success --lang smt --tlimit-per=6000";
	private static final String SOLVER_COMMAND_MATHSAT = "mathsat";
	/**
	 * If DEFAULT_SOLVER_COMMAND is not null we ignore the solver specified for each test and use only the solver
	 * specified here. This can be useful to check if there is a suitable solver for all tests and this can be useful
	 * for generating difficult SMT-LIB benchmarks.
	 */
	private static final String DEFAULT_SOLVER_COMMAND = null;

	private Script mScript;
	private IUltimateServiceProvider mServices;
	private ManagedScript mMgdScript;
	private ILogger mLogger;

	@Before
	public void setUp() throws Exception {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger("lol");
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);

	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	public static Sort getBitvectorSort8(final Script script) {
		return SmtSortUtils.getBitvectorSort(script, 8);
	}

	private Term parse(final String inputSTR) {
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, inputSTR);
		return formulaAsTerm;
	}

	private Term translateQelimBacktranslate(final Term input) {
		final TranslationManager translationManager =
				new TranslationManager(mMgdScript, ConstraintsForBitwiseOperations.SUM, false);
		final Triple<Term, Set<TermVariable>, Boolean> translated = translationManager.translateBvtoInt(input);
		if (!translated.getSecond().isEmpty() || translated.getThird()) {
			throw new UnsupportedOperationException();
		}
		// System.out.println("translatedResult: " + translated.toStringDirect());
		final Term qelimResult = PartialQuantifierElimination.eliminate(mServices, mMgdScript, translated.getFirst(),
				SimplificationTechnique.SIMPLIFY_DDA);
		// System.out.println("qelimResult: " + qelimResult.toStringDirect());
		final Term backTranslated = translationManager.translateIntBacktoBv(qelimResult);
		// System.out.println("backtransresult: " + backTranslated.toStringDirect());
		return backTranslated;
	}

	private void testQelim(final Term t1, final Term t2) {
		final Term qelimResult =
				PartialQuantifierElimination.eliminate(mServices, mMgdScript, t1, SimplificationTechnique.SIMPLIFY_DDA);

		final LBool equi = SmtUtils.checkEquivalence(t1, t2, mScript);
		Assert.assertFalse(String.format(
				"Insufficient ressources to check equivalence between input and output. Input: %s, Output %s", t1, t2),
				equi.equals(LBool.UNKNOWN));
		Assert.assertFalse(String.format("Input and output are not logically equivalent. Input: %s, Output %s", t1, t2),
				equi.equals(LBool.SAT));
		// System.out.println("bit-vector quantifier Elimination: " + qelimResult.toStringDirect());
		Assert.assertTrue("Result contains quantifiers", QuantifierUtils.isQuantifierFree(t2)); // translation qelim
		// Assert.assertTrue(QuantifierUtils.isQuantifierFree(qelimResult)); // bit-vector qelim

	}

	private void setUpScript(final String solverCommand, final VarDecl... varDecls) {
		final Script script = createSolver(solverCommand);
		script.setLogic(Logics.ALL);
		for (final VarDecl varDecl : varDecls) {
			varDecl.declareVars(script);
		}
		mScript = script;
		mMgdScript = new ManagedScript(mServices, script);
	}

	private Script createSolver(final String proviededSolverCommand) {
		String effectiveSolveCommand;
		if (DEFAULT_SOLVER_COMMAND != null) {
			effectiveSolveCommand = DEFAULT_SOLVER_COMMAND;
		} else {
			effectiveSolveCommand = proviededSolverCommand;
		}
		Script result = new HistoryRecordingScript(UltimateMocks.createSolver(effectiveSolveCommand, LogLevel.INFO));
		final String testName = ReflectionUtil.getCallerMethodName(4);
		if (WRITE_SMT_SCRIPTS_TO_FILE) {
			try {
				final String filename = testName + ".smt2";
				result = new LoggingScript(result, filename, true);
			} catch (final IOException e) {
				throw new AssertionError("IOException while constructing LoggingScript");
			}
		}
		if (WRITE_MAIN_TRACK_SCRIPT_IF_UNKNOWN_TO_FILE) {
			final String baseFilename = testName;
			result = new LoggingScriptForMainTrackBenchmarks(result, baseFilename, ".");
		}
		return result;
	}

	// @Test // TODO takes a long time and cannot eliminate all quantifiers
	public void BV_2017_Preiner_scholl_smt08_model_model_6_64() {
		final VarDecl[] funDecls = new VarDecl[] {
				new VarDecl(SmtSortUtils::getBoolSort, "bool.b22", "bool.b7", "bool.b5", "bool.b6", "bool.b23",
						"bool.b12", "bool.b8", "bool.b10", "bool.b14"),
				new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "x3", "x4", "x5"), };
		final String inputSTR =
				"(forall ((?lambda (_ BitVec 32))) (or (not (and (not (and (not (and bool.b6 (not (and (not (and (not (and (not (and (not bool.b12) (not bool.b5) (not bool.b14) (not (bvsle x3 (_ bv723 32))) (bvsle (bvadd x3 (bvmul (_ bv3 32) ?lambda) (bvmul (_ bv3 32) x5)) (_ bv50 32)) (bvsle x3 (_ bv1200 32)) (not bool.b10) (not bool.b8) (bvsle x3 (_ bv40 32)))) (not (bvsle x3 (_ bv0 32))))) (bvsle (bvadd (bvmul (_ bv4294967295 32) ?lambda) (bvmul (_ bv4294967295 32) x5)) (_ bv4294967286 32)) (not (and (not (and (not bool.b5) (not (bvsle (bvadd x4 (bvmul (_ bv60 32) ?lambda)) (_ bv4820 32))))) (bvsle x3 (_ bv0 32)))))) bool.b23)) (not (and (not bool.b23) (not (and (not (and (bvsle x3 (_ bv15 32)) (not (and (bvsle (bvadd x3 (bvmul (_ bv4294967287 32) ?lambda) (bvmul (_ bv4294967287 32) x5)) (_ bv1105 32)) (not (and (not (and (not (and (bvsle x3 (_ bv371 32)) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (not (bvsle x3 (_ bv723 32))) (bvsle x3 (_ bv1200 32)) (not bool.b10) (not bool.b8))))) (bvsle (bvadd (bvmul (_ bv4294967295 32) ?lambda) (bvmul (_ bv4294967295 32) x5)) (_ bv4294967286 32)) (not (and (not (bvsle x3 (_ bv371 32))) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (bvsle x3 (_ bv610 32)) (bvsle x3 (_ bv1200 32)) (not bool.b10) (not bool.b8) (bvsle x3 (_ bv30 32)))))))) (bvsle (bvadd x3 (bvmul (_ bv4294967287 32) ?lambda) (bvmul (_ bv4294967287 32) x5)) (_ bv628 32)))) (not (and (not (bvsle (bvadd x3 (bvmul (_ bv4294967287 32) ?lambda) (bvmul (_ bv4294967287 32) x5)) (_ bv628 32))) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (not bool.b10) (not bool.b8))))))))) (not (and (not (bvsle x3 (_ bv15 32))) (not (and (not (and (bvsle (bvadd x3 (bvmul (_ bv4294967290 32) ?lambda) (bvmul (_ bv4294967290 32) x5)) (_ bv658 32)) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (not (bvsle x3 (_ bv371 32))) (bvsle x3 (_ bv610 32)) (bvsle (bvadd (bvmul (_ bv4294967295 32) ?lambda) (bvmul (_ bv4294967295 32) x5)) (_ bv4294967286 32)) (not bool.b10) (not bool.b8) (bvsle x3 (_ bv30 32)))))) (not (and (not (bvsle (bvadd x3 (bvmul (_ bv4294967290 32) ?lambda) (bvmul (_ bv4294967290 32) x5)) (_ bv658 32))) (not (and (not (and (not (bvsle x3 (_ bv371 32))) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (bvsle x3 (_ bv610 32)) (bvsle (bvadd (bvmul (_ bv4294967295 32) ?lambda) (bvmul (_ bv4294967295 32) x5)) (_ bv4294967286 32)) (not bool.b10) (not bool.b8) (bvsle x3 (_ bv30 32)))))) (not (and (bvsle x3 (_ bv371 32)) (not (and (not bool.b12) (not bool.b5) (not bool.b14) (bvsle (bvadd (bvmul (_ bv4294967295 32) ?lambda) (bvmul (_ bv4294967295 32) x5)) (_ bv4294967286 32)) (not bool.b10) (not bool.b8))))))))))))))))))) bool.b7)) (not bool.b22) (not (and (not (and (not bool.b6) bool.b5)) (not bool.b7))))) (bvslt ?lambda (_ bv0 32)) (exists ((?lambdaprime (_ BitVec 32))) (and (bvsle (_ bv0 32) ?lambdaprime) (not (and (not (and (not bool.b5) (not (and (not (bvsle (bvmul (_ bv4294967295 32) x3) (_ bv4294967266 32))) (not (bvsle (bvadd (bvmul (_ bv4294967295 32) x4) (bvmul (_ bv4294967236 32) ?lambdaprime)) (_ bv4294962796 32))))) bool.b7 (not bool.b6) (not bool.b22))) (not (bvsle (bvadd (bvmul (_ bv4294967295 32) ?lambdaprime) (bvmul (_ bv4294967295 32) x5)) (_ bv4294967286 32))) (not (and (not bool.b5) (not bool.b6) (not bool.b7) (not (and (not (bvsle (bvmul (_ bv4294967295 32) x3) (_ bv4294967266 32))) (not (bvsle (bvadd (bvmul (_ bv4294967295 32) x4) (bvmul (_ bv4294967236 32) ?lambdaprime)) (_ bv4294963196 32))))) (not bool.b22))) (not (and (not bool.b5) bool.b6 (not (and (not (bvsle (bvmul (_ bv4294967295 32) x3) (_ bv4294967266 32))) (not (bvsle (bvadd (bvmul (_ bv4294967295 32) x4) (bvmul (_ bv4294967236 32) ?lambdaprime)) (_ bv4294962386 32))))) (not bool.b7) (not bool.b22))))) (bvsle ?lambdaprime ?lambda)))))";
		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void arrayEliminationRushingMountaineer02() {
		final VarDecl[] funDecls =
				new VarDecl[] { new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "~#a~0.base"),
						new VarDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "#valid"), };
		final String inputSTR =
				"(exists ((|v_#valid_34| (Array (_ BitVec 32) (_ BitVec 1))) (|#t~string0.base| (_ BitVec 32)) (|#t~string3.base| (_ BitVec 32)) (|#t~string6.base| (_ BitVec 32)) (|#t~string9.base| (_ BitVec 32)) (|#t~string12.base| (_ BitVec 32)) (|#t~string15.base| (_ BitVec 32))) (= (store (store (store (store (store (store (store |v_#valid_34| (_ bv0 32) (_ bv0 1)) |#t~string0.base| (_ bv1 1)) |#t~string3.base| (_ bv1 1)) |#t~string6.base| (_ bv1 1)) |#t~string9.base| (_ bv1 1)) |#t~string12.base| (_ bv1 1)) |#t~string15.base| (_ bv1 1)) |#valid|))";

		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void heap_data_cart2() {
		final VarDecl[] funDecls =
				new VarDecl[] { new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "idxDim1", "idxDim2"),
						new VarDecl(QuantifierEliminationTest::getArrayBv32Bv32Bv32Sort, "arr"), };
		final String inputSTR =
				"(and (= idxDim2 (_ bv0 32)) (exists ((x (_ BitVec 32))) (and (exists ((|â| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (y (_ BitVec 32)) (z Bool)) (and (or (and (not (bvslt (select (select |â| y) (_ bv4 32)) x)) (not z)) (and (bvslt (select (select |â| y) (_ bv4 32)) x) z)) (= (store |â| y (store (store (select |â| y) (_ bv8 32) x) (_ bv4 32) (select (store (select |â| y) (_ bv8 32) x) (_ bv4 32)))) arr) (not (bvslt (select (select |â| idxDim1) (bvadd idxDim2 (_ bv4 32))) (select (select |â| idxDim1) (bvadd idxDim2 (_ bv8 32))))) (not (bvslt (select (select |â| idxDim1) (bvadd idxDim2 (_ bv8 32))) (_ bv0 32))) (not z))) (not (bvslt x (_ bv0 32))))))";
		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void memleaks_test1_3() {
		final VarDecl[] funDecls =
				new VarDecl[] { new VarDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "#valid", "old(#valid)"), };
		final String inputSTR =
				"(forall ((|v_old(#valid)_BEFORE_CALL_3| (Array (_ BitVec 32) (_ BitVec 1)))) (or (= |#valid| |v_old(#valid)_BEFORE_CALL_3|) (not (forall ((v_entry_point_~p~0.base_12 (_ BitVec 32))) (or (not (= (select |old(#valid)| v_entry_point_~p~0.base_12) (_ bv0 1))) (= |v_old(#valid)_BEFORE_CALL_3| (store |old(#valid)| v_entry_point_~p~0.base_12 (_ bv0 1))))))))";
		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void memleaks_test4_2() {
		final VarDecl[] funDecls =
				new VarDecl[] { new VarDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "#valid", "old(#valid)"), };
		final String inputSTR =
				"(forall ((|v_old(#valid)_BEFORE_CALL_8| (Array (_ BitVec 32) (_ BitVec 1)))) (or (not (forall ((v_entry_point_~p~0.base_23 (_ BitVec 32)) (v_entry_point_~q~0.base_17 (_ BitVec 32))) (or (= (store (store (store |old(#valid)| v_entry_point_~p~0.base_23 (_ bv1 1)) v_entry_point_~q~0.base_17 (_ bv0 1)) v_entry_point_~p~0.base_23 (_ bv0 1)) |v_old(#valid)_BEFORE_CALL_8|) (not (= (_ bv0 1) (select |old(#valid)| v_entry_point_~p~0.base_23))) (not (= (select (store |old(#valid)| v_entry_point_~p~0.base_23 (_ bv1 1)) v_entry_point_~q~0.base_17) (_ bv0 1)))))) (= |#valid| |v_old(#valid)_BEFORE_CALL_8|)))";
		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void arrayEliminationRushingMountaineer01() {
		final VarDecl[] funDecls =
				new VarDecl[] { new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "~#a~0.base"),
						new VarDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "#valid"), };
		final String inputSTR =
				"(exists ((|v_#valid_16| (Array (_ BitVec 32) (_ BitVec 1))) (|#t~string2.base| (_ BitVec 32))) (= (store (store (store |v_#valid_16| (_ bv0 32) (_ bv0 1)) |#t~string2.base| (_ bv1 1)) |~#a~0.base| (_ bv1 1)) |#valid|))";
		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void arrayEliminationRushingMountaineer01Reduced() {
		final VarDecl[] funDecls = new VarDecl[] { new VarDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "a"), };
		final String inputSTR =
				"(exists ((ax (Array (_ BitVec 32) (_ BitVec 1))) (kx (_ BitVec 32))) (= (store (store ax (_ bv0 32) (_ bv0 1)) kx (_ bv1 1)) a))";
		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void arrayEliminationRushingMountaineer03() {
		final VarDecl[] funDecls =
				new VarDecl[] { new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "main_~x0~0.base"),
						new VarDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "#valid"), };
		final String inputSTR =
				"(exists ((|v_#valid_64| (Array (_ BitVec 32) (_ BitVec 1))) (|main_#t~malloc1.base| (_ BitVec 32)) (|main_#t~malloc2.base| (_ BitVec 32)) (|main_#t~malloc3.base| (_ BitVec 32))) (and (= (store (store (store (store |v_#valid_64| main_~x0~0.base (_ bv1 1)) |main_#t~malloc1.base| (_ bv1 1)) |main_#t~malloc2.base| (_ bv1 1)) |main_#t~malloc3.base| (_ bv1 1)) |#valid|) (= (select (store (store (store |v_#valid_64| main_~x0~0.base (_ bv1 1)) |main_#t~malloc1.base| (_ bv1 1)) |main_#t~malloc2.base| (_ bv1 1)) |main_#t~malloc3.base|) (_ bv0 1)) (= (_ bv0 1) (select (store |v_#valid_64| main_~x0~0.base (_ bv1 1)) |main_#t~malloc1.base|))))";
		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void bvTirHospitalized() {
		final VarDecl[] funDecls = { new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "A", "q", "r") };
		final String inputSTR = "(forall ((B (_ BitVec 32))) (= A (bvadd (bvmul q B) r)))";

		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	/**
	 * Regression test for bug in array PQE. Should maybe be moved to different file.
	 */
	@Test
	public void heap_data_cart() {
		final VarDecl[] funDecls =
				new VarDecl[] { new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "idxDim1", "idxDim2"),
						new VarDecl(QuantifierEliminationTest::getArrayBv32Bv32Bv32Sort, "arr"), };
		final String inputSTR =
				"(and (= idxDim2 (_ bv0 32)) (exists ((x (_ BitVec 32))) (and (exists ((y Bool) (|â| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32))))) (and (not y) (or (and (not (bvslt (select (select |â| idxDim1) (bvadd idxDim2 (_ bv4 32))) x)) (not y)) (and y (bvslt (select (select |â| idxDim1) (bvadd idxDim2 (_ bv4 32))) x))) (= (select (select |â| idxDim1) (bvadd idxDim2 (_ bv8 32))) (_ bv0 32)) (= arr (store |â| idxDim1 (store (store (select |â| idxDim1) (bvadd idxDim2 (_ bv8 32)) x) (bvadd idxDim2 (_ bv4 32)) (select (store (select |â| idxDim1) (bvadd idxDim2 (_ bv8 32)) x) (bvadd idxDim2 (_ bv4 32)))))))) (not (bvslt x (_ bv0 32))))))";
		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void list_simple_dll2cupdateall() {
		final VarDecl[] funDecls = new VarDecl[] {
				new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "main_~s~0.base", "main_~s~0.offset",
						"main_~new_data~0", "main_~len~0"),
				new VarDecl(QuantifierEliminationTest::getArrayBv32Bv32Bv32Sort, "#memory_$Pointer$.base"), };
		final String inputSTR =
				"(forall ((|v_dll_circular_update_at_#in~head.offset_11| (_ BitVec 32)) (|v_#memory_int_114| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (v_dll_circular_update_at_~head.offset_21 (_ BitVec 32)) (|v_#memory_int_115| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (|v_#memory_$Pointer$.base_115| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (v_dll_circular_update_at_~data_16 (_ BitVec 32)) (|v_dll_circular_update_at_#in~head.base_11| (_ BitVec 32)) (v_dll_circular_update_at_~head.base_21 (_ BitVec 32)) (|v_dll_circular_update_at_#in~data_10| (_ BitVec 32)) (|v_old(#memory_$Pointer$.base)_40| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32))))) (or (forall ((v_dll_circular_update_at_~head.offset_16 (_ BitVec 32)) (v_dll_circular_update_at_~data_12 (_ BitVec 32))) (= (select (select (store |v_#memory_int_115| (select (select |v_#memory_$Pointer$.base_115| main_~s~0.base) main_~s~0.offset) (store (select |v_#memory_int_115| (select (select |v_#memory_$Pointer$.base_115| main_~s~0.base) main_~s~0.offset)) (bvadd v_dll_circular_update_at_~head.offset_16 (_ bv8 32)) v_dll_circular_update_at_~data_12)) main_~s~0.base) (bvadd main_~s~0.offset (_ bv8 32))) main_~len~0)) (not (and (= v_dll_circular_update_at_~data_16 |v_dll_circular_update_at_#in~data_10|) (= |v_#memory_int_115| (store |v_#memory_int_114| v_dll_circular_update_at_~head.base_21 (store (select |v_#memory_int_114| v_dll_circular_update_at_~head.base_21) (bvadd v_dll_circular_update_at_~head.offset_21 (_ bv8 32)) v_dll_circular_update_at_~data_16))) (= main_~s~0.base |v_dll_circular_update_at_#in~head.base_11|) (= (store |v_old(#memory_$Pointer$.base)_40| v_dll_circular_update_at_~head.base_21 (store (select |v_old(#memory_$Pointer$.base)_40| v_dll_circular_update_at_~head.base_21) (bvadd v_dll_circular_update_at_~head.offset_21 (_ bv8 32)) (select (select |v_#memory_$Pointer$.base_115| v_dll_circular_update_at_~head.base_21) (bvadd v_dll_circular_update_at_~head.offset_21 (_ bv8 32))))) |v_#memory_$Pointer$.base_115|) (= |v_dll_circular_update_at_#in~head.base_11| v_dll_circular_update_at_~head.base_21) (= |v_dll_circular_update_at_#in~head.offset_11| main_~s~0.offset) (= main_~new_data~0 |v_dll_circular_update_at_#in~data_10|) (= |v_old(#memory_$Pointer$.base)_40| |#memory_$Pointer$.base|) (= |v_dll_circular_update_at_#in~head.offset_11| v_dll_circular_update_at_~head.offset_21)))))";
		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void sll_circular_traversal_2() {
		final VarDecl[] funDecls = new VarDecl[] {
				new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "sll_circular_create_~new_head~0.base",
						"sll_circular_create_~new_head~0.offset", "sll_circular_create_~head~0.offset",
						"sll_circular_create_~head~0.base", "sll_circular_create_~last~0.base",
						"sll_circular_create_~last~0.offset"),
				new VarDecl(QuantifierEliminationTest::getArrayBv32Bv32Sort, "#length"), };
		final String inputSTR =
				"(forall ((|#memory_$Pointer$.base| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (|#memory_$Pointer$.offset| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (|v_#memory_$Pointer$.offset_156| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (|v_#memory_$Pointer$.base_164| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32))))) (or (and (= sll_circular_create_~new_head~0.base (select (select (store |v_#memory_$Pointer$.base_164| sll_circular_create_~last~0.base (store (select |v_#memory_$Pointer$.base_164| sll_circular_create_~last~0.base) sll_circular_create_~last~0.offset sll_circular_create_~new_head~0.base)) sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset)) (= (select (select (store |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base (store (select |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base) sll_circular_create_~last~0.offset sll_circular_create_~new_head~0.offset)) sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset) sll_circular_create_~new_head~0.offset)) (not (and (= (store |#memory_$Pointer$.offset| sll_circular_create_~new_head~0.base (store (select |#memory_$Pointer$.offset| sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset sll_circular_create_~head~0.offset)) |v_#memory_$Pointer$.offset_156|) (= (store |#memory_$Pointer$.base| sll_circular_create_~new_head~0.base (store (select |#memory_$Pointer$.base| sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset sll_circular_create_~head~0.base)) |v_#memory_$Pointer$.base_164|))) (and (bvule (bvadd (select (select (store |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base (store (select |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base) sll_circular_create_~last~0.offset sll_circular_create_~new_head~0.offset)) sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset) (_ bv8 32)) (select |#length| (select (select (store |v_#memory_$Pointer$.base_164| sll_circular_create_~last~0.base (store (select |v_#memory_$Pointer$.base_164| sll_circular_create_~last~0.base) sll_circular_create_~last~0.offset sll_circular_create_~new_head~0.base)) sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset))) (bvule (bvadd (select (select (store |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base (store (select |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base) sll_circular_create_~last~0.offset sll_circular_create_~new_head~0.offset)) sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset) (_ bv4 32)) (bvadd (select (select (store |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base (store (select |v_#memory_$Pointer$.offset_156| sll_circular_create_~last~0.base) sll_circular_create_~last~0.offset sll_circular_create_~new_head~0.offset)) sll_circular_create_~new_head~0.base) sll_circular_create_~new_head~0.offset) (_ bv8 32))))))";
		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	/**
	 * TODO Matthias 2023-03-14: After switching to the new elimination for div and
	 * mod (DML) we cannot eliminate all auxiliary variables.
	 */
	@Test
	public void bvTirBug07() {
		final VarDecl[] funDecls = { new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "main_~a~0", "main_~b~0") };
		final String inputSTR =	"(forall ((|main_#t~post2| (_ BitVec 32)) (main_~i~0 (_ BitVec 32)) (|v_main_#t~post2_11| (_ BitVec 32)) (|v_main_#t~ret1_14| (_ BitVec 32)) (v_main_~b~0_19 (_ BitVec 32))) (or (bvult v_main_~b~0_19 main_~a~0) (bvult (bvadd (bvneg v_main_~b~0_19) main_~a~0) (_ bv1 32)) (not (bvult main_~i~0 main_~a~0)) (and (or (= |v_main_#t~ret1_14| (_ bv0 32)) (not (= (bvadd v_main_~b~0_19 (_ bv4294967295 32)) main_~b~0))) (or (not (= |v_main_#t~ret1_14| (_ bv0 32))) (not (= v_main_~b~0_19 main_~b~0)) (not (= |main_#t~post2| |v_main_#t~post2_11|))))))";
		setUpScript(SOLVER_COMMAND_Z3, funDecls);
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}
}