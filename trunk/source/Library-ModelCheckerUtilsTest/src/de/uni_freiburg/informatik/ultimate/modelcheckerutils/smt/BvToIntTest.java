package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.IOException;
import java.util.HashMap;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.bvToIntSMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.intToBvBackTranslator;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationManager;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.LoggingScriptForMainTrackBenchmarks;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;

/**
 *
 * @author Max Barth
 */

public class BvToIntTest {

	private static final boolean WRITE_SMT_SCRIPTS_TO_FILE = false;
	private static final boolean WRITE_MAIN_TRACK_SCRIPT_IF_UNKNOWN_TO_FILE = false;

	private static final String SOLVER_COMMAND_Z3 =
			"z3 SMTLIB2_COMPLIANT=true -t:6000 -memory:2024 -smt2 -in smt.arith.solver=2";
	private static final String SOLVER_COMMAND_CVC4 = "cvc4 --incremental --print-success --lang smt --tlimit-per=6000";
	private static final String SOLVER_COMMAND_MATHSAT = "mathsat";
	/**
	 * If DEFAULT_SOLVER_COMMAND is not null we ignore the solver specified
	 * for each test and use only the solver
	 * specified here. This can be useful to check if there is a suitable
	 * solver for all tests and this can be useful
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

	private Term parse(final String formulaAsString) {
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		return formulaAsTerm;
	}

	private Term translateQelimBacktranslateO(final Term input) {
		final bvToIntSMT bvtoint = new bvToIntSMT(mMgdScript, null, null, null);
		final Term translated = bvtoint.intBlasting(input);

		System.out.println("translatedResult: " + translated.toStringDirect());
		final Term qelimResult = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, translated,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		System.out.println("qelimResult: " + qelimResult.toStringDirect());

		final intToBvBackTranslator back =
				new intToBvBackTranslator(mScript, bvtoint.getVarMap(), bvtoint.reversedTranslationMap());

		final Term backTranslated = back.backTranslate(qelimResult);
		System.out.println("backtransresult: " + backTranslated.toStringDirect());
		return backTranslated;
	}

	private Term translateQelimBacktranslate(final Term input) {
		final TranslationManager translationManager = new TranslationManager(mMgdScript);
		final Term translated = translationManager.translateBvtoInt(input);

		System.out.println("translatedResult: " + translated.toStringDirect());
		final Term qelimResult = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, translated,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		System.out.println("qelimResult: " + qelimResult.toStringDirect());

		final Term backTranslated = translationManager.translateIntBacktoBv(qelimResult);
		System.out.println("backtransresult: " + backTranslated);
		System.out.println("backtransresult: " + backTranslated.toStringDirect());
		return backTranslated;
	}

	private void testQelim(final Term t1, final Term t2) {
		final Term qelimResult = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, t1,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		System.out.println(qelimResult);
		final LBool equi = SmtUtils.checkEquivalence(t1, t2, mScript);
		assert !equi.equals(LBool.UNKNOWN);
		Assert.assertTrue(equi.equals(LBool.UNSAT));
		if (equi.equals(LBool.UNSAT)) {
			Assert.assertTrue(equi.equals(LBool.UNSAT));
		} else if (!QuantifierUtils.isQuantifierFree(qelimResult)) {
			// TODO translate everything
			// TODO not equivalent if we find qfree int formel
			Assert.assertTrue(true);
		} else {
			Assert.assertTrue(false);
		}

	}

	private void testSpecialCase(final Term input) {
		final TranslationManager translationManager = new TranslationManager(mMgdScript);
		final Term translated = translationManager.translateBvtoInt(input);
		System.out.println("translatedResult: " + translated.toStringDirect());
		final String backtranslate =
				"(and (or  (< v_intInVar_1 (+ v_intInVar_3 1))  (or(not(<(+ v_intInVar_3 1) 1) ) (< v_intInVar_1 v_intInVar_3)) )	   (< v_intInVar_3 256) (< v_intInVar_2 256) (< v_intInVar_1 v_intInVar_2) (< v_intInVar_1 256) (<= 0 v_intInVar_1) (<= 0 v_intInVar_2) (< v_intInVar_2 v_intInVar_3) (<= 0 v_intInVar_3))";

		Assert.assertTrue(SmtUtils.checkEquivalence(translated, parse(backtranslate), mScript).equals(LBool.UNSAT));

		final Term backTranslated = translationManager.translateIntBacktoBv(parse(backtranslate));
		System.out.println("backtransresult: " + backTranslated.toStringDirect());

		Assert.assertTrue(SmtUtils.checkEquivalence(input, backTranslated, mScript).equals(LBool.UNSAT));
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

	private void testTranslationModel(final Term inputAsTerm) {
		mScript.setOption(":produce-models", Boolean.TRUE);

		final TranslationManager translationManager = new TranslationManager(mMgdScript);
		final Term outputTerm = translationManager.translateBvtoInt(inputAsTerm);

		mScript.echo(new QuotedObject("Checking if input and output of translation are equivalent"));

		System.out.println(outputTerm);
		// final LBool bitvecCheckSat = Util.checkSat(mScript, inputAsTerm);
		// final LBool intCheckSat = Util.checkSat(mScript, outputTerm);
		mScript.push(1);
		mScript.assertTerm(outputTerm);
		final LBool satInt = mScript.checkSat();

		final LBool satBit;
		if (satInt.equals(LBool.SAT)) {
			final Term[] backtranslatedmodel = backTranslateModel(translationManager.getReversedVarMap(), inputAsTerm);
			final Term newInputTerm = mScript.term("and", backtranslatedmodel);
			mScript.pop(1);
			mScript.push(1);
			mScript.assertTerm(newInputTerm);
			System.out.println(newInputTerm);
			satBit = mScript.checkSat();
			mScript.pop(1);

		} else {
			mScript.push(1);
			mScript.assertTerm(inputAsTerm);
			satBit = mScript.checkSat();
			mScript.pop(1);
		}
		System.out.println("BV: " + satBit);
		System.out.println("INT: " + satInt);
		Assert.assertTrue(satInt.equals(satBit));
	}

	private Term[] backTranslateModel(final HashMap<Term, Term> varmap, final Term inputAsTerm) {

		Term[] vars = new Term[varmap.keySet().size()];
		vars = varmap.keySet().toArray(vars);
		final Term[] varConjunction = new Term[mScript.getValue(vars).size() + 1];
		for (int i = 0; i < varmap.keySet().size(); i++) {

			final Term bvVar = varmap.get(vars[i]);
			final int intVarValue = Integer.parseInt(mScript.getValue(vars).get(vars[i]).toStringDirect());
			final String bitString = Integer.toBinaryString(intVarValue);
			final int size = Integer.valueOf(bvVar.getSort().getIndices()[0]);

			final String repeated = new String(new char[size - bitString.length()]).replace("\0", "0");
			final String bvVarValue = "#b" + repeated + bitString;

			final Term newBvConst = mScript.binary(bvVarValue);
			varConjunction[i] = mScript.term("=", newBvConst, bvVar);
		}
		varConjunction[mScript.getValue(vars).size()] = inputAsTerm;
		return varConjunction;
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

	@Test
	public void testNonLinearity() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y", "z") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (= (bvmul y x) z)";
		testTranslationModel(parse(inputSTR));
	}

	@Test
	public void test1() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (= (bvmul (_ bv255 8) x) (bvmul (_ bv8 8) x))";
		testTranslationModel(parse(inputSTR));
	}

	@Test
	public void test2() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (= (bvadd (_ bv12 8) x) (concat (_ bv1 2) (_ bv8 6)))";
		testTranslationModel(parse(inputSTR));
	}

	@Test
	public void testConcat() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y", "z") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (= ((_ extract 10 3) (concat (_ bv1 2) (concat (_ bv1 2) x))) z)";
		// testTranslationModel(parse(inputSTR));
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void bvslt() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y", "z") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " ( bvslt  x z)";
		// testTranslationModel(parse(inputSTR));
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}
	@Test
	public void bvshl() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = "(= (bvshl (_ bv1 8) x) (_ bv128 8) )";
		testTranslationModel(parse(inputSTR));
	}

	@Test
	public void bvlshr() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = "(= (bvlshr (_ bv128 8) x) (_ bv0 8) )";
		testTranslationModel(parse(inputSTR));
	}

	@Test
	public void bvand() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (= (bvand #b11111111 x) #b00000011 ))";
		testTranslationModel(parse(inputSTR));
	}

	@Test
	public void bvselect() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR =
				"(exists ((a0 (Array (_ BitVec 8) (_ BitVec 8)))) (and (= (select a0 x  ) y)  (bvult (select a0 x  ) y))  )";
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void bvsdiv() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (= (bvsdiv #b11111111 #b11000111) x))";
		testTranslationModel(parse(inputSTR));

	}

	@Test
	public void bvsrem() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (= (bvsrem #b11111111 #b11000111) x ))";
		testTranslationModel(parse(inputSTR));
	}

	@Test
	public void bvor() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (= (bvor y x) #b00000011 ))";
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void bvtest() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (= (bvand (bvlshr (_ bv128 8) x) #b11111111) #b00000011 ))";
		testTranslationModel(parse(inputSTR));
	}

	@Test
	public void bvAndQelim() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y", "z", "a") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (= (bvand (bvmul (bvsub #b00001011 x) #b00001011) y) #b01001011 ))";
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	// @Test TODO
	public void arrayConstraintsNecessary() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y", "z", "a") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		// is there an indice less than 0?
		// exists j. j < 0 (select a j) = x
		final String inputSTR = " ()";
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void bvDeltaOptimization() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y", "z", "a") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (= (bvadd (bvmul (bvsub #b00001011 x) #b00001011) y) #b01001011 ))";
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}
	@Test
	public void bugSignedRelation() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y", "z", "a") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = "(not (bvslt ((_ zero_extend 24) (_ bv1 8)) ((_ sign_extend 24) (_ bv255 8))))";
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void bvNestedConcat() {
		final VarDecl[] vars = { new VarDecl(PolynomialRelationTest::getBitvectorSort8, "x", "y", "z", "a") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (= (concat (concat (concat #b011 x) #b01) y) #b011011111110100001111 ))";
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	// @Test
	public void rajdeepIteration5wp() {
		final VarDecl[] vars =
				new VarDecl[] { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "~smain.count"),
						new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "ULTIMATE.start_design_~nack.base",
								"ULTIMATE.start_design_~nack.offset", "ULTIMATE.start_design_~alloc_addr.base",
								"ULTIMATE.start_main_~#nack~7.base", "ULTIMATE.start_main_~#nack~7.offset"),
						new VarDecl(QuantifierEliminationTest::getArrayBv32Bv8Sort, "~smain.busy"),
		};
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR =
				"(forall ((|#memory_INTTYPE1| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 8)))) (v_bitvector_28 (_ BitVec 32)) (v_bitvector_27 (_ BitVec 32)) (~smain.free_addr (_ BitVec 8)) (v_bitvector_20 (_ BitVec 8)) (~smain.alloc (_ BitVec 8)) (v_bitvector_32 (_ BitVec 32)) (v_bitvector_31 (_ BitVec 32)) (v_bitvector_30 (_ BitVec 32)) (v_bitvector_29 (_ BitVec 32)) (v_bitvector_36 (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 8)))) (ULTIMATE.start_design_~alloc_addr.offset (_ BitVec 32)) (|ULTIMATE.start_design_#t~ite18| (_ BitVec 32)) (v_bitvector_24 (_ BitVec 8)) (v_bitvector_19 (_ BitVec 8)) (v_bitvector_35 (_ BitVec 8)) (v_bitvector_25 (_ BitVec 32)) (v_bitvector_26 (_ BitVec 32)) (v_bitvector_33 (_ BitVec 32)) (v_bitvector_34 (_ BitVec 32))) (and (or (= (_ bv0 32) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) ~smain.alloc) (_ bv0 32))) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32))) (= (select (select (store (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv1 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv1 8))) ULTIMATE.start_design_~alloc_addr.base) v_bitvector_28 ((_ extract 7 0) v_bitvector_27))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8)) (= (_ bv0 32) (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) ~smain.alloc) (_ bv0 32))) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32))) (= (select (select (store (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base) v_bitvector_28 ((_ extract 7 0) v_bitvector_27))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8))) (or (= (_ bv0 32) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) ~smain.alloc) (_ bv0 32))) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32))) (= (_ bv0 32) (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) ~smain.alloc) (_ bv0 32))) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32))) (= (select (select (store (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base) v_bitvector_32 ((_ extract 7 0) v_bitvector_31))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8)) (= (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv16 32))) (or (= (_ bv0 32) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv0 32)) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32))) (= (_ bv0 32) (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv0 32)) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32))) (= (select (select (store (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base) v_bitvector_30 ((_ extract 7 0) v_bitvector_29))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8))) (or (not (= (select (select (store (store v_bitvector_36 ULTIMATE.start_design_~nack.base (store (select v_bitvector_36 ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store v_bitvector_36 ULTIMATE.start_design_~nack.base (store (select v_bitvector_36 ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base) ULTIMATE.start_design_~alloc_addr.offset ((_ extract 7 0) |ULTIMATE.start_design_#t~ite18|))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8))) (= (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) v_bitvector_35) (_ bv1 32))) ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32)) (_ bv0 32)) (= (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) v_bitvector_35) (_ bv1 32))) ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32)) (_ bv0 32)) (= (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv16 32))) (or (not (= (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv16 32))) (= (_ bv0 32) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) ~smain.alloc) (_ bv0 32))) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32))) (= (_ bv0 32) (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) ~smain.alloc) (_ bv0 32))) ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32))) (= (_ bv0 8) ~smain.alloc) (= (select (select (store (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv1 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base (store (select |#memory_INTTYPE1| ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv1 8))) ULTIMATE.start_design_~alloc_addr.base) v_bitvector_25 ((_ extract 7 0) v_bitvector_26))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8))) (or (not (= (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv16 32))) (not (= (select (select (store (store v_bitvector_36 ULTIMATE.start_design_~nack.base (store (select v_bitvector_36 ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv1 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store v_bitvector_36 ULTIMATE.start_design_~nack.base (store (select v_bitvector_36 ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv1 8))) ULTIMATE.start_design_~alloc_addr.base) v_bitvector_33 ((_ extract 7 0) v_bitvector_34))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8))) (= (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) v_bitvector_35) (_ bv1 32))) ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32)) (_ bv0 32)) (= (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) v_bitvector_35) (_ bv1 32))) ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32)) (_ bv0 32)) (= (_ bv0 8) v_bitvector_35)) (or (not (= (select (select (store (store v_bitvector_36 ULTIMATE.start_design_~nack.base (store (select v_bitvector_36 ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base (store (select (store v_bitvector_36 ULTIMATE.start_design_~nack.base (store (select v_bitvector_36 ULTIMATE.start_design_~nack.base) ULTIMATE.start_design_~nack.offset (_ bv0 8))) ULTIMATE.start_design_~alloc_addr.base) ULTIMATE.start_design_~alloc_addr.offset ((_ extract 7 0) |ULTIMATE.start_design_#t~ite18|))) |ULTIMATE.start_main_~#nack~7.base|) |ULTIMATE.start_main_~#nack~7.offset|) (_ bv0 8))) (= (bvand (bvashr ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv0 32)) ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv4 32)) (_ bv1 32)) (_ bv0 32)) (= (_ bv0 32) (bvand ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvsub (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (_ bv0 32)) ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32)))))))) (_ bv31 32)))) (_ bv15 32))))))";
		final String expectedResultAsString =
				"(let ((.cse14 (= ULTIMATE.start_design_~alloc_addr.base |ULTIMATE.start_main_~#nack~7.base|))) (let ((.cse4 (not .cse14)) (.cse1 (= ULTIMATE.start_design_~nack.offset |ULTIMATE.start_main_~#nack~7.offset|)) (.cse2 (= ULTIMATE.start_design_~nack.base |ULTIMATE.start_main_~#nack~7.base|))) (let ((.cse7 (= (_ bv16 32) (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)))) (.cse8 (and .cse4 .cse1 .cse2))) (let ((.cse3 (or .cse14 .cse8)) (.cse10 (not .cse7))) (and (or (forall ((v_prenex_9 (_ BitVec 8)) (v_prenex_8 (_ BitVec 8))) (let ((.cse0 ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvadd (bvneg ((_ zero_extend 24) (bvand v_prenex_8 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_prenex_9) (_ bv15 32)))))))) (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32))) (_ bv31 32)))))) (or (= (_ bv0 32) (bvand (bvashr .cse0 (_ bv4 32)) (_ bv1 32))) (= (bvand .cse0 (_ bv15 32)) (_ bv0 32))))) (and (or (and .cse1 .cse2) (forall ((v_bitvector_28 (_ BitVec 32))) (= |ULTIMATE.start_main_~#nack~7.offset| v_bitvector_28))) .cse3 .cse4)) (forall ((v_prenex_17 (_ BitVec 8)) (v_prenex_18 (_ BitVec 8))) (let ((.cse5 ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvneg ((_ zero_extend 24) (bvand v_prenex_18 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_prenex_17) (_ bv15 32))))))))) (_ bv31 32)))))) (or (= (_ bv0 32) (bvand .cse5 (_ bv15 32))) (= (bvand (bvashr .cse5 (_ bv4 32)) (_ bv1 32)) (_ bv0 32))))) (or (and .cse3 .cse4 .cse1 .cse2) (forall ((v_prenex_6 (_ BitVec 8)) (v_prenex_5 (_ BitVec 8))) (let ((.cse6 ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvadd (bvneg ((_ zero_extend 24) (bvand v_prenex_5 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_prenex_6) (_ bv15 32)))))))) (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32))) (_ bv31 32)))))) (or (= (_ bv0 32) (bvand (bvashr .cse6 (_ bv4 32)) (_ bv1 32))) (= (bvand .cse6 (_ bv15 32)) (_ bv0 32))))) .cse7) (or .cse8 (forall ((v_bitvector_20 (_ BitVec 8)) (~smain.free_addr (_ BitVec 8))) (let ((.cse9 ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvadd (bvneg ((_ zero_extend 24) (bvand v_bitvector_20 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) ~smain.free_addr) (_ bv15 32)))))))) (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32))) (_ bv31 32)))))) (or (= (_ bv0 32) (bvand (bvashr .cse9 (_ bv4 32)) (_ bv1 32))) (= (bvand .cse9 (_ bv15 32)) (_ bv0 32)))))) (or .cse8 .cse10 (forall ((v_bitvector_19 (_ BitVec 8)) (v_bitvector_24 (_ BitVec 8)) (v_bitvector_35 (_ BitVec 8))) (let ((.cse11 ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) v_bitvector_35) (_ bv1 32)) (bvneg ((_ zero_extend 24) (bvand v_bitvector_19 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_bitvector_24) (_ bv15 32))))))))) (_ bv31 32)))))) (or (= (bvand .cse11 (_ bv15 32)) (_ bv0 32)) (= (_ bv0 8) v_bitvector_35) (= (bvand (bvashr .cse11 (_ bv4 32)) (_ bv1 32)) (_ bv0 32)))))) (or (forall ((v_prenex_11 (_ BitVec 8)) (v_prenex_12 (_ BitVec 8))) (let ((.cse12 ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvadd (bvneg ((_ zero_extend 24) (bvand v_prenex_12 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_prenex_11) (_ bv15 32)))))))) (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32))) (_ bv31 32)))))) (or (= (_ bv0 32) (bvand (bvashr .cse12 (_ bv4 32)) (_ bv1 32))) (= (bvand .cse12 (_ bv15 32)) (_ bv0 32))))) .cse10) (or (forall ((v_prenex_4 (_ BitVec 8)) (v_prenex_3 (_ BitVec 8)) (v_prenex_1 (_ BitVec 8))) (let ((.cse13 ((_ zero_extend 24) ((_ extract 7 0) (bvand (bvadd (bvand ((_ zero_extend 24) ~smain.count) (_ bv31 32)) (bvand ((_ zero_extend 24) v_prenex_4) (_ bv1 32)) (bvneg ((_ zero_extend 24) (bvand v_prenex_1 (select ~smain.busy ((_ zero_extend 24) ((_ extract 7 0) (bvand ((_ zero_extend 24) v_prenex_3) (_ bv15 32))))))))) (_ bv31 32)))))) (or (= (bvand (bvashr .cse13 (_ bv4 32)) (_ bv1 32)) (_ bv0 32)) (= (bvand .cse13 (_ bv15 32)) (_ bv0 32))))) .cse7))))))";
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	// @Test
	public void forester_heap_dll_simple_white_blue() {
		final VarDecl[] vars = new VarDecl[] {
				new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "main_~x~0.offset", "main_~head~0.offset",
						"main_~x~0.base", "main_#t~malloc2.base", "main_~head~0.base"),
				new VarDecl(QuantifierEliminationTest::getArrayBv32Bv1Sort, "#valid"), };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR =
				"(forall ((|#memory_$Pointer$.base| (Array (_ BitVec 32) (Array (_ BitVec 32) (_ BitVec 32)))) (|main_#t~mem3.offset| (_ BitVec 32)) (v_subst_5 (_ BitVec 32)) (v_DerPreprocessor_1 (_ BitVec 32))) (= (_ bv1 1) (select |#valid| (select (select (store (store (store |#memory_$Pointer$.base| main_~x~0.base (store (select |#memory_$Pointer$.base| main_~x~0.base) main_~x~0.offset |main_#t~malloc2.base|)) |main_#t~malloc2.base| (store (select (store |#memory_$Pointer$.base| main_~x~0.base (store (select |#memory_$Pointer$.base| main_~x~0.base) main_~x~0.offset |main_#t~malloc2.base|)) |main_#t~malloc2.base|) (bvadd |main_#t~mem3.offset| (_ bv4 32)) main_~x~0.base)) (select (select (store (store |#memory_$Pointer$.base| main_~x~0.base (store (select |#memory_$Pointer$.base| main_~x~0.base) main_~x~0.offset |main_#t~malloc2.base|)) |main_#t~malloc2.base| (store (select (store |#memory_$Pointer$.base| main_~x~0.base (store (select |#memory_$Pointer$.base| main_~x~0.base) main_~x~0.offset |main_#t~malloc2.base|)) |main_#t~malloc2.base|) (bvadd |main_#t~mem3.offset| (_ bv4 32)) main_~x~0.base)) main_~x~0.base) main_~x~0.offset) (store (store (select (store (store |#memory_$Pointer$.base| main_~x~0.base (store (select |#memory_$Pointer$.base| main_~x~0.base) main_~x~0.offset |main_#t~malloc2.base|)) |main_#t~malloc2.base| (store (select (store |#memory_$Pointer$.base| main_~x~0.base (store (select |#memory_$Pointer$.base| main_~x~0.base) main_~x~0.offset |main_#t~malloc2.base|)) |main_#t~malloc2.base|) (bvadd |main_#t~mem3.offset| (_ bv4 32)) main_~x~0.base)) (select (select (store (store |#memory_$Pointer$.base| main_~x~0.base (store (select |#memory_$Pointer$.base| main_~x~0.base) main_~x~0.offset |main_#t~malloc2.base|)) |main_#t~malloc2.base| (store (select (store |#memory_$Pointer$.base| main_~x~0.base (store (select |#memory_$Pointer$.base| main_~x~0.base) main_~x~0.offset |main_#t~malloc2.base|)) |main_#t~malloc2.base|) (bvadd |main_#t~mem3.offset| (_ bv4 32)) main_~x~0.base)) main_~x~0.base) main_~x~0.offset)) (bvadd v_subst_5 (_ bv8 32)) v_DerPreprocessor_1) v_subst_5 (_ bv0 32))) main_~head~0.base) main_~head~0.offset))))";
		final String expectedResultAsString =
				"(forall ((|main_#t~mem3.offset| (_ BitVec 32)) (v_arrayElimCell_62 (_ BitVec 32)) (v_subst_5 (_ BitVec 32)) (v_DerPreprocessor_1 (_ BitVec 32))) (or (and (= (bvadd v_subst_5 (_ bv8 32)) main_~head~0.offset) (= |main_#t~malloc2.base| main_~head~0.base) (= (_ bv1 1) (select |#valid| v_DerPreprocessor_1))) (and (= (select |#valid| (_ bv0 32)) (_ bv1 1)) (= |main_#t~malloc2.base| main_~head~0.base) (= main_~head~0.offset v_subst_5)) (and (or (not (= |main_#t~malloc2.base| main_~head~0.base)) (not (= (bvadd v_subst_5 (_ bv8 32)) main_~head~0.offset))) (or (not (= main_~x~0.offset main_~head~0.offset)) (not (= main_~head~0.base main_~x~0.base))) (or (and (or (not (= main_~head~0.offset (bvadd |main_#t~mem3.offset| (_ bv4 32)))) (not (= |main_#t~malloc2.base| main_~head~0.base))) (= (select |#valid| v_arrayElimCell_62) (_ bv1 1))) (and (= (_ bv1 1) (select |#valid| main_~x~0.base)) (= |main_#t~malloc2.base| main_~head~0.base) (= main_~head~0.offset (bvadd |main_#t~mem3.offset| (_ bv4 32))))) (or (not (= |main_#t~malloc2.base| main_~head~0.base)) (not (= main_~head~0.offset v_subst_5)))) (and (or (not (= |main_#t~malloc2.base| main_~head~0.base)) (not (= (bvadd v_subst_5 (_ bv8 32)) main_~head~0.offset))) (= (_ bv1 1) (select |#valid| |main_#t~malloc2.base|)) (or (not (= |main_#t~malloc2.base| main_~head~0.base)) (not (= main_~head~0.offset v_subst_5))) (= main_~head~0.base main_~x~0.base) (= main_~x~0.offset main_~head~0.offset))))";
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void bvTirBug06LimitedDomain() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort1, "c") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR =
				"(exists ((x (_ BitVec 1)) (y (_ BitVec 1))) (and (not (= x y)) (not (= x c)) (not (= y c))))";

		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test // TODO Qelim fails on BV but nor on int
	public void bvTirOffsetBug01() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = "(forall ((x (_ BitVec 8))) (or (bvuge x a) (bvule x b)))";
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test // TODO Qelim fails on BV but nor on int
	public void negatedbvTirOffsetBug01() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = "(exists ((x (_ BitVec 8))) (not(or (bvuge x a) (bvule x b))))";
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test // TODO Qelim fails on BV but nor on int
	public void negatedbvTirOffsetBug01eq() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = "(exists ((x (_ BitVec 8))(y (_ BitVec 8))) (and (bvult a x) (bvult x y) (bvult y b)))";
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test // TODO Qelim fails on BV but nor on int
	public void negatedbvTirOffsetBug01specialCase() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b", "y", "x") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = " (and (bvult x a) (bvult a y))";
		// testSpecialCase(parse(inputSTR));
		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test // Doesn't work, quantified aux var
	public void bvTirHospitalized() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "A", "q", "r") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = "(forall ((B (_ BitVec 32))) (= A (bvadd (bvmul q B) r)))";

		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void bvTirIrd3() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "a", "b") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = "(exists ((x (_ BitVec 32))) (bvult a x)))";

		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	@Test
	public void bvTirBug03strict() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR =
				"(exists ((x (_ BitVec 8))) (and (not (=  y x)) (bvule lo x) (bvult x hi) (bvule lo y) (bvult y hi)))";

		final Term qelim = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim);
	}

	// 2*x auf andere seite bringen mit DER Translation Actually Usefull?
	@Test
	public void bvDER2x() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final String inputSTR = "(exists ((x (_ BitVec 8))) (= y (bvmul		 #b00000010 x)) )";

		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim3);

	}

	// 2*x auf andere seite bringen mit DER Translation Actually Usefull?
	@Test // TODO git pull
	public void bvDERUNSAT2x() {

		final String inputSTR = "(exists ((x (_ BitVec 8)))  (= y (bvmul	x #b00000111 )) )";
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim3);
	}

	// @Test
	public void checkEqui() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b", "y") };
		final VarDecl[] varsS =
				{ new VarDecl(SmtSortUtils::getIntSort, "v_intInVar_1", "v_intInVar_2", "v_intInVar_3") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		//
		final String inputSTR1 = "(= (_ bv128 8) a)";

		final String inputSTR2 =
				"(bvslt ((_ sign_extend 1) (bvsdiv (bvadd (_ bv2097151 21) ((_ sign_extend 1) (bvsdiv ((_ sign_extend 1) (bvadd ((_ zero_extend 11) a) ((_ sign_extend 2) (bvmul ((_ zero_extend 9) (bvurem a (_ bv128 8))) (_ bv131070 17))))) (_ bv128 20)))) (_ bv2097150 21))) (_ bv1 22))";

		final LBool equi = SmtUtils.checkEquivalence(parse(inputSTR1), parse(inputSTR2), mScript);
		System.out.println(equi);
		assert !equi.equals(LBool.UNKNOWN);
		Assert.assertTrue(equi.equals(LBool.UNSAT));

	}

	@Test
	public void bvuleTIR() {
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvule x hi ) (bvule lo x)))";
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi", "y") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(qelim3, parse("(bvule lo hi)"));
	}

	@Test
	public void bvugeTIR() {
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvuge hi x  ) (bvuge  x lo)))";
		final String expectedResult = "(bvuge hi lo)";
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void signed3() {
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsge hi x  ) (bvsge x lo)))";
		final String expectedResult = "(bvsge hi lo)";
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}


	@Test
	public void signed4() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsle x hi ) (bvsle lo x)))";
		final String expectedResult = "(bvsle lo hi)";
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void bvTIRSignedUnsignedMix() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsle x hi ) (bvule lo x)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test // Timeout
	public void signed6() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };

		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsgt hi x) (bvsle lo x)))";
		final String expectedResult = "(bvslt lo hi)";
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test // BV Solver timeout
	public void signed7() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi", "mi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsgt hi mi) (bvsge mi x) (bvsle lo x)))";
		final String expectedResult = "(and (bvsle lo mi) (bvsgt hi mi))";
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void signed8() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi", "mi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsgt hi mi) (bvsge mi x) (bvsle hi x)))";
		final String expectedResult = "false";
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void bvTir03Strict() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvugt hi x) (bvult lo x)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void bvTirBug01() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR =
				"(exists ((main_~x~0 (_ BitVec 32))) (and (bvsgt main_~x~0 (_ bv100 32)) (not (= (bvadd main_~x~0 (_ bv4294967286 32)) (_ bv91 32))) (not (bvsgt main_~x~0 (_ bv101 32)))))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void bvTirBug02() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi") };
		final String inputSTR =
				"(exists ((main_~x~0 (_ BitVec 32))) (and (not (= (bvadd main_~x~0 (_ bv4294967286 32)) (_ bv91 32)))  (bvsge main_~x~0 (_ bv101 32))))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void bvTirBug04nonstrict() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "lo", "hi", "y") };
		final String inputSTR =
				"(exists ((x (_ BitVec 8))) (and (not (=  y x)) (bvule lo x) (bvule x hi) (bvule lo y) (bvult y hi)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void bvTirSingleDirectionExistsLowerUnsigned() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvult x a) (bvugt b x)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void signed2() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvslt x a) (bvsgt b x)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void bvTirSingleDirectionExistsUpperUnsigned() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvugt x a) (bvult b x)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void signed5() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvsgt x a) (bvslt b x)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void bvTirSingleDirectionForallLowerUnsigned() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(forall ((x (_ BitVec 8))) (or (bvule x a) (bvuge b x)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void signed1() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		// TODO test wenn signed replaced by definition
		final String inputSTR = "(forall ((x (_ BitVec 8))) (or (bvsle x a) (bvsge b x)))";
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(inputSTR), qelim3);
	}

	@Test
	public void bvTirSingleDirectionForallUpperUnsigned() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(forall ((x (_ BitVec 8))) (or (bvuge x a) (bvule b x)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void divisionAndModuloTest() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b", "x") };
		final String inputSTR = "(and (bvsle (bvudiv (_ bv252 8) (_ bv5 8)) b) (= b (_ bv255 8)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void signed0() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b") };
		final String inputSTR = "(forall ((x (_ BitVec 8))) (or (bvsge x a) (bvsle b x)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void bvTirSingleDirectionAndAntiDerUltExists() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b", "c") };
		final String inputSTR = "(exists ((x (_ BitVec 8))) (and (bvult x c) (distinct x b)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void bvTirSingleDirectionAndAntiDerUleExists() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "a", "b") };
		final String inputSTR = "(exists ((x (_ BitVec 32))) (and (bvule a x) (distinct b x)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void bvTirSingleDirectionAndAntiDerUltForall() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort8, "a", "b", "c") };
		final String inputSTR = "(forall ((x (_ BitVec 8))) (or (bvult x c) (= x b)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test
	public void bvTirSingleDirectionAndAntiDerUleForall() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "a", "b") };
		final String inputSTR = "(forall ((x (_ BitVec 32))) (or (bvule a x) (= b x)))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

	@Test // Timeout
	public void bvTirBug07() {
		final VarDecl[] vars = { new VarDecl(QuantifierEliminationTest::getBitvectorSort32, "main_~a~0", "main_~b~0") };
		final String inputSTR =
				"(forall ((|main_#t~post2| (_ BitVec 32)) (main_~i~0 (_ BitVec 32)) (|v_main_#t~post2_11| (_ BitVec 32)) (|v_main_#t~ret1_14| (_ BitVec 32)) (v_main_~b~0_19 (_ BitVec 32))) (or (bvult v_main_~b~0_19 main_~a~0) (bvult (bvadd (bvneg v_main_~b~0_19) main_~a~0) (_ bv1 32)) (not (bvult main_~i~0 main_~a~0)) (and (or (= |v_main_#t~ret1_14| (_ bv0 32)) (not (= (bvadd v_main_~b~0_19 (_ bv4294967295 32)) main_~b~0))) (or (not (= |v_main_#t~ret1_14| (_ bv0 32))) (not (= v_main_~b~0_19 main_~b~0)) (not (= |main_#t~post2| |v_main_#t~post2_11|))))))";
		final String expectedResult = inputSTR;
		setUpScript(SOLVER_COMMAND_Z3, vars);
		final Term qelim3 = translateQelimBacktranslate(parse(inputSTR));
		testQelim(parse(expectedResult), qelim3);
	}

}