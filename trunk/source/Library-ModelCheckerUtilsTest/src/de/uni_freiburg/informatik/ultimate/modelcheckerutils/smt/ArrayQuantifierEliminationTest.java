package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class ArrayQuantifierEliminationTest {
	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private Sort mIntSort;
	private Sort mBoolSort;
	private Term mTrueTerm;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger("lol");
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mIntSort = SmtSortUtils.getIntSort(mMgdScript);
		mBoolSort = SmtSortUtils.getBoolSort(mMgdScript);
		mTrueTerm = mScript.term("true");
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	@Test
	public void argentina() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("a", new Sort[0], intintArraySort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and  (=(select a0 7)42) (=(select a0 k)23) (=(store a0 2 1337) a))))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testQuantifireFree(result));
		Assert.assertTrue(testIS(result,
				"(and (= 1337 (select a 2)) (= (select a 7) 42) (or (= (select a k) 23) (= k 2)) (or (not (= k 2)) (= (select a k) 1337)) (or (not (= k 7)) (= (select a 7) 23)))"));
	}

//	 @Test //Select Over Store
	public void butan() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("a", new Sort[0], intintArraySort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and  (=(store a0 4 1337)a) (=(select (store a 2 42) 4) 1337) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testQuantifireFree(result));

	}

//	 @Test //Store Over Store
	public void butan2() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("a", new Sort[0], intintArraySort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and  (=(store a0 7 32)a) (=(store (store a0 i 13327)k 13327) a) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testQuantifireFree(result));

	}

	@Test
	public void finland() {
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and  (=(select a0 k)42) (=(select a0 i)23) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testIS(result, "(not (= i k))"));
	}

	@Test
	public void finland1() {
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		mScript.declareFun("x", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (or (and  (=(select a0 k)42) (=(select a0 i)23) )  (and  (=(select a0 j)44) (=(select a0 x)2324) )       ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testIS(result, "(or (not (= i k)) (not (= j x)))"));
	}

	@Test
	public void finland2() {
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		mScript.declareFun("x", new Sort[0], mIntSort);
		final String formulaAsString = "(forall ((a0 (Array Int Int))) (and (or  (not(=(select a0 k)42)) (not(=(select a0 i)23)) )  (or  (not(=(select a0 j)44)) (not(=(select a0 x)2324) ))       ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testIS(result, "false"));
	}

	@Test // finland with forall and disjunction VERIFY RESULT
	public void sweden() {
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		mScript.declareFun("x", new Sort[0], mIntSort);
		final String formulaAsString = "(forall ((a0 (Array Int Int))) (or  (=(select a0 i)42)(=(select a0 k)23)))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testIS(result,
				"(and (or (not (= i k)) (forall ((sj_0 Int) (si_0 Int)) (= si_0 sj_0))) (or (forall ((sj_0 Int)) (= sj_0 42)) (forall ((si_0 Int)) (= si_0 23))))"));
	}
	 @Test
	public void yemen() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("v", new Sort[0], mIntSort);
		mScript.declareFun("a1", new Sort[0], intintArraySort);
		mScript.declareFun("a2", new Sort[0], intintArraySort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and  (=(store a0 k v) a1) (=(store a0 k v) a2) (not(= a1 a2)) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testQuantifireFree(result));
	}
	 @Test //eliminiating Array Equailitys, dealing with Partial Equailitys
	public void saudiarabia() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("v", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("a1", new Sort[0], intintArraySort);
		mScript.declareFun("a2", new Sort[0], intintArraySort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and  (=(store a0 k v) a1) (=(store a0 i v) a2) (not(= a1 a2)) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testQuantifireFree(result));
	}
	 @Test //eliminiating Array Equailitys, dealing with Partial Equailitys
	public void saudiarabia2() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("v", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("u", new Sort[0], mIntSort);
		mScript.declareFun("a3", new Sort[0], intintArraySort);
		mScript.declareFun("a1", new Sort[0], intintArraySort);
		mScript.declareFun("a2", new Sort[0], intintArraySort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and (=(store a0 k v) a1) (=(store a2 k v) a1))) ";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testQuantifireFree(result));
	}
	 @Test // 2 Stores
	public void brazil() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("v", new Sort[0], mIntSort);
		mScript.declareFun("a1", new Sort[0], intintArraySort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and (=(store a0 1 3) a1) (= (select a0 k) 4)  (=(store a0 2 4) a1) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testQuantifireFree(result));
	}
	@Test // 2 Stores and partial Equality
	public void laplata() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("a1", new Sort[0], intintArraySort);
		mScript.declareFun("a2", new Sort[0], intintArraySort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and (=(store a0 k 3) a1) (= a1 a2)  (=(store a0 i 4) a2) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testQuantifireFree(result));
	}
	
	@Test // 2 Stores, 2 Quantified Array, Arrays with Sort (Array Int Bool) and partial Equality
	public void germany() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mBoolSort);
		mScript.declareFun("b", new Sort[0], intintArraySort);
		final String formulaAsString = "(exists ((a0 (Array Int Bool))(a1 (Array Int Bool))) (and (= (store a1 2 true) b) (= (store a0 1 false) b) (= (select b 2) true)(= (select b 1) false)))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testQuantifireFree(result));
	}
	@Test // 2 Quantified Array, Arrays with Sort (Array Int Bool) and partial Equality
	public void france() {
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))(a1 (Array Int Int))) (and (=(select a1 k)3) (=(select a1 k)2) (= k 1) (=(select a0 k)2) (=(select a0 k)3)))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testQuantifireFree(result));
	}
	public boolean testTRUE(Term result) {
		return SmtUtils.isTrue(result);
	}

	public boolean testQuantifireFree(Term result) {
		return QuantifierUtils.isQuantifierFree(result);

	}

	public boolean testIS(Term result, String formulaAsString) {
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		return result == formulaAsTerm;
	}

	public boolean testValid(String formulaAsString) {
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		final LBool checkSatResult = SmtUtils.checkSatTerm(mScript, mScript.term("distinct", mTrueTerm, formulaAsTerm));
		return (checkSatResult == LBool.UNSAT);
	}

	public Term parseAndElim(String formulaAsString) {
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		Term result = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript, formulaAsTerm,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		// Term result = NewPartialQuantiElim.tryToEliminate(mServices, mLogger,
		// mMgdScript, formulaAsTerm,
		// SimplificationTechnique.SIMPLIFY_DDA,
		// XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		mLogger.info("Result: " + result);
		return result;
	}

}
