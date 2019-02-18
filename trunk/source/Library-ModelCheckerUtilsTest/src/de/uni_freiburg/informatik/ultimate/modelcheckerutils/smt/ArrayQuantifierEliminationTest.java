/*
 * Copyright (C) 2018-2019 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2018-2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
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
/*
	 @Test //Store Over Store
	public void butan4() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("a", new Sort[0], intintArraySort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		mScript.declareFun("p", new Sort[0], mIntSort);
		mScript.declareFun("v", new Sort[0], mIntSort);
		mScript.declareFun("u", new Sort[0], mIntSort);
		mScript.declareFun("n", new Sort[0], mIntSort);
		mScript.declareFun("m", new Sort[0], mIntSort);
		
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and   (=(store a0 p u)a) (= (select (store (store a0 i n)k m) j )v) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testEquivalenz(formulaAsString, result));

	}	

	
	 
//   @Test
	public void congo() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		final Sort multiDimArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort));
		mScript.declareFun("a", new Sort[0], multiDimArraySort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int (Array Int Int)))) (and  (= (select (select a0 5) 7)10)  (= a (store a0 7 (store (select a0 7) 8 23) ))))";
		Term result = parseAndElim(formulaAsString);
		 Assert.assertTrue(testEquivalenz(formulaAsString, result));

//		final String testFormulaAsString = "";

//		Assert.assertTrue(testEquivalenz(testFormulaAsString, result));
	}


	 @Test //Select Over Store
	public void butan() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		
		mScript.declareFun("a", new Sort[0], intintArraySort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and  (= (store a0 4 1337) a ) (= (select (store a0 2 42) 4) 1337) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testEquivalenz(formulaAsString, result));
 
	}

	 @Test //Store Over Store7
	public void butan2() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("a", new Sort[0], intintArraySort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and  (= i k)(=(store a0 k 32)a) (=(store (store a0 i 666)k 13327) a) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testEquivalenz(formulaAsString, result));

	}
	 
	 @Test //Store Over Store
	public void butan3() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("a", new Sort[0], intintArraySort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and  (not(= i k)) (=(store a0 k 32)a) (=(store (store a0 i 666) k 13327) a) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testEquivalenz(formulaAsString, result));

	}
	 
	 @Test //Store Over Store
	public void tunis() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("a", new Sort[0], intintArraySort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int)))   (=(select a0 j )1)  )";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testEquivalenz(formulaAsString, result));
		 }
	 @Test //Store Over Store
	public void italy() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("a", new Sort[0], intintArraySort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int)))    (= (store a0 j 32) a)  )";
		
		Term result = parseAndElim(formulaAsString);
		String testFormulaAsString = "(= (select a j) 32)";

		Assert.assertTrue(testEquivalenz(testFormulaAsString, result));
		 }
	
	 @Test
	public void argentina() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("a", new Sort[0], intintArraySort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and  (=(select a0 7)42) (=(select a0 k)23) (=(store a0 2 1337) a))))";
		Term result = parseAndElim(formulaAsString);
		// Assert.assertTrue(testEquivalenz(formulaAsString, result));

		final String testFormulaAsString = "(or (and (= 1337 (select a 2)) (= (select a 7) 42) (= k 2)) (and (= 1337 (select a 2)) (= (select a 7) 42) (= (select a k) 23)))";

		Assert.assertTrue(testEquivalenz(testFormulaAsString, result));
	}


	 @Test
	public void finland2() {
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		mScript.declareFun("x", new Sort[0], mIntSort);
		final String formulaAsString = "(forall ((a0 (Array Int Int))) (and (or  (not(=(select a0 k)42)) (not(=(select a0 i)23)) )  (or  (not(=(select a0 j)44)) (not(=(select a0 x)2324) )) ))";
		Term result = parseAndElim(formulaAsString);
		final String testFormulaAsString = "(and (= j x) (= i k))";
		Assert.assertTrue(testEquivalenz(testFormulaAsString, result));
	}

	 @Test
	public void finland1() {
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		mScript.declareFun("x", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (or (and  (=(select a0 k)42) (=(select a0 i)23) )  (and  (=(select a0 j)44) (=(select a0 x)2324) )  ))";
		Term result = parseAndElim(formulaAsString);
		final String testFormulaAsString = "(or(not(= k i)) (not (= j x)) )";
		Assert.assertTrue(testEquivalenz(testFormulaAsString, result));
	}

	 @Test // finland with forall and disjunction Result is equivalent to false
	public void sweden() {
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		mScript.declareFun("x", new Sort[0], mIntSort);
		final String formulaAsString = "(forall ((a0 (Array Int Int))) (or  (not(=(select a0 k)42)) (not(=(select a0 i)23))) ) ";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testEquivalenz(formulaAsString, result));
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
		Assert.assertTrue(testEquivalenz(formulaAsString, result));
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
		final String testFormulaAsString = "(and (forall ((j_0 Int)) (or (= k j_0) (= i j_0) (= (select a2 j_0) (select a1 j_0)))) (not (= a1 a2)) (= (select a2 i) v) (= (select a1 k) v))";
		Assert.assertTrue(testEquivalenz(testFormulaAsString, result));

	}

	@Test // 2 Stores, 2 Quantified Array, Arrays with Sort (Array Int Bool) and partial
			// Equality
	public void germany() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mBoolSort);
		mScript.declareFun("b", new Sort[0], intintArraySort);
		final String formulaAsString = "(exists ((a0 (Array Int Bool))(a1 (Array Int Bool))) (and (= (store a1 2 true) b) (= (store a0 1 false) b) (= (select a0 2) true)(= (select a1 1) false)))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testEquivalenz(formulaAsString, result));	
	}

	 @Test // 2 Stores
	public void brazil() {
		final Sort intintArraySort = SmtSortUtils.getArraySort(mScript, mIntSort, mIntSort);
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("v", new Sort[0], mIntSort);
		mScript.declareFun("a1", new Sort[0], intintArraySort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and (=(store a0 1 3) a1) (= (select a0 k) 4)  (=(store a0 2 4) a1) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testEquivalenz(formulaAsString, result));
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
		final String testFormulaAsString = "(and (forall ((j_0 Int)) (or (= k j_0) (= i j_0) (= (select a2 j_0) (select a1 j_0)))) (= (select a2 i) 4) (= (select a1 k) 3) (= a1 a2))";
		Assert.assertTrue(testEquivalenz(testFormulaAsString, result));
	}

	 @Test // 2 Quantified Array, Arrays with Sort (Array Int Bool) and partial
	// Equality
	public void france() {
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("j", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))(a1 (Array Int Int))) (and (=(select a1 k)3) (=(select a1 k)2) (= k 1) (=(select a0 k)2) (=(select a0 k)3)))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testEquivalenz(formulaAsString, result));
	}
	*/		
	
	
	 @Test
	public void finland() {
		mScript.declareFun("k", new Sort[0], mIntSort);
		mScript.declareFun("i", new Sort[0], mIntSort);
		final String formulaAsString = "(exists ((a0 (Array Int Int))) (and  (=(select a0 k)42) (=(select a0 i)23) ))";
		Term result = parseAndElim(formulaAsString);
		Assert.assertTrue(testEquivalenz(formulaAsString, result));
	}
	
	
	
	public boolean testTRUE(Term result) {
		return SmtUtils.isTrue(result);
	}

	public boolean testEquivalenz(String formulaAsString, Term result) {
		Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		Term equi = SmtUtils.not(mScript, SmtUtils.binaryEquality(mScript, formulaAsTerm, result));
		System.out.print("TEST: " + SmtUtils.checkSatTerm(mScript, equi) + "\n");
		return (SmtUtils.checkSatTerm(mScript, equi) == LBool.UNSAT);
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
