/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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

import java.math.BigInteger;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.PolynomialTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Leonard Fichtner
 */
public class PolynomialTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private Sort mRealSort;
	private Sort mBoolSort;
	private Sort mIntSort;
	private Sort[] mEmptySort;
	private Term mTrueTerm;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger("lol");
		mScript = UltimateMocks.createZ3Script(LogLevel.INFO);
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mRealSort = SmtSortUtils.getRealSort(mMgdScript);
		mBoolSort = SmtSortUtils.getBoolSort(mMgdScript);
		mIntSort = SmtSortUtils.getIntSort(mMgdScript);
		mEmptySort = new Sort[0];
		mTrueTerm = mScript.term("true");
	}

	@After
	public void tearDown() {
		mScript.exit();
	}

	/**
	 * Test addition and multiplication.
	 */
	@Test
	public void polynomialTermTest01() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String formulaAsString = "(+ (* 2 x) y)";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
		Assert.assertTrue(result instanceof AffineTerm);
	}


	/**
	 * Test division by constant.
	 */
	@Test
	public void polynomialTermTest02() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		final String formulaAsString = "(/ (- y x) 10.0)";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
		Assert.assertTrue(result instanceof AffineTerm);
	}

	/**
	 * Test treating of division by sum of variables as a unique variable.
	 */
	@Test
	public void polynomialTermTest03() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		final String formulaAsString = "(/ (- 2.0 x) (+ y x))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
		Assert.assertTrue(result instanceof AffineTerm);
	}

	/**
	 * Test treating division by variable as a unique variable.
	 */
	@Test
	public void polynomialTermTest04() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		final String formulaAsString = "(/ (- y x) y)";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
	}

	/**
	 * Test treating division by sum of constant and variable as a unique variable.
	 */
	@Test
	public void polynomialTermTest05() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		final String formulaAsString = "(/ (- 2.0 x) (+ x 19.0))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
		Assert.assertTrue(result instanceof AffineTerm);
	}

	/**
	 * Test multiplication of equal variables.
	 */
	@Test
	public void polynomialTermTest06() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String formulaAsString = "(+ (* x x) (* y y))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
	}

	/**
	 * Test addition of differently ordered (but equal) multiplications of variables.
	 */
	@Test
	public void polynomialTermTest07() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String formulaAsString = "(+ (* x y) (* y x))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
	}

	/**
	 * A the product of non-zero bitvectors can be zero.
	 */
	@Test
	public void polynomialTermTest08() {
		final Sort bv8 = SmtSortUtils.getBitvectorSort(mScript, 8);
		mScript.declareFun("x", new Sort[0], bv8);
		mScript.declareFun("y", new Sort[0], bv8);
		final String formulaAsString = "(bvmul (bvmul (_ bv4 8) x y) (bvmul (_ bv64 8) x x x))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
		final boolean resultIsCorrect2 = BitvectorUtils.constructTerm(mScript, BigInteger.ZERO, bv8).equals(resultAsTerm);
		Assert.assertTrue(resultIsCorrect2);
	}
	
	/**
	 * Test div.
	 */
	@Test
	public void polynomialTermTest09() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String formulaAsString = "(div (* (* y 6) (* y (* x x) ) ) (div 6 3))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
	}
	
	/**
	 * Test division of zero by something with div.
	 */
	@Test
	public void polynomialTermTest10() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String formulaAsString = "(div (* (* y 0) (* y (* x x) ) ) (div 144 12))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
	}
	
	/**
	 * Test treating div as a unique variable, if division is by zero.
	 */
	@Test
	public void polynomialTermTest11() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String formulaAsString = "(div (* (* y 23) (* y (* x x))) (div 0 12))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
	}

	/**
	 * Test treating div as a unique variable, if coefficients are not integer-divisible.
	 */
	@Test
	public void polynomialTermTest12() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String formulaAsString = "(div (* (* y 6) (* y (* x x))) (div 144 12))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
	}
	
	/**
	 * Test affine div.
	 */
	@Test
	public void polynomialTermTest13() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String formulaAsString = "(+ (div (* y 14) (div 1337 191)) (div (* (+ x y) 20) 10))";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
		Assert.assertTrue(result instanceof AffineTerm);
	}
	
	/**
	 * Test treating affine div as unique variable, and then handle these variables.
	 */
	@Test
	public void polynomialTermTest14() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String formulaAsString = "(* (+ (div (* y 123) (div 1337 191)) (div (* (+ x y) 23) 10)) 2)";
		final Term formulaAsTerm = TermParseUtils.parseTerm(mScript, formulaAsString);
		mLogger.info("Input: " + formulaAsTerm);
		final IPolynomialTerm result = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(formulaAsTerm);
		final Term resultAsTerm = result.toTerm(mScript);
		mLogger.info("Output: " + resultAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, formulaAsTerm, resultAsTerm);
		Assert.assertTrue(resultIsCorrect);
		Assert.assertTrue(result instanceof AffineTerm);
	}

	private static boolean areEquivalent(final Script script, final Term formulaAsTerm, final Term resultAsTerm) {
		final Term equality = SmtUtils.binaryEquality(script, formulaAsTerm, resultAsTerm);
		final Term negatedEquality = SmtUtils.not(script, equality);
		script.push(1);
		script.assertTerm(negatedEquality);
		final LBool lbool = script.checkSat();
		script.pop(1);
		return lbool == LBool.UNSAT;
	}

}
