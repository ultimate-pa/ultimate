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

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermTransformer;
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
 * @author Leonard Fichtner (leonard.fichtner@web.de)
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

	
	@Test
	public void realDivisionByConst() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		final String inputAsString = "(/ (- y x) 10.0)";
		runLogicalEquivalenceBasedTest(inputAsString, true);
	}

	/**
	 * Test treating division by variable as a unique variable.
	 */
	@Test
	public void realDivisionByVar() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		final String inputAsString = "(/ (- y x) y)";
		runLogicalEquivalenceBasedTest(inputAsString, false);
	}

	/**
	 * Test treating of division by sum of variables as a unique variable.
	 */
	@Test
	public void realDivisionBySum01() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		final String inputAsString = "(/ (- 2.0 x) (+ y x))";
		runLogicalEquivalenceBasedTest(inputAsString, true);
	}

	/**
	 * Test treating division by sum of constant and variable as a unique variable.
	 */
	@Test
	public void realDivisionBySum02() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		final String inputAsString = "(/ (- 2.0 x) (+ x 19.0))";
		runLogicalEquivalenceBasedTest(inputAsString, true);
	}

	/**
	 * Test multiplication of equal variables.
	 */
	@Test
	public void realMul() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputAsString = "(+ (* x x) (* y y))";
		runLogicalEquivalenceBasedTest(inputAsString, false);
	}

	/**
	 * Test addition of differently ordered (but equal) multiplications of variables.
	 */
	@Test
	public void realAddMul() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputAsString = "(+ (* x y) (* y x))";
		runLogicalEquivalenceBasedTest(inputAsString, false);
	}

	/**
	 * A the product of non-zero bitvectors can be zero.
	 */
	@Test
	public void bvMul() {
		final Sort bv8 = SmtSortUtils.getBitvectorSort(mScript, 8);
		mScript.declareFun("x", new Sort[0], bv8);
		mScript.declareFun("y", new Sort[0], bv8);
		final String inputAsString = "(bvmul (bvmul (_ bv4 8) x y) (bvmul (_ bv64 8) x x x))";
		final String expectedOutputAsString = "(_ bv0 8)";
		runDefaultTest(inputAsString, expectedOutputAsString);
	}
	
	@Test
	public void intAddMul() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputAsString = "(+ (* 2 x) y)";
		runLogicalEquivalenceBasedTest(inputAsString, true);
	}

	/**
	 * Test div.
	 */
	@Test
	public void intDivision01() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputAsString = "(div (* (* y 6) (* y (* x x) ) ) (div 6 3))";
		runLogicalEquivalenceBasedTest(inputAsString, false);
	}
	
	/**
	 * Test division of zero by something with div.
	 */
	@Test
	public void intDivision02() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputAsString = "(div (* (* y 0) (* y (* x x) ) ) (div 144 12))";
		runLogicalEquivalenceBasedTest(inputAsString, false);
	}
	
	/**
	 * Test treating div as a unique variable, if division is by zero.
	 */
	@Test
	public void intDivision03() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputAsString = "(div (* (* y 23) (* y (* x x))) (div 0 12))";
		runLogicalEquivalenceBasedTest(inputAsString, false);
	}

	/**
	 * Test treating div as a unique variable, if coefficients are not integer-divisible.
	 */
	@Test
	public void intDivision04() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputAsString = "(div (* (* y 6) (* y (* x x))) (div 144 12))";
		runLogicalEquivalenceBasedTest(inputAsString, false);
	}
	
	/**
	 * Test affine div.
	 */
	@Test
	public void intDivision05() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputAsString = "(+ (div (* y 14) (div 1337 191)) (div (* (+ x y) 20) 10))";
		runLogicalEquivalenceBasedTest(inputAsString, true);
	}
	
	/**
	 * Test treating affine div as unique variable, and then handle these variables.
	 */
	@Test
	public void intDivision06() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputAsString = "(* (+ (div (* y 123) (div 1337 191)) (div (* (+ x y) 23) 10)) 2)";
		runLogicalEquivalenceBasedTest(inputAsString, true);
	}
	
	/**
	 * Test treating affine div as unique variable, and then handle these variables.
	 */
	@Test
	public void intDivision07() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputAsString = "(* (div (* y 123) (div 1337 191)) (div (* y 123) (div 1337 191)))";
		runLogicalEquivalenceBasedTest(inputAsString, false);
	}
	
	/**
	 * Test addition of AffineTerm and a PolynomialTerm.
	 */
	@Test
	public void intAdd() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputAsString = "(+ (* 2 x) (* y y))";
		runLogicalEquivalenceBasedTest(inputAsString, false);
	}
	
	/**
	 * Result should be 
	 * <pre>(/ 42.0 x y)</pre>
	 * instead of
	 * <pre>(/ 42.0 (/ x y))</pre>.
	 */
	@Test
	public void realDivisionLeftAssoc01() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		final String inputAsString = "(/ 42.0 x y)";
		runDefaultTest(inputAsString, inputAsString);
	}

	
	/**
	 * Check that non-polynomial terms get partially simplified
	 */
	@Test
	public void realDivisionLeftAssoc02() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		final String inputAsString = "(/ 42.0 2.0 x)";
		final String expectedOutputAsString = "(/ 21.0 x)";
		runDefaultTest(inputAsString, expectedOutputAsString);
	}
	
	/**
	 * The last constant divisors should be pulled out as coefficient.
	 */
	@Test
	public void realDivisionLeftAssoc03() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		final String inputAsString = "(/ 42.0 x y 21.0 2.0)";
		final String expectedOutputAsString = "(* (/ 1.0 42.0) (/ 42.0 x y))";
		runSyntaxWithoutPermutationsTest(inputAsString, expectedOutputAsString);
	}

	/**
	 * Result should be 
	 * <pre>(div (+ (* 21 x x) 1) x)</pre>
	 */
	@Test
	public void realDivisionLeftAssoc04() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		final String inputAsString = "(/ (+ (* 42.0 x x) 2.0) 2.0 x 2.0)";
		final String expectedOutputAsString = "(* (/ 1.0 2.0) (/ (+ (* 21.0 x x) 1.0) x))";
		runSyntaxWithoutPermutationsTest(inputAsString, expectedOutputAsString);
	}
	
	/**
	 * Check that intermediate constants get simplified.
	 */
	@Test
	public void realDivisionLeftAssoc05() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		final String inputAsString = "(/ 42.0 x 5.0 2.0 y 21.0 2.0)";
		final String expectedOutputAsString = "(* (/ 1.0 42.0) (/ 42.0 x 10.0 y))";
		runSyntaxWithoutPermutationsTest(inputAsString, expectedOutputAsString);
	}

	/**
	 * Similar as {@link PolynomialTest#realDivisionLeftAssoc05} but where
	 * variables have been replaced by the zero literal.
	 */
	@Test
	public void realDivisionLeftAssoc05ZeroLiteral() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		final String inputAsString = "(/ 42.0 0.0 5.0 2.0 0.0 21.0 2.0)";
		final String expectedOutputAsString = "(* (/ 1.0 42.0) (/ 42.0 0.0 10.0 0.0))";
		runSyntaxWithoutPermutationsTest(inputAsString, expectedOutputAsString);
	}

	/**
	 * Result should be 
	 * <pre>(/ 42 x y)</pre>
	 * instead of
	 * <pre>(/ 42 (/ x y))</pre>.
	 */
	@Test
	public void intDivisionLeftAssoc01() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		mScript.declareFun("y", new Sort[0], intSort);
		final String inputAsString = "(div 42 x y)";
		runDefaultTest(inputAsString, inputAsString);
	}
	
	/**
	 * Check that non-polynomial terms get partially simplified
	 */
	@Test
	public void intDivisionLeftAssoc02() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		final String inputAsString = "(div 42 2 x)";
		final String expectedOutputAsString = "(div 21 x)";
		runDefaultTest(inputAsString, expectedOutputAsString);
	}
	
	/**
	 * Result should be 
	 * <pre>(div (* x 21) x)</pre>
	 */
	@Test
	public void intDivisionLeftAssoc03() {
		final Sort intSort = SmtSortUtils.getIntSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], intSort);
		final String inputAsString = "(div (* 42 x) 2 x)";
		final String expectedOutputAsString = "(div (* x 21) x)";
		runDefaultTest(inputAsString, expectedOutputAsString);
	}
	
	/**
	 * Result should be 
	 * <pre>(* 42.0 x y)</pre>
	 * instead of
	 * <pre>(* 42.0 (* x y))</pre>.
	 */
	@Test
	public void realMultiplicationLeftAssoc01() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		final String inputAsString = "(* 42.0 y x)";
		runSyntaxWithoutPermutationsTest(inputAsString, inputAsString);
	}
	
	/**
	 * Check that non-polynomial terms get partially simplified
	 */
	@Test
	public void realMultiplicationLeftAssoc02() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		final String inputAsString = "(* 42.0 2.0 x)";
		final String expectedOutputAsString = "(* 84.0 x)";
		runSyntaxWithoutPermutationsTest(inputAsString, expectedOutputAsString);
	}
	
	/**
	 * Result should be 
	 * <pre>(+ 42.0 x y)</pre>
	 * instead of
	 * <pre>(+ 42.0 (+ x y))</pre>.
	 */
	@Test
	public void realAdditionLeftAssoc01() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		final String inputAsString = "(+ 42.0 y x)";
		runSyntaxWithoutPermutationsTest(inputAsString, "(+ 42.0 y x)");
	}
	
	/**
	 * Check that non-polynomial terms get partially simplified
	 */
	@Test
	public void realAdditionLeftAssoc02() {
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		mScript.declareFun("x", new Sort[0], realSort);
		final String inputAsString = "(+ 42.0 2.0 x)";
		final String expectedOutputAsString = "(+ 44.0 x)";
		runSyntaxWithoutPermutationsTest(inputAsString, expectedOutputAsString);
	}
	
	/**
	 * Test whether transformed input is syntactically equivalent to expected
	 * output.
	 */
	private void runDefaultTest(final String inputAsString, final String expectedOutputAsString) {
		final Term inputAsTerm = TermParseUtils.parseTerm(mScript, inputAsString);
		final Term expectedOutputAsTerm = TermParseUtils.parseTerm(mScript, expectedOutputAsString);
		mLogger.info("Input: " + inputAsTerm);
		final IPolynomialTerm output = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(inputAsTerm);
		final Term outputAsTerm = output.toTerm(mScript);
		mLogger.info("Output: " + outputAsTerm);
		mLogger.info("Expected output: " + expectedOutputAsTerm);
		final boolean outputIsCorrect = expectedOutputAsTerm.equals(outputAsTerm);
		Assert.assertTrue(outputIsCorrect);
	}
	
	/**
	 * Test whether transformed input is syntactically equivalent to expected
	 * output, except for permutation. Only works for "flattened" Terms.
	 */
	private void runSyntaxWithoutPermutationsTest(final String inputAsString, final String expectedOutputAsString) {
		final Term inputAsTerm = TermParseUtils.parseTerm(mScript, inputAsString);
		final Term expectedOutputAsTerm = TermParseUtils.parseTerm(mScript, expectedOutputAsString);
		mLogger.info("Input: " + inputAsTerm);
		final IPolynomialTerm output = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(inputAsTerm);
		final Term outputAsTerm = output.toTerm(mScript);
		mLogger.info("Output: " + outputAsTerm);
		mLogger.info("Expected output: " + expectedOutputAsTerm);
		//Trim braces
		String expectedTrimmed = expectedOutputAsString.substring(1, expectedOutputAsString.length() - 1);
		String outputTrimmed = outputAsTerm.toString().substring(1, outputAsTerm.toString().length() - 1);
		String[] expectedArgs = expectedTrimmed.split("\\s");
		String[] outputArgs = outputTrimmed.split("\\s");
		for (int i = 0; i < expectedArgs.length; i++) {
			for (int j = 0; j < outputArgs.length; j++) {
				if (expectedArgs[i].equals(outputArgs[j])) {
					outputArgs[j] = null;
					expectedArgs[i] = null;
					break;
				}
			}
		}
		boolean inputRemoved = true;
		for (String arg : outputArgs) {
			if (!(arg == null)) {
				inputRemoved = false;
			}
		}
		boolean expectedRemoved = true;
		for (String arg : expectedArgs) {
			if (!(arg == null)) {
				expectedRemoved = false;
			}
		}
		final boolean outputIsCorrect = inputRemoved && expectedRemoved;
		Assert.assertTrue(outputIsCorrect);
	}
	
	/**
	 * Test whether the transformed input is logically equivalent to the input.
	 * @param checkOutputIsAffine check that transformed input is an {@link AffineTerm}
	 */
	private void runLogicalEquivalenceBasedTest(final String inputAsString, final boolean checkOutputIsAffine) {
		final Term inputAsTerm = TermParseUtils.parseTerm(mScript, inputAsString);
		mLogger.info("Input: " + inputAsTerm);
		final IPolynomialTerm output = (IPolynomialTerm) new PolynomialTermTransformer(mScript).transform(inputAsTerm);
		final Term outputAsTerm = output.toTerm(mScript);
		mLogger.info("Output: " + outputAsTerm);
		final boolean resultIsCorrect = areEquivalent(mScript, inputAsTerm, outputAsTerm);
		Assert.assertTrue(resultIsCorrect);
		if (checkOutputIsAffine) {
			Assert.assertTrue(output instanceof AffineTerm);
		}
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
