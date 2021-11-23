/*
 * Copyright (C) 2021 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.qvasr;

import org.hamcrest.MatcherAssert;
import org.hamcrest.core.IsEqual;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class of tests checking the correctness of various functions needed for computation of rational vector addition
 * systems.
 *
 * @author jonas
 *
 */
public class QvasrAbstractorTest {

	private IUltimateServiceProvider mServices;
	private Script mScript;
	private ManagedScript mMgdScript;
	private ILogger mLogger;
	private Sort mRealSort;

	@Before
	public void setUp() {
		mServices = UltimateMocks.createUltimateServiceProviderMock();
		mLogger = mServices.getLoggingService().getLogger("lol");
		mScript = UltimateMocks.createZ3Script();
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		mRealSort = SmtSortUtils.getRealSort(mMgdScript);
		mLogger.info("Before");
	}

	@Test
	public void testExpandRealMultiplication() {
		/*
		 * Test (0 * x) = 0
		 */
		final Term zero = mScript.decimal("0");
		final Term x = mMgdScript.constructFreshTermVariable("x", SmtSortUtils.getRealSort(mMgdScript));
		final Term zeroTimesX = QvasrAbstractor.expandRealMultiplication(mMgdScript, zero, x);
		MatcherAssert.assertThat(zeroTimesX, IsEqual.equalTo(zero));

		/*
		 * Test (0 * (y + 1)) = 0
		 */
		mScript.declareFun("y", new Sort[0], mRealSort);
		final String yPlus1String = "(+ y 1)";
		final Term yPlus1 = TermParseUtils.parseTerm(mScript, yPlus1String);
		final Term yPlus1Times0 = QvasrAbstractor.expandRealMultiplication(mMgdScript, zero, yPlus1);
		MatcherAssert.assertThat(yPlus1Times0, IsEqual.equalTo(zero));

		/*
		 * Test (y + 1) * (z + 1) = yz + y + z + 1
		 */
		mScript.declareFun("z", new Sort[0], mRealSort);
		final String zPlus1String = "(+ z 1)";
		final Term zPlus1 = TermParseUtils.parseTerm(mScript, zPlus1String);
		final Term yPlus1TimesZPlus1 = QvasrAbstractor.expandRealMultiplication(mMgdScript, zPlus1, yPlus1);
		final String yPlus1TimesZPlus1ResultString = "(+ (* z y) y 1.0 z)";
		final Term yPlus1TimesZPlus1ResultTerm = TermParseUtils.parseTerm(mScript, yPlus1TimesZPlus1ResultString);
		MatcherAssert.assertThat(yPlus1TimesZPlus1, IsEqual.equalTo(yPlus1TimesZPlus1ResultTerm));

		/*
		 * Test zy * (y + 1) = zy^2 + zy
		 */
		final String zyString = "(* z y)";
		final Term zy = TermParseUtils.parseTerm(mScript, zyString);
		final Term zyTimesYPlus1 = QvasrAbstractor.expandRealMultiplication(mMgdScript, zy, yPlus1);
		final String zyTimesYPlus1ResultString = "(+ (* (* y y) z) (* z y) )";
		final Term zyTimesYPlus1ResultTerm = TermParseUtils.parseTerm(mScript, zyTimesYPlus1ResultString);
		MatcherAssert.assertThat(zyTimesYPlus1, IsEqual.equalTo(zyTimesYPlus1ResultTerm));
	}

	@Test
	public void testSimplifyRealDivision() {
		final Term zero = mScript.decimal("0");
		final Term one = mScript.decimal("1");

		/*
		 * Test (x / 1) = x
		 */
		final Term x = mMgdScript.constructFreshTermVariable("x", SmtSortUtils.getRealSort(mMgdScript));
		final Term xOverOneSimplified = QvasrAbstractor.simplifyRealDivision(mMgdScript, x, one);
		MatcherAssert.assertThat(xOverOneSimplified, IsEqual.equalTo(x));

		/*
		 * Test (0 / x) = 0
		 */
		final Term zeroOverOneSimplified = QvasrAbstractor.simplifyRealDivision(mMgdScript, zero, x);
		MatcherAssert.assertThat(zeroOverOneSimplified, IsEqual.equalTo(zero));

		/*
		 * Test (x / x) = 1
		 */
		final Term xOverXSimplified = QvasrAbstractor.simplifyRealDivision(mMgdScript, x, x);
		MatcherAssert.assertThat(xOverXSimplified, IsEqual.equalTo(one));

		mScript.declareFun("x", new Sort[0], mRealSort);
		mScript.declareFun("y", new Sort[0], mRealSort);
		mScript.declareFun("z", new Sort[0], mRealSort);

		/*
		 * Test ((y + 1) / (z + 2)) = ((y + 1) / (z + 2))
		 */
		final String yP1String = "(+ y 1.0)";
		final String zP2String = "(+ z 2.0)";
		final String yP1OverZP2String = "(/ (+ y 1.0) (+ z 2.0))";
		final Term yP1OverZP2 = TermParseUtils.parseTerm(mScript, yP1OverZP2String);
		final Term yP1 = TermParseUtils.parseTerm(mScript, yP1String);
		final Term zP2 = TermParseUtils.parseTerm(mScript, zP2String);
		final Term yP1OverZP2Simplified = QvasrAbstractor.simplifyRealDivision(mMgdScript, yP1, zP2);
		MatcherAssert.assertThat(yP1OverZP2Simplified, IsEqual.equalTo(yP1OverZP2));

		/*
		 * Test ((x + y + 1)/(z + 2)) / ((yx) / (z + 2)) = (x + y + 1) / (yx)
		 */
		final String yPXP1OverZP2String = "(/ (+ y x 1.0) (+ z 2.0))";
		final String yTXOverZP2String = "(/ (* y x) (+ z 2.0))";
		final String yPXP1OverZP2OveryTXOverZP2StringResultString = "(/ (+ x y 1.0) (* y x))";
		final Term yPXP1OverZP2 = TermParseUtils.parseTerm(mScript, yPXP1OverZP2String);
		final Term yTXOverZP2 = TermParseUtils.parseTerm(mScript, yTXOverZP2String);
		final Term yPXP1OverZP2OveryTXOverZP2StringResult =
				TermParseUtils.parseTerm(mScript, yPXP1OverZP2OveryTXOverZP2StringResultString);
		final Term yPXP1OverZP2OveryTXOverZP2StringSimplified =
				QvasrAbstractor.simplifyRealDivision(mMgdScript, yPXP1OverZP2, yTXOverZP2);
		MatcherAssert.assertThat(yPXP1OverZP2OveryTXOverZP2StringSimplified,
				IsEqual.equalTo(yPXP1OverZP2OveryTXOverZP2StringResult));

		/*
		 * Test ((yx) / (z + 2))/((yx) / (z + 2)) = 1
		 */
		final Term yTXOverZP2OveryTXOverZP2Simplified =
				QvasrAbstractor.simplifyRealDivision(mMgdScript, yTXOverZP2, yTXOverZP2);
		MatcherAssert.assertThat(yTXOverZP2OveryTXOverZP2Simplified, IsEqual.equalTo(one));

		/*
		 * Test (x + y + 1)/((x + y + 1) / (z + 2)) = z + 2
		 */
		final String yPXP1String = "(+ y x 1.0)";
		final Term yPXP1 = TermParseUtils.parseTerm(mScript, yPXP1String);
		final Term yPXP1OveryPXP1OverZP2Simplified =
				QvasrAbstractor.simplifyRealDivision(mMgdScript, yPXP1, yPXP1OverZP2);
		MatcherAssert.assertThat(yPXP1OveryPXP1OverZP2Simplified, IsEqual.equalTo(zP2));
	}

	@Test
	public void testSimplifyRealMultiplication() {
		final Term zero = mScript.decimal("0");
		final Term one = mScript.decimal("1");
		mScript.declareFun("x", new Sort[0], mRealSort);
		mScript.declareFun("y", new Sort[0], mRealSort);
		mScript.declareFun("z", new Sort[0], mRealSort);

		/*
		 * Test x * 0 = 0 and x * 1 = x
		 */
		final String xString = "x";
		final Term x = TermParseUtils.parseTerm(mScript, xString);
		final Term xTimes0 = QvasrAbstractor.simplifyRealMultiplication(mMgdScript, x, zero);
		MatcherAssert.assertThat(xTimes0, IsEqual.equalTo(zero));
		final Term xTimes1 = QvasrAbstractor.simplifyRealMultiplication(mMgdScript, x, one);
		MatcherAssert.assertThat(xTimes1, IsEqual.equalTo(x));

		/*
		 * Test (2y / (x + 1)) * (3 / y) = 6/(x + 1)
		 */
		final String yOverXP1String = "(/ (* 2.0 y) (+ x 1.0))";
		final String threeOverYString = "(/ 3.0 y)";
		final Term yOverXP1 = TermParseUtils.parseTerm(mScript, yOverXP1String);
		final Term threeOverY = TermParseUtils.parseTerm(mScript, threeOverYString);
		final String yOverXP1OverThreeOverYResultString = "(/ 6.0 (+ x 1.0))";
		final Term yOverXP1TimesThreeOverYResult =
				TermParseUtils.parseTerm(mScript, yOverXP1OverThreeOverYResultString);
		final Term yOverXP1TimesThreeOverY =
				QvasrAbstractor.simplifyRealMultiplication(mMgdScript, yOverXP1, threeOverY);
		MatcherAssert.assertThat(yOverXP1TimesThreeOverY, IsEqual.equalTo(yOverXP1TimesThreeOverYResult));

		/*
		 * Test ((x + 2.0) / y) * (y / (x + 2)) = 1
		 */
		final String xP2OverYString = "(/ (+ x 2.0) y)";
		final String yOverxP2String = "(/ y (+ x 2.0))";
		final Term yOverxP2 = TermParseUtils.parseTerm(mScript, xP2OverYString);
		final Term xP2OverY = TermParseUtils.parseTerm(mScript, yOverxP2String);
		final Term yOverxP2TimesxP2OverY = QvasrAbstractor.simplifyRealMultiplication(mMgdScript, yOverxP2, xP2OverY);
		MatcherAssert.assertThat(yOverxP2TimesxP2OverY, IsEqual.equalTo(one));

		/*
		 * Test 3 * (x / y) = 3x/y
		 */
		final String threeString = "3.0";
		final String xOverYString = "(/ x y)";
		final Term three = TermParseUtils.parseTerm(mScript, threeString);
		final Term xOverY = TermParseUtils.parseTerm(mScript, xOverYString);
		final String threeTimesXOverYResultString = "(/ (* x 3.0) y)";
		final Term threeTimesXOverYResult = TermParseUtils.parseTerm(mScript, threeTimesXOverYResultString);
		final Term threeTimesXOverY = QvasrAbstractor.simplifyRealMultiplication(mMgdScript, three, xOverY);
		MatcherAssert.assertThat(threeTimesXOverY, IsEqual.equalTo(threeTimesXOverYResult));

		/*
		 * Test y * (x / y) = x
		 */
		final String yString = "y";
		final Term y = TermParseUtils.parseTerm(mScript, yString);
		final Term yTimesXOverY = QvasrAbstractor.simplifyRealMultiplication(mMgdScript, y, xOverY);
		MatcherAssert.assertThat(yTimesXOverY, IsEqual.equalTo(x));
	}

	@Test
	public void testSimplifyRealSubstraction() {
		final Term zero = mScript.decimal("0");
		final Term one = mScript.decimal("1");
		mScript.declareFun("x", new Sort[0], mRealSort);
		mScript.declareFun("y", new Sort[0], mRealSort);
		mScript.declareFun("z", new Sort[0], mRealSort);

		final String xString = "x";
		final Term x = TermParseUtils.parseTerm(mScript, xString);

		/*
		 * Test 1 - 1 = 0 and x - 0 = x
		 */
		final Term oneMinOne = QvasrAbstractor.simplifyRealSubtraction(mMgdScript, one, one);
		MatcherAssert.assertThat(oneMinOne, IsEqual.equalTo(zero));
		final Term xMinZero = QvasrAbstractor.simplifyRealSubtraction(mMgdScript, x, zero);
		MatcherAssert.assertThat(xMinZero, IsEqual.equalTo(x));

		/*
		 * Test 3x - x = 2x
		 */
		final String threeXString = "(* 3.0 x)";
		final Term threeX = TermParseUtils.parseTerm(mScript, threeXString);
		final String twoXString = "(* x 2.0)";
		final Term twoX = TermParseUtils.parseTerm(mScript, twoXString);
		final Term threeXMinX = QvasrAbstractor.simplifyRealSubtraction(mMgdScript, threeX, x);
		MatcherAssert.assertThat(threeXMinX, IsEqual.equalTo(twoX));

		/*
		 * Test ((x + y)/ z) - ((x + 3) / y) = (xy + y^2 - xz + 3z)/(zy)
		 */
		final String xPYOverZString = "(/ (+ x y) z)";
		final Term xPYOverZ = TermParseUtils.parseTerm(mScript, xPYOverZString);
		final String xPThreeOverYString = "(/ (+ x 3.0) y)";
		final Term xPThreeOverY = TermParseUtils.parseTerm(mScript, xPThreeOverYString);
		final Term xPYOverZMinxPThreeOverY =
				QvasrAbstractor.simplifyRealSubtraction(mMgdScript, xPYOverZ, xPThreeOverY);
		MatcherAssert.assertThat(xPYOverZMinxPThreeOverY, IsEqual.equalTo(one));

		/*
		 * Test (3x / 2) - x = x/2
		 */
		final String threeXOverTwoString = "(/ (* 3.0 x) 2.0)";
		final Term threeXOverTwo = TermParseUtils.parseTerm(mScript, threeXOverTwoString);
		final String xOverTwoString = "(* x (/ 1.0 2.0))";
		final Term xOverTwo = TermParseUtils.parseTerm(mScript, xOverTwoString);
		final Term threeXOverTwoMinXOverTwo = QvasrAbstractor.simplifyRealSubtraction(mMgdScript, threeXOverTwo, x);
		MatcherAssert.assertThat(threeXOverTwoMinXOverTwo, IsEqual.equalTo(xOverTwo));

		/*
		 * Test (y / (x + 1)) - (y / (x + 1)) = 0
		 */
		final String yOverXPOneString = "(/ y (+ x 1.0))";
		final Term yOverXPOne = TermParseUtils.parseTerm(mScript, yOverXPOneString);
		final Term yOverXPOneMinYOverXPOne =
				QvasrAbstractor.simplifyRealSubtraction(mMgdScript, yOverXPOne, yOverXPOne);
		MatcherAssert.assertThat(yOverXPOneMinYOverXPOne, IsEqual.equalTo(zero));
	}

	@Test
	public void testReduceRealDivision() {
		mScript.declareFun("x", new Sort[0], mRealSort);
		mScript.declareFun("y", new Sort[0], mRealSort);

		/*
		 * Test (x * (x + y))/ x * (y + 3) = x
		 */
		final String xTimesXYString = "(* x (+ x y))";
		final String xPyString = "(* x (+ y 3.0)))";
		final String xTimesXYOverxPyResultString = "(/ (+ x y) (y + 3.0))";
		final Term xTimesXY = TermParseUtils.parseTerm(mScript, xPyString);
		final Term xy = TermParseUtils.parseTerm(mScript, xTimesXYString);
		final Term xTimesXYOverxPyResult = TermParseUtils.parseTerm(mScript, xTimesXYOverxPyResultString);
		final Pair<Term, Term> xyOverXReduced = QvasrAbstractor.reduceRealDivision(mMgdScript, xy, xTimesXY);
		MatcherAssert.assertThat(SmtUtils.divReal(mScript, xyOverXReduced.getFirst(), xyOverXReduced.getSecond()),
				IsEqual.equalTo(xTimesXYOverxPyResult));
	}

}
