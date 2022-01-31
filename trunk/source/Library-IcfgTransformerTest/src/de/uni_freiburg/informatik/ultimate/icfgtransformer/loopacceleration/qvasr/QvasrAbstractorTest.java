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
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class of tests checking the functionality of various operations needed for the computation of rational vector
 * addition systems with resets (Qvasr).
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrAbstractorTest {

	private Script mScript;
	private ManagedScript mMgdScript;
	private Sort mRealSort;

	/**
	 * Testsuite setup.
	 */
	@Before
	public void setUp() {
		final IUltimateServiceProvider mServices = UltimateMocks.createUltimateServiceProviderMock();
		mScript = UltimateMocks.createZ3Script();
		mMgdScript = new ManagedScript(mServices, mScript);
		final ILogger mLogger = mServices.getLoggingService().getLogger("log");
		mScript.setLogic(Logics.ALL);
		mRealSort = SmtSortUtils.getRealSort(mMgdScript);
		mLogger.info("Before");
	}

	/**
	 * Test expand Multiplication.
	 */
	@Test
	public void testExpandRealMultiplication() {
		final Term zero = mScript.decimal("0");
		final Term one = mScript.decimal("1");
		final Term three = mScript.decimal("3");
		final TermVariable x = mScript.variable("x", mRealSort);
		final TermVariable y = mScript.variable("y", mRealSort);
		final TermVariable z = mScript.variable("z", mRealSort);
		/*
		 * Test (0 * x) = 0
		 */
		final Term zeroTimesX = QvasrAbstractor.expandRealMultiplication(mMgdScript, zero, x);
		MatcherAssert.assertThat(zeroTimesX, IsEqual.equalTo(zero));

		/*
		 * Test (0 * (y + 1)) = 0
		 */
		final Term yPlus1 = SmtUtils.sum(mScript, "+", y, one);
		final Term yPlus1Times0 = QvasrAbstractor.expandRealMultiplication(mMgdScript, zero, yPlus1);
		MatcherAssert.assertThat(yPlus1Times0, IsEqual.equalTo(zero));

		/*
		 * Test 3*(3 + 3) = 18
		 */
		final Term threePThree = SmtUtils.sum(mScript, "+", three, three);
		final Term threeTimesThreePThree = QvasrAbstractor.expandRealMultiplication(mMgdScript, three, threePThree);
		MatcherAssert.assertThat(threeTimesThreePThree, IsEqual.equalTo(mScript.decimal("18")));

		/*
		 * Test (y + 1) * (z + 1) = yz + y + z + 1
		 */
		mScript.declareFun("z", new Sort[0], mRealSort);
		final Term zPlus1 = SmtUtils.sum(mScript, "+", z, one);
		final Term yPlus1TimesZPlus1 = QvasrAbstractor.expandRealMultiplication(mMgdScript, zPlus1, yPlus1);
		final Term yPlus1TimesZPlus1ResultTerm =
				SmtUtils.sum(mScript, "+", SmtUtils.mul(mScript, "*", z, y), y, one, z);
		MatcherAssert.assertThat(yPlus1TimesZPlus1, IsEqual.equalTo(yPlus1TimesZPlus1ResultTerm));

		/*
		 * Test zy * (y + 1) = zy^2 + zy
		 */
		final Term zy = SmtUtils.mul(mScript, "*", z, y);
		final Term zyTimesYPlus1 = QvasrAbstractor.expandRealMultiplication(mMgdScript, zy, yPlus1);
		final Term zyTimesYPlus1ResultTerm =
				SmtUtils.sum(mScript, "+", zy, SmtUtils.mul(mScript, "*", SmtUtils.mul(mScript, "*", z, y), y));
		MatcherAssert.assertThat(zyTimesYPlus1.toStringDirect(),
				IsEqual.equalTo(zyTimesYPlus1ResultTerm.toStringDirect()));

		/*
		 * Test zy * zy = zy^2
		 */
		final Term zyTimesZy = QvasrAbstractor.expandRealMultiplication(mMgdScript, zy, zy);
		final Term zyTimesZyResultTerm = SmtUtils.mul(mScript, "*", zy, zy);
		MatcherAssert.assertThat(zyTimesZy.toStringDirect(), IsEqual.equalTo(zyTimesZyResultTerm.toStringDirect()));

		/*
		 * Test 3(y + 1) = 3y + 3
		 */
		final Term threeTimesYP1 = QvasrAbstractor.expandRealMultiplication(mMgdScript, mScript.decimal("3"), yPlus1);
		final Term threeTimesYP1ResultTerm =
				SmtUtils.sum(mScript, "+", SmtUtils.mul(mScript, "*", mScript.decimal("3"), y), mScript.decimal("3"));
		MatcherAssert.assertThat(threeTimesYP1.toStringDirect(),
				IsEqual.equalTo(threeTimesYP1ResultTerm.toStringDirect()));

		/*
		 * Test 3(zy + y + 1) = 3zy + 3y + 3
		 */
		final Term xYPYPOne = SmtUtils.sum(mScript, "+", zy, yPlus1);
		final Term threeTimesXYPYPOne = QvasrAbstractor.expandRealMultiplication(mMgdScript, three, xYPYPOne);
		final Term threeTimesXYPYPOneResult = SmtUtils.sum(mScript, "+", SmtUtils.mul(mScript, "*", three, zy),
				SmtUtils.mul(mScript, "*", y, three), three);
		MatcherAssert.assertThat(threeTimesXYPYPOne.toStringDirect(),
				IsEqual.equalTo(threeTimesXYPYPOneResult.toStringDirect()));

		/*
		 * Test 3(zy + xy) = 3zy + 3xy
		 */
		final Term xy = SmtUtils.mul(mScript, "*", x, y);
		final Term xyPzy = SmtUtils.sum(mScript, "+", xy, zy);
		final Term threeTimesXyPzy = QvasrAbstractor.expandRealMultiplication(mMgdScript, three, xyPzy);
		final Term threeTimesXyPzyResult = SmtUtils.sum(mScript, "+", SmtUtils.mul(mScript, "*", three, zy),
				SmtUtils.mul(mScript, "*", three, xy));
		MatcherAssert.assertThat(threeTimesXyPzy.toStringDirect(),
				IsEqual.equalTo(threeTimesXyPzyResult.toStringDirect()));

		/*
		 * Test -3(y + 1) = -3y - 3
		 */
		final Term negOne = mScript.decimal("-1");
		final Term negThree = SmtUtils.mul(mScript, "*", negOne, three);
		final Term negThreeTimesYPOne = QvasrAbstractor.expandRealMultiplication(mMgdScript, negThree, yPlus1);
		final Term negThreeTimesYPOneResult =
				SmtUtils.sum(mScript, "+", negThree, SmtUtils.mul(mScript, "*", y, negThree));
		MatcherAssert.assertThat(negThreeTimesYPOne.toStringDirect(),
				IsEqual.equalTo(negThreeTimesYPOneResult.toStringDirect()));

		/*
		 * Test 3*((x/(y + 1)) + (y / xy)) = 3x/y+1 + 3y/xy
		 */
		final Term divXYP1 = SmtUtils.divReal(mScript, x, yPlus1);
		final Term divYXY = SmtUtils.divReal(mScript, y, xy);
		final Term threeTimesDivXYP1PDivYXY = QvasrAbstractor.expandRealMultiplication(mMgdScript, three,
				SmtUtils.sum(mScript, "+", divXYP1, divYXY));
		final Term threeTimesDivXYP1PDivYXYResult = SmtUtils.sum(mScript, "+",
				SmtUtils.mul(mScript, "*", three, divXYP1), SmtUtils.mul(mScript, "*", three, divYXY));
		MatcherAssert.assertThat(threeTimesDivXYP1PDivYXY.toStringDirect(),
				IsEqual.equalTo(threeTimesDivXYP1PDivYXYResult.toStringDirect()));
	}

	/**
	 * Test the simplification of divisions.
	 */
	@Test
	public void testSimplifyRealDivision() {
		final Term zero = mScript.decimal("0");
		final Term one = mScript.decimal("1");
		final TermVariable x = mScript.variable("x", mRealSort);
		final TermVariable y = mScript.variable("y", mRealSort);

		/*
		 * Test (x / 1) = x
		 */
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

		/*
		 * Test ((y + 1) / (z + 2)) = ((y + 1) / (z + 2))
		 */
		final Term yP1 = SmtUtils.sum(mScript, "+", y, one);
		final Term zP2 = SmtUtils.sum(mScript, "+", x, mScript.decimal("2"));
		final Term yP1OverZP2 = SmtUtils.divReal(mScript, yP1, zP2);
		final Term yP1OverZP2Simplified = QvasrAbstractor.simplifyRealDivision(mMgdScript, yP1, zP2);
		MatcherAssert.assertThat(yP1OverZP2Simplified, IsEqual.equalTo(yP1OverZP2));

		/*
		 * Test ((x + y + 1)/(z + 2)) / ((yx) / (z + 2)) = (x + y + 1) / (yx)
		 */
		final Term xPyPOne = SmtUtils.sum(mScript, "+", y, x, one);
		final Term yPXP1OverZP2 = SmtUtils.divReal(mScript, xPyPOne, zP2);
		final Term yTXOverZP2 = SmtUtils.divReal(mScript, SmtUtils.mul(mScript, "*", y, x), zP2);
		final Term yPXP1OverZP2OveryTXOverZP2StringResult =
				SmtUtils.divReal(mScript, xPyPOne, SmtUtils.mul(mScript, "*", y, x));
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
		final Term yPXP1OveryPXP1OverZP2Simplified =
				QvasrAbstractor.simplifyRealDivision(mMgdScript, xPyPOne, yPXP1OverZP2);
		MatcherAssert.assertThat(yPXP1OveryPXP1OverZP2Simplified, IsEqual.equalTo(zP2));

	}

	/**
	 * Test the simplification of multiplications.
	 */
	@Test
	public void testSimplifyRealMultiplication() {
		final Term zero = mScript.decimal("0");
		final Term one = mScript.decimal("1");
		final TermVariable x = mScript.variable("x", mRealSort);
		final TermVariable y = mScript.variable("y", mRealSort);

		/*
		 * Test x * 0 = 0 and x * 1 = x
		 */
		final Term xTimes0 = QvasrAbstractor.simplifyRealMultiplication(mMgdScript, x, zero);
		MatcherAssert.assertThat(xTimes0, IsEqual.equalTo(zero));
		final Term xTimes1 = QvasrAbstractor.simplifyRealMultiplication(mMgdScript, x, one);
		MatcherAssert.assertThat(xTimes1, IsEqual.equalTo(x));

		/*
		 * Test (2y / (x + 1)) * (3 / y) = 6/(x + 1)
		 */
		final Term yOverXP1 = SmtUtils.divReal(mScript, SmtUtils.mul(mScript, "*", mScript.decimal("2"), y),
				SmtUtils.sum(mScript, "+", x, one));
		final Term threeOverY = SmtUtils.divReal(mScript, mScript.decimal("3"), y);
		final Term yOverXP1TimesThreeOverYResult =
				SmtUtils.divReal(mScript, mScript.decimal("6"), SmtUtils.sum(mScript, "+", x, one));
		final Term yOverXP1TimesThreeOverY =
				QvasrAbstractor.simplifyRealMultiplication(mMgdScript, yOverXP1, threeOverY);
		MatcherAssert.assertThat(yOverXP1TimesThreeOverY, IsEqual.equalTo(yOverXP1TimesThreeOverYResult));

		/*
		 * Test ((x + 2.0) / y) * (y / (x + 2)) = 1
		 */
		final Term yOverxP2 = SmtUtils.divReal(mScript, SmtUtils.sum(mScript, "+", x, mScript.decimal("2")), y);
		final Term xP2OverY = SmtUtils.divReal(mScript, y, SmtUtils.sum(mScript, "+", x, mScript.decimal("2")));
		final Term yOverxP2TimesxP2OverY = QvasrAbstractor.simplifyRealMultiplication(mMgdScript, yOverxP2, xP2OverY);
		MatcherAssert.assertThat(yOverxP2TimesxP2OverY, IsEqual.equalTo(one));

		/*
		 * Test 3 * (x / y) = 3x/y
		 */

		final Term xOverY = SmtUtils.divReal(mScript, x, y);
		final Term threeTimesXOverYResult =
				SmtUtils.divReal(mScript, SmtUtils.mul(mScript, "*", x, mScript.decimal("3")), y);
		final Term threeTimesXOverY =
				QvasrAbstractor.simplifyRealMultiplication(mMgdScript, mScript.decimal("3"), xOverY);
		MatcherAssert.assertThat(threeTimesXOverY, IsEqual.equalTo(threeTimesXOverYResult));

		/*
		 * Test y * (x / y) = x
		 */
		final Term yTimesXOverY = QvasrAbstractor.simplifyRealMultiplication(mMgdScript, y, xOverY);
		MatcherAssert.assertThat(yTimesXOverY, IsEqual.equalTo(x));
	}

	/**
	 * Test simplification of differences.
	 */
	@Test
	public void testSimplifyRealSubstraction() {
		final Term zero = mScript.decimal("0");
		final Term one = mScript.decimal("1");
		final TermVariable x = mScript.variable("x", mRealSort);
		final TermVariable y = mScript.variable("y", mRealSort);
		final TermVariable z = mScript.variable("z", mRealSort);

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
		final Term threeX = SmtUtils.mul(mScript, "*", mScript.decimal("3"), x);
		final Term twoX = SmtUtils.mul(mScript, "*", x, mScript.decimal("2"));
		final Term threeXMinX = QvasrAbstractor.simplifyRealSubtraction(mMgdScript, threeX, x);
		MatcherAssert.assertThat(threeXMinX, IsEqual.equalTo(twoX));

		/*
		 * Test (y / (x + 1)) - (y / (x + 1)) = 0
		 */
		final Term yOverXPOne = SmtUtils.divReal(mScript, y, SmtUtils.sum(mScript, "+", x, mScript.decimal("1")));
		final Term yOverXPOneMinYOverXPOne =
				QvasrAbstractor.simplifyRealSubtraction(mMgdScript, yOverXPOne, yOverXPOne);
		MatcherAssert.assertThat(yOverXPOneMinYOverXPOne, IsEqual.equalTo(zero));

		/*
		 * Test (3x / 2) - x = x/2
		 */
		final Term threeXOverTwo =
				SmtUtils.divReal(mScript, SmtUtils.mul(mScript, "*", mScript.decimal("3"), x), mScript.decimal("2"));
		final Term xOverTwo = SmtUtils.divReal(mScript, x, mScript.decimal("2"));
		final Term threeXOverTwoMinXOverTwo = QvasrAbstractor.simplifyRealSubtraction(mMgdScript, threeXOverTwo, x);
		MatcherAssert.assertThat(threeXOverTwoMinXOverTwo, IsEqual.equalTo(xOverTwo));

		/*
		 * Test x - (3x / 2) - x = -x/2
		 */
		final Term negX = SmtUtils.minus(mScript, zero, x);
		final Term negXOverTwo = SmtUtils.divReal(mScript, negX, mScript.decimal("2"));
		final Term xMinThreeXOverTwo = QvasrAbstractor.simplifyRealSubtraction(mMgdScript, x, threeXOverTwo);
		MatcherAssert.assertThat(xMinThreeXOverTwo, IsEqual.equalTo(negXOverTwo));

		/*
		 * Test ((x + y)/ z) - ((x + 3) / y) = (xy + y^2 - xz + 3z)/(zy)
		 */
		final Term xPYOverZ = SmtUtils.divReal(mScript, SmtUtils.sum(mScript, "+", x, y), z);
		final Term xPThreeOverY = SmtUtils.divReal(mScript, SmtUtils.sum(mScript, "+", x, mScript.decimal("3")), y);
		final Term zTimesMinThree = SmtUtils.mul(mScript, "*", z, mScript.decimal("-3"));
		final Term negXZ = SmtUtils.mul(mScript, "*", SmtUtils.mul(mScript, "*", x, z), mScript.decimal("-1"));
		final Term ySquare = SmtUtils.mul(mScript, "*", y, y);
		final Term xY = SmtUtils.mul(mScript, "*", x, y);
		final Term sumAll = SmtUtils.sum(mScript, "+", zTimesMinThree, negXZ, ySquare, xY);
		final Term xPYOverZMinxPThreeOverYResult = SmtUtils.divReal(mScript, sumAll, SmtUtils.mul(mScript, "*", z, y));
		final Term xPYOverZMinxPThreeOverY =
				QvasrAbstractor.simplifyRealSubtraction(mMgdScript, xPYOverZ, xPThreeOverY);
		MatcherAssert.assertThat(xPYOverZMinxPThreeOverY, IsEqual.equalTo(xPYOverZMinxPThreeOverYResult));
	}

	/**
	 * Test the simplification of divisions.
	 */
	@Test
	public void testReduceRealDivision() {
		final TermVariable x = mScript.variable("x", mRealSort);
		final TermVariable y = mScript.variable("y", mRealSort);
		final Term zero = mScript.decimal("0");
		final Term one = mScript.decimal("1");
		final Term three = mScript.decimal("3");
		final Term xPOne = SmtUtils.sum(mScript, "+", x, one);
		final Term yPThree = SmtUtils.sum(mScript, "+", y, mScript.decimal("3"));
		final Term xPY = SmtUtils.sum(mScript, "+", x, y);
		final Term xTimesXY = SmtUtils.mul(mScript, "*", x, yPThree);

		/*
		 * Test (x * (x + y))/ x * (y + 3) = (x + y)/(y + 3)
		 */
		final Term xy = SmtUtils.mul(mScript, "*", x, xPY);
		final Term xTimesXYOverxPyResult = SmtUtils.divReal(mScript, xPY, yPThree);
		final Pair<Term, Term> xyOverXReduced = QvasrAbstractor.reduceRealDivision(mMgdScript, xy, xTimesXY);
		MatcherAssert.assertThat(SmtUtils.divReal(mScript, xyOverXReduced.getFirst(), xyOverXReduced.getSecond()),
				IsEqual.equalTo(xTimesXYOverxPyResult));

		/*
		 * Test ((x + 1)(x + y)) / ((y + 3)(x + 1)) = (x + y)/(y + 3)
		 */
		final Term xPOneTimesXPY = SmtUtils.mul(mScript, "*", xPOne, xPY);
		final Term yPThreeTimesXPOne = SmtUtils.mul(mScript, "*", yPThree, xPOne);
		final Pair<Term, Term> xPOneTimesXPYOveryPThreeTimesXPOneReduced =
				QvasrAbstractor.reduceRealDivision(mMgdScript, xPOneTimesXPY, yPThreeTimesXPOne);
		MatcherAssert.assertThat(SmtUtils.divReal(mScript, xPOneTimesXPYOveryPThreeTimesXPOneReduced.getFirst(),
				xPOneTimesXPYOveryPThreeTimesXPOneReduced.getSecond()), IsEqual.equalTo(xTimesXYOverxPyResult));

		/*
		 * Test xy/xy(x + 1) = 1/(x + 1)
		 */
		final Term xTimesY = SmtUtils.mul(mScript, "*", x, y);
		final Term xYTimesxPOne = SmtUtils.mul(mScript, "*", xTimesY, xPOne);
		final Pair<Term, Term> xYOverxYTimesxPOneReduced =
				QvasrAbstractor.reduceRealDivision(mMgdScript, xTimesY, xYTimesxPOne);
		MatcherAssert.assertThat(
				SmtUtils.divReal(mScript, xYOverxYTimesxPOneReduced.getFirst(), xYOverxYTimesxPOneReduced.getSecond()),
				IsEqual.equalTo(SmtUtils.divReal(mScript, one, xPOne)));

		/*
		 * Test (x^2(x + 1)(x + y)) / ((x + 1) x^2 (y + 3)) = (x + y) / (y + 3)
		 */
		final Term xSquared = SmtUtils.mul(mScript, "*", x, x);
		final Term xSquaredTimesXPOneTimesXPY = SmtUtils.mul(mScript, "*", xSquared, xPOne, xPY);
		final Term xPOneTimesXSquaredTimesYPThree = SmtUtils.mul(mScript, "*", xPOne, xSquared, yPThree);
		final Pair<Term, Term> xSquaredTimesXPOneTimesXPYOverxPOneTimesXSquaredTimesYPThreeReduced = QvasrAbstractor
				.reduceRealDivision(mMgdScript, xSquaredTimesXPOneTimesXPY, xPOneTimesXSquaredTimesYPThree);
		final Term xSquaredTimesXPOneTimesXPYOverxPOneTimesXSquaredTimesYPThreeResult =
				SmtUtils.divReal(mScript, xPY, yPThree);
		MatcherAssert.assertThat(
				SmtUtils.divReal(mScript,
						xSquaredTimesXPOneTimesXPYOverxPOneTimesXSquaredTimesYPThreeReduced.getFirst(),
						xSquaredTimesXPOneTimesXPYOverxPOneTimesXSquaredTimesYPThreeReduced.getSecond()),
				IsEqual.equalTo(xSquaredTimesXPOneTimesXPYOverxPOneTimesXSquaredTimesYPThreeResult));

		/*
		 * Test 3x/x(x + 1) = 3/(x + 1)
		 */
		final Term threeTimesX = SmtUtils.mul(mScript, "*", three, x);
		final Term xTimesXPOne = SmtUtils.mul(mScript, "*", x, xPOne);
		final Pair<Term, Term> threeTimesXOverxTimesXPOne =
				QvasrAbstractor.reduceRealDivision(mMgdScript, threeTimesX, xTimesXPOne);
		MatcherAssert.assertThat(
				SmtUtils.divReal(mScript, threeTimesXOverxTimesXPOne.getFirst(),
						threeTimesXOverxTimesXPOne.getSecond()),
				IsEqual.equalTo(SmtUtils.divReal(mScript, three, xPOne)));

		/*
		 * Test -3x/x(x + 1) = -3/(x + 1)
		 */
		final Term negX = SmtUtils.minus(mScript, zero, x);
		final Term negThree = SmtUtils.minus(mScript, zero, three);
		final Term threeTimesNegX = SmtUtils.mul(mScript, "*", three, negX);
		final Pair<Term, Term> threeTimesNegXOverxTimesXPOne =
				QvasrAbstractor.reduceRealDivision(mMgdScript, threeTimesNegX, xTimesXPOne);
		MatcherAssert.assertThat(
				SmtUtils.divReal(mScript, threeTimesNegXOverxTimesXPOne.getFirst(),
						threeTimesNegXOverxTimesXPOne.getSecond()),
				IsEqual.equalTo(SmtUtils.divReal(mScript, negThree, xPOne)));

		/*
		 * Test 3 / 3x(x + 1) = 1 / x(x + 1)
		 */

		final Pair<Term, Term> threeOverThreeTimesXTimesXPOne =
				QvasrAbstractor.reduceRealDivision(mMgdScript, three, SmtUtils.mul(mScript, "*", three, xTimesXPOne));
		final Term threeOverThreeTimesXTimesXPOneResult = SmtUtils.divReal(mScript, one, xTimesXPOne);
		MatcherAssert.assertThat(
				SmtUtils.divReal(mScript, threeOverThreeTimesXTimesXPOne.getFirst(),
						threeOverThreeTimesXTimesXPOne.getSecond()),
				IsEqual.equalTo(threeOverThreeTimesXTimesXPOneResult));

		/*
		 * Test 3x / 3x(x + 1) = 1 / (x + 1)
		 */
		final Pair<Term, Term> threeTimesXOverThreeTimesXTimesXPOneReduced = QvasrAbstractor
				.reduceRealDivision(mMgdScript, threeTimesX, SmtUtils.mul(mScript, "*", threeTimesX, xPOne));
		MatcherAssert.assertThat(
				SmtUtils.divReal(mScript, threeTimesXOverThreeTimesXTimesXPOneReduced.getFirst(),
						threeTimesXOverThreeTimesXTimesXPOneReduced.getSecond()),
				IsEqual.equalTo(SmtUtils.divReal(mScript, one, xPOne)));

		/*
		 * Test 3x / 3x(x + 1) = 1 / (x + 1)
		 */
		final Term xPYPOne = SmtUtils.sum(mScript, "+", x, y, one);
		final Pair<Term, Term> xPYPOneTimesThreeXOverXPYPOne = QvasrAbstractor.reduceRealDivision(mMgdScript,
				SmtUtils.mul(mScript, "*", xPYPOne, threeTimesX), xPYPOne);
		MatcherAssert.assertThat(
				SmtUtils.divReal(mScript, xPYPOneTimesThreeXOverXPYPOne.getFirst(),
						xPYPOneTimesThreeXOverXPYPOne.getSecond()).toStringDirect(),
				IsEqual.equalTo(threeTimesX.toStringDirect()));
	}

}
