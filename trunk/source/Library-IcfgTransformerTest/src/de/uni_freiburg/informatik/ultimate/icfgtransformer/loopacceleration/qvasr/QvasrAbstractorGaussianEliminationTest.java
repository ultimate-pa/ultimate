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
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * A test suite for checking the functionality of the Gaussian elimination algorithm employed in the Qvasr-abstraction
 * scheme.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrAbstractorGaussianEliminationTest {

	private Script mScript;
	private ManagedScript mMgdScript;

	private Term mX;
	private Term mY;
	private Term mA;

	private Term mTwo;
	private Term mOne;
	private Term mZero;

	/**
	 * Set up
	 */
	@Before
	public void setUp() {
		final IUltimateServiceProvider mServices = UltimateMocks.createUltimateServiceProviderMock();
		mScript = UltimateMocks.createZ3Script();
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		final ILogger mLogger = mServices.getLoggingService().getLogger("log");
		mLogger.info("Before");
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		mScript.declareFun("a", new Sort[0], realSort);

		mX = TermParseUtils.parseTerm(mScript, "x");
		mY = TermParseUtils.parseTerm(mScript, "y");
		mA = TermParseUtils.parseTerm(mScript, "a");

		mZero = mScript.decimal("0");
		mOne = mScript.decimal("1");
		mTwo = mScript.decimal("2");
	}

	/**
	 * Test solving of {{1, 0, 0}, {0, 1, 0}} = {{1, 0, 0}, {0, 1, 0}}
	 */
	@Test
	public void testGaussianElimination0() {
		Term[][] matrix = { { mOne, mZero, mZero }, { mZero, mOne, mZero } };
		matrix = QvasrAbstractor.gaussianSolve(mMgdScript, matrix);
		final Term[][] result = { { mOne, mZero, mZero }, { mZero, mOne, mZero } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x, 1, 0}, {1, x, 0}} = {{1, 0, 0}, {0, 1, 0}}
	 */
	@Test
	public void testGaussianElimination1() {
		Term[][] matrix = { { mX, mOne, mZero }, { mOne, mX, mZero } };
		matrix = QvasrAbstractor.gaussianSolve(mMgdScript, matrix);
		final Term[][] result = { { mOne, mZero, mZero }, { mZero, mOne, mZero } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x, 0, 2}, {1, 2, 0}} = {{1, 0, 2/x}, {0, 1, -1/x}}
	 */
	@Test
	public void testGaussianElimination2() {
		Term[][] matrix = { { mX, mZero, mTwo }, { mOne, mTwo, mZero } };
		matrix = QvasrAbstractor.gaussianSolve(mMgdScript, matrix);
		final Term div1 = TermParseUtils.parseTerm(mScript, "(/ 2.0 x)");
		final Term div2 = TermParseUtils.parseTerm(mScript, "(/ (- 1.0) x)");
		final Term[][] result = { { mOne, mZero, div1 }, { mZero, mOne, div2 } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x, 0, 2}, {1, y, 0}} = {{1, 0, 2/x}, {0, 1, -2/xy}}
	 */
	@Test
	public void testGaussianElimination3() {
		Term[][] matrix = { { mX, mZero, mTwo }, { mOne, mY, mZero } };
		matrix = QvasrAbstractor.gaussianSolve(mMgdScript, matrix);
		final Term div1 = TermParseUtils.parseTerm(mScript, "(/ 2.0 x)");
		final Term div2 = TermParseUtils.parseTerm(mScript, "(/ (- 2.0) (* x y))");
		final Term[][] result = { { mOne, mZero, div1 }, { mZero, mOne, div2 } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x, 0, y}, {1, y, 0}} = {{1, 0, y/x}, {0, 1, -1/x}}
	 */
	@Test
	public void testGaussianElimination4() {
		Term[][] matrix = { { mX, mZero, mY }, { mOne, mY, mZero } };
		matrix = QvasrAbstractor.gaussianSolve(mMgdScript, matrix);
		final Term div1 = TermParseUtils.parseTerm(mScript, "(/ y x)");
		final Term div2 = TermParseUtils.parseTerm(mScript, "(/ (- 1.0) x)");
		final Term[][] result = { { mOne, mZero, div1 }, { mZero, mOne, div2 } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x + 1, x + y + 1, a}, {1, y + 1, a}} = {{1, 0, 0}, {0, 1, 0}}
	 */
	@Test
	public void testGaussianElimination5() {
		final Term xPYP1 = TermParseUtils.parseTerm(mScript, "(+ x y 1.0)");
		final Term yP1 = TermParseUtils.parseTerm(mScript, "(+ y 1.0)");
		final Term xP1 = TermParseUtils.parseTerm(mScript, "(+ x 1.0)");

		Term[][] matrix = { { xP1, xPYP1, mA }, { mOne, yP1, mA }, { xP1, xP1, mA }, { mOne, mOne, mA } };
		matrix = QvasrAbstractor.gaussianSolve(mMgdScript, matrix);
		final Term[][] result = { { mOne, mZero, mZero }, { mZero, mOne, mZero }, { mZero, mZero, mOne } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x + 1, 2, a}, {1, 2, a}} = {{1, 0, 0}, {0, 1, a/2}}
	 */
	@Test
	public void testGaussianElimination6() {
		final Term xP1 = TermParseUtils.parseTerm(mScript, "(+ x 1.0)");

		Term[][] matrix = { { xP1, mTwo, mA }, { mOne, mTwo, mA }, { xP1, mTwo, mA }, { mOne, mTwo, mA } };
		matrix = QvasrAbstractor.gaussianSolve(mMgdScript, matrix);
		final Term[][] result =
				{ { mOne, mZero, mZero }, { mZero, mOne, TermParseUtils.parseTerm(mScript, "(/ a 2.0)") } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x + y, x + y, a}, {y, y, a}, {x, x, a}, {0, 0, a}} = {{1, 1, 0}, {0, 0, 1}}
	 */
	@Test
	public void testGaussianElimination7() {
		final Term xPY = TermParseUtils.parseTerm(mScript, "(+ x y)");

		Term[][] matrix = { { xPY, xPY, mA }, { mY, mY, mA }, { mX, mX, mA }, { mZero, mZero, mA } };
		matrix = QvasrAbstractor.gaussianSolve(mMgdScript, matrix);
		final Term[][] result = { { mOne, mOne, mZero }, { mZero, mZero, mOne } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{x + y, x + y + y, a}, {y, y + y, a}, {x, x, a}, {0, 0, a}} = {{1, 0, 0}, {0, 1, 0}, {0, 0, 1}}
	 */
	@Test
	public void testGaussianElimination8() {
		final Term xPY = TermParseUtils.parseTerm(mScript, "(+ x y)");
		final Term xPYPY = TermParseUtils.parseTerm(mScript, "(+ x y y)");
		final Term yPY = TermParseUtils.parseTerm(mScript, "(+ y y)");

		Term[][] matrix = { { xPY, xPYPY, mA }, { mY, yPY, mA }, { mX, mX, mA }, { mZero, mZero, mA } };
		matrix = QvasrAbstractor.gaussianSolve(mMgdScript, matrix);
		final Term[][] result = { { mOne, mZero, mZero }, { mZero, mOne, mZero }, { mZero, mZero, mOne } };
		testMatrixEquality(matrix, result);
	}

	/**
	 * Test solving of {{1, 1, 1}, {1, 1, 0}} = {{1, 1, 0}, {0, 0, 1}}
	 */
	@Test
	public void testGaussianElimination9() {
		Term[][] matrix = { { mOne, mOne, mOne }, { mOne, mOne, mZero } };
		matrix = QvasrAbstractor.gaussianSolve(mMgdScript, matrix);
		final Term[][] result = { { mOne, mOne, mZero }, { mZero, mZero, mOne } };
		testMatrixEquality(matrix, result);
	}

	static void testMatrixEquality(final Term[][] matrix1, final Term[][] matrix2) {
		MatcherAssert.assertThat(matrix1.length, IsEqual.equalTo(matrix2.length));
		MatcherAssert.assertThat(matrix1[0].length, IsEqual.equalTo(matrix2[0].length));
		for (int i = 0; i < matrix1.length; i++) {
			for (int j = 0; j < matrix1[0].length; j++) {
				MatcherAssert.assertThat(matrix1[i][j], IsEqual.equalTo(matrix2[i][j]));
			}
		}
	}

}
