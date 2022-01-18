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

import java.math.BigInteger;

import org.hamcrest.MatcherAssert;
import org.hamcrest.core.IsEqual;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

/**
 * Testsuite for the {@link QvasrVectorSpaceBasisConstructor}.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrVectorSpaceBasisConstructorTest {

	private ManagedScript mMgdScript;

	private Term mFour;
	private Term mThree;
	private Term mTwo;
	private Term mOne;
	private Term mZero;

	/**
	 * Testsuite setup.
	 */
	@Before
	public void setUp() {
		final IUltimateServiceProvider mServices = UltimateMocks.createUltimateServiceProviderMock();
		final Script mScript = UltimateMocks.createZ3Script();
		mMgdScript = new ManagedScript(mServices, mScript);
		mScript.setLogic(Logics.ALL);
		final Sort realSort = SmtSortUtils.getRealSort(mMgdScript);
		final ILogger mLogger = mServices.getLoggingService().getLogger("log");
		mLogger.info("Before");
		mScript.declareFun("x", new Sort[0], realSort);
		mScript.declareFun("y", new Sort[0], realSort);
		mScript.declareFun("a", new Sort[0], realSort);

		mZero = mScript.decimal("0");
		mOne = mScript.decimal("1");
		mTwo = mScript.decimal("2");
		mThree = mScript.decimal("3");
		mFour = mScript.decimal("4");
	}

	/**
	 * Test Vector basis for {{1, 0, 1}, {0, 1, 1}} = {1, 1, 1}
	 */
	@Test
	public void testSolutionBuilding0() {
		final Term[][] matrix = { { mOne, mZero, mOne }, { mZero, mOne, mOne } };
		final Rational[][] vectorSpaceBasis =
				QvasrVectorSpaceBasisConstructor.computeVectorSpaceBasis(mMgdScript, matrix);
		final Integer[][] vectorSpaceBasisResult = { { 1, 1, 1 } };
		testBasisVectorEquality(vectorSpaceBasis, integerMatrixToRationalMatrix(vectorSpaceBasisResult));
	}

	/**
	 * Test Vector basis for {{1, 0, 2, 1}, {0, 1, 3, 1}} = {{-2, -3, 1, 0}, {1, 1, 0, 1}}
	 */
	@Test
	public void testSolutionBuilding1() {
		final Term[][] matrix = { { mOne, mZero, mTwo, mOne }, { mZero, mOne, mThree, mOne } };
		final Rational[][] vectorSpaceBasis =
				QvasrVectorSpaceBasisConstructor.computeVectorSpaceBasis(mMgdScript, matrix);
		final Integer[][] vectorSpaceBasisResult = { { 1, 1, 0, 1 }, { -2, -3, 1, 0 } };
		testBasisVectorEquality(vectorSpaceBasis, integerMatrixToRationalMatrix(vectorSpaceBasisResult));
	}

	/**
	 * Test Vector basis for {{1, 0, 0, 4}, {0, 1, 0, 2}, {0, 0, 1, -1}} = {{4, 2, -1, 1}}
	 */
	@Test
	public void testSolutionBuilding2() {
		final Term negOne = mMgdScript.getScript().decimal("-1");
		final Term[][] matrix =
				{ { mOne, mZero, mZero, mFour }, { mZero, mOne, mZero, mTwo }, { mZero, mZero, mOne, negOne } };
		final Rational[][] vectorSpaceBasis =
				QvasrVectorSpaceBasisConstructor.computeVectorSpaceBasis(mMgdScript, matrix);
		final Integer[][] vectorSpaceBasisResult = { { 4, 2, -1, 1 } };
		testBasisVectorEquality(vectorSpaceBasis, integerMatrixToRationalMatrix(vectorSpaceBasisResult));
	}

	/**
	 * Test Vector basis for {{1, 1, 1, 4}} = {{-1, 1, 0, 0}, {-1, 0, 1, 0}, {4, 0, 0, 1}}
	 */
	@Test
	public void testSolutionBuilding3() {
		final Term[][] matrix = { { mOne, mOne, mOne, mFour } };
		final Rational[][] vectorSpaceBasis =
				QvasrVectorSpaceBasisConstructor.computeVectorSpaceBasis(mMgdScript, matrix);
		final Integer[][] vectorSpaceBasisResult = { { 4, 0, 0, 1 }, { -1, 0, 1, 0 }, { -1, 1, 0, 0 } };
		testBasisVectorEquality(vectorSpaceBasis, integerMatrixToRationalMatrix(vectorSpaceBasisResult));
	}

	/**
	 * Test Vector basis for {{1, 1, 0}, {0, 0, 1}} = {{-1, 1, 0 }} (This is the solution for s_1(x + y) + s_(x + y) =
	 * a)
	 */
	@Test
	public void testSolutionBuilding4() {
		final Term[][] matrix = { { mOne, mOne, mZero }, { mZero, mZero, mOne } };
		final Rational[][] vectorSpaceBasis =
				QvasrVectorSpaceBasisConstructor.computeVectorSpaceBasis(mMgdScript, matrix);
		final Integer[][] vectorSpaceBasisResult = { { -1, 1, 0 } };
		testBasisVectorEquality(vectorSpaceBasis, integerMatrixToRationalMatrix(vectorSpaceBasisResult));
	}

	/**
	 * Test Vector basis for {{1, 2, 1, 0}} = {{-2, 1, 0, 0}, {-1, 0, 1, 0}}
	 */
	@Test
	public void testSolutionBuilding5() {
		final Term[][] matrix = { { mOne, mTwo, mOne, mZero } };
		final Rational[][] vectorSpaceBasis =
				QvasrVectorSpaceBasisConstructor.computeVectorSpaceBasis(mMgdScript, matrix);
		final Integer[][] vectorSpaceBasisResult = { { -1, 0, 1, 0 }, { -2, 1, 0, 0 } };
		testBasisVectorEquality(vectorSpaceBasis, integerMatrixToRationalMatrix(vectorSpaceBasisResult));
	}

	/**
	 * Test Vector basis for {{1, 0, 0, 4}, {0, 1, 1, 2}} = {{4, 2, -1, 1}}
	 */
	@Test
	public void testSolutionBuilding6() {
		final Term[][] matrix = { { mOne, mZero, mZero, mFour }, { mZero, mOne, mOne, mTwo } };
		final Rational[][] vectorSpaceBasis =
				QvasrVectorSpaceBasisConstructor.computeVectorSpaceBasis(mMgdScript, matrix);
		final Integer[][] vectorSpaceBasisResult = { { 4, 2, 0, 1 }, { 0, -1, 1, 0 } };
		testBasisVectorEquality(vectorSpaceBasis, integerMatrixToRationalMatrix(vectorSpaceBasisResult));
	}

	/**
	 * Test Vector basis for {{1, 0, 2, 3}, {0, 1, -3, 4}} = {{3, 4, 0, 1}, {-2, 3, 1, 0}}
	 */
	@Test
	public void testSolutionBuilding7() {
		final Term negThree = mMgdScript.getScript().decimal("-3");
		final Term[][] matrix = { { mOne, mZero, mTwo, mThree }, { mZero, mOne, negThree, mFour } };
		final Rational[][] vectorSpaceBasis =
				QvasrVectorSpaceBasisConstructor.computeVectorSpaceBasis(mMgdScript, matrix);
		final Integer[][] vectorSpaceBasisResult = { { 3, 4, 0, 1 }, { -2, 3, 1, 0 } };
		testBasisVectorEquality(vectorSpaceBasis, integerMatrixToRationalMatrix(vectorSpaceBasisResult));
	}

	/**
	 * Test Vector basis for {{1, 0, 1}, {0, 1, 0}} = {{1, 0, 1}}
	 */
	@Test
	public void testSolutionBuilding8() {
		final Term[][] matrix = { { mOne, mZero, mOne }, { mZero, mOne, mZero } };
		final Rational[][] vectorSpaceBasis =
				QvasrVectorSpaceBasisConstructor.computeVectorSpaceBasis(mMgdScript, matrix);
		final Integer[][] vectorSpaceBasisResult = { { 1, 0, 1 } };
		testBasisVectorEquality(vectorSpaceBasis, integerMatrixToRationalMatrix(vectorSpaceBasisResult));
	}

	/**
	 * Convert an integer matrix to a rational matrix. Needed for easier parsing of matrices.
	 *
	 * @param matrix
	 *            The matrix that is to be converted.
	 * @return Input matrix consisting of {@link Rational}.
	 */
	public static Rational[][] integerMatrixToRationalMatrix(final Integer[][] matrix) {
		final Rational[][] matrixRational = new Rational[matrix.length][matrix[0].length];
		for (int i = 0; i < matrix.length; i++) {
			for (int j = 0; j < matrix[0].length; j++) {
				matrixRational[i][j] = Rational.valueOf(new BigInteger(matrix[i][j].toString()), BigInteger.ONE);
			}
		}
		return matrixRational;

	}

	/**
	 * Convert an integer vector to a rational vector. Needed for easier parsing of matrices.
	 *
	 * @param vector
	 *            The vector that is to be converted.
	 * @return Input vector consisting of {@link Rational}.
	 */
	public static Rational[] integerVectorToRationalVector(final Integer[] vector) {
		final Rational[] matrixRational = new Rational[vector.length];
		for (int i = 0; i < vector.length; i++) {
			matrixRational[i] = Rational.valueOf(new BigInteger(vector[i].toString()), BigInteger.ONE);
		}
		return matrixRational;
	}

	static void testBasisVectorEquality(final Rational[][] matrix1, final Rational[][] matrix2) {
		MatcherAssert.assertThat(matrix1.length, IsEqual.equalTo(matrix2.length));
		MatcherAssert.assertThat(matrix1[0].length, IsEqual.equalTo(matrix2[0].length));
		for (int i = 0; i < matrix1.length; i++) {
			for (int j = 0; j < matrix1[0].length; j++) {
				MatcherAssert.assertThat(matrix1[i][j], IsEqual.equalTo(matrix2[i][j]));
			}
		}
	}

}
