/*
 * Copyright (C) 2021 Miriam Herzig
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;

import java.math.BigInteger;
import java.util.Random;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Test class for QuadraticMatrix.
 *
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuadraticMatrixTest {

	/**
	 * Function that checks if two quadratic matrices are identical meaning they are of the same dimension and have the
	 * same entries.
	 */
	static void checkMatrixEquality(final QuadraticMatrix matrix1, final QuadraticMatrix matrix2) {
		assertEquals(matrix1.getDimension(), matrix2.getDimension());
		final int n = matrix1.getDimension();
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				checkBigIntegerEquality(matrix1.getEntry(i, j), matrix2.getEntry(i, j));
			}
		}
	}

	/**
	 * Function that checks if two BigInteger are identical
	 */
	static void checkBigIntegerEquality(final BigInteger a, final BigInteger b) {
		assertEquals(a.intValue(), b.intValue());
	}

	/**
	 * Create a random quadratic matrix of dimension n. Used for nontrivial test cases.
	 */
	QuadraticMatrix createRandomMatrix(final int n) {
		final Random random = new Random(10);
		final BigInteger[][] randomEntries = new BigInteger[n][n];
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				randomEntries[i][j] = BigInteger.valueOf(random.nextInt());
			}
		}
		final QuadraticMatrix Random = new QuadraticMatrix(randomEntries);
		return Random;
	}

	/**
	 * Transform an integer array of arrays to a BigInteger QUadraticMatrix.
	 */
	public static QuadraticMatrix intToBigInteger(final int[][] entries) {
		final int n = entries.length;
		final QuadraticMatrix bigIntegerMatrix = QuadraticMatrix.constructZeroMatrix(n);
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				bigIntegerMatrix.setEntry(i, j, BigInteger.valueOf(entries[i][j]));
			}
		}
		return bigIntegerMatrix;
	}

	/**
	 * Tests function {@link QuadraticMatrix#constructIdentityMatrix(int)}.
	 */
	@Test
	public void testIdentityMatrix() {
		final int n = 10;
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(n);
		assertEquals(n, E.getDimension());
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				if (i == j) {
					checkBigIntegerEquality(BigInteger.valueOf(1), E.getEntry(i, j));
				} else {
					checkBigIntegerEquality(BigInteger.valueOf(0), E.getEntry(i, j));
				}
			}
		}
	}

	/**
	 * Tests function {@link QuadraticMatrix#copyMatrix(QuadraticMatrix)}.
	 */
	@Test
	public void testCopyMatrix() {
		// Create matrix of dimension 10 with random entries.
		final QuadraticMatrix A1 = createRandomMatrix(10);
		// Copy matrix.
		final QuadraticMatrix A2 = QuadraticMatrix.copyMatrix(A1);
		// Test whether the matrices are equal.
		checkMatrixEquality(A1, A2);
		// Test whether the matrices do not have the same pointer.
		assertNotEquals(A1, A2);
	}

	/**
	 * Tests the function {@link QuadraticMatrix#addition(QuadraticMatrix, QuadraticMatrix)}.
	 */
	@Test
	public void testAddition() {
		// First case: add zero-matrix to random matrix
		final QuadraticMatrix A = createRandomMatrix(5);
		final QuadraticMatrix zeroMatrix = QuadraticMatrix.constructZeroMatrix(5);
		final QuadraticMatrix Sum = QuadraticMatrix.addition(A, zeroMatrix);
		// Test whether A and Sum have the same dimension and the same entries.
		checkMatrixEquality(A, Sum);
		// Test whether the matrices do not have the same pointer.
		assertNotEquals(A, Sum);

		// Second case: two non-zero matrices.
		final int[][] entries_1 = { { 1, 3, 5, 4 }, { -3, -5, 6, 0 }, { 1, 4, 6, -1 }, { 0, 0, 0, 1 } };
		final int[][] entries_2 = { { 8, 3, 5, 12 }, { 1, -2, -1, 2 }, { 0, 1, 0, 1 }, { 0, 1, 3, 1 } };
		final int[][] entries_sum = { { 9, 6, 10, 16 }, { -2, -7, 5, 2 }, { 1, 5, 6, 0 }, { 0, 1, 3, 2 } };
		final QuadraticMatrix A_1 = intToBigInteger(entries_1);
		final QuadraticMatrix A_2 = intToBigInteger(entries_2);
		final QuadraticMatrix Sum_1 = intToBigInteger(entries_sum);
		final QuadraticMatrix Sum_2 = QuadraticMatrix.addition(A_1, A_2);
		checkMatrixEquality(Sum_1, Sum_2);
	}

	/**
	 * Tests the function {@link QuadraticMatrix#scalarMultiplication(BigInteger, QuadraticMatrix)}.
	 */
	@Test
	public void testScalarMultiplication() {
		// First case: a=0.
		final BigInteger a1 = BigInteger.valueOf(0);
		final QuadraticMatrix M1 = createRandomMatrix(5);
		final QuadraticMatrix Zero = QuadraticMatrix.constructZeroMatrix(5);
		final QuadraticMatrix a1_M1 = QuadraticMatrix.scalarMultiplication(a1, M1);
		checkMatrixEquality(a1_M1, Zero);

		// Second case: a != 0.
		final BigInteger a2 = BigInteger.valueOf(2);
		final int[][] entries_m2 = { { 2, 4, -1 }, { 2, 0, -5 }, { 3, 1, -1 } };
		final int[][] a_entries_m2 = { { 4, 8, -2 }, { 4, 0, -10 }, { 6, 2, -2 } };
		final QuadraticMatrix M2 = intToBigInteger(entries_m2);
		final QuadraticMatrix a2_M2 = intToBigInteger(a_entries_m2);
		final QuadraticMatrix a2_M2_2 = QuadraticMatrix.scalarMultiplication(a2, M2);
		checkMatrixEquality(a2_M2, a2_M2_2);
	}

	/**
	 * Tests the function {@link QuadraticMatrix#multiplication(QuadraticMatrix, QuadraticMatrix)}.
	 */
	@Test
	public void testMultiplication() {
		// First case: multiply identity matrix to random matrix.
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(6);
		final QuadraticMatrix M1 = createRandomMatrix(6);
		final QuadraticMatrix E_M1 = QuadraticMatrix.multiplication(E, M1);
		checkMatrixEquality(E_M1, M1);

		// Second case: two nontrivial matrices.
		final int[][] entries_1 = { { 2, 4, 5, 0 }, { 3, 4, -1, -2 }, { 9, 0, 0, 1 }, { 1, 2, 0, 0 } };
		final int[][] entries_2 = { { 3, 4, -2, 0 }, { 7, 2, 1, 0 }, { -2, -1, -1, 0 }, { 0, 1, -1, 0 } };
		final int[][] entries_res = { { 24, 11, -5, 0 }, { 39, 19, 1, 0 }, { 27, 37, -19, 0 }, { 17, 8, 0, 0 } };
		final QuadraticMatrix M_1 = intToBigInteger(entries_1);
		final QuadraticMatrix M_2 = intToBigInteger(entries_2);
		final QuadraticMatrix M_res = intToBigInteger(entries_res);
		final QuadraticMatrix M_1M_2 = QuadraticMatrix.multiplication(M_1, M_2);
		checkMatrixEquality(M_res, M_1M_2);
	}

	/**
	 * Tests the function {@link QuadraticMatrix#power(QuadraticMatrix, int)}.
	 */
	@Test
	public void testPower() {
		// First case: identity matrix.
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(5);
		final QuadraticMatrix E_4 = QuadraticMatrix.power(E, 4);
		checkMatrixEquality(E, E_4);

		// Second case: nontrivial matrix.
		final int[][] entries = { { 1, 4, 3 }, { -1, 0, 2 }, { 2, -1, -3 } };
		final int[][] entries_res = { { 6, 10, 5 }, { -9, 21, 24 }, { 12, -25, -26 } };
		final QuadraticMatrix M = intToBigInteger(entries);
		final QuadraticMatrix Res = intToBigInteger(entries_res);
		final QuadraticMatrix M_3 = QuadraticMatrix.power(M, 3);
		checkMatrixEquality(Res, M_3);
	}

	/**
	 * Tests the function {@link QuadraticMatrix#computeDet()}.
	 */
	@Test
	public void testDet() {
		// First case: identity matrix
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(5);
		checkBigIntegerEquality(BigInteger.valueOf(1), E.computeDet());
		// assertEquals(1, E.det());

		// Second case: nontrivial invertible matrix.
		final int[][] entries_1 = { { 1, 3, -1, 1 }, { 2, 6, -2, 2 }, { 1, 0, 0, 3 }, { 1, 2, -1, 0 } };
		final QuadraticMatrix M_1 = intToBigInteger(entries_1);
		checkBigIntegerEquality(BigInteger.valueOf(0), M_1.computeDet());
		// assertEquals(0,M_1.det());

		// Third case: nontrivial not invertible matrix.
		final int[][] entries_2 = { { 1, 2, 4, 2 }, { 1, 6, 5, 4 }, { 2, -1, 5, 0 }, { 9, -3, 1, 0 } };
		final QuadraticMatrix M_2 = intToBigInteger(entries_2);
		checkBigIntegerEquality(BigInteger.valueOf(-126), M_2.computeDet());
		// assertEquals(-126,M_2.det());
	}

	/**
	 * Tests the function {@link QuadraticMatrix#computeInverse(QuadraticMatrix)}
	 */
	@Test
	public void testInverse() {
		// identity matrix.
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(6);
		final RationalMatrix E_inverse = QuadraticMatrix.computeInverse(E);
		checkMatrixEquality(E, E_inverse.getIntMatrix());
		checkBigIntegerEquality(BigInteger.valueOf(1), E_inverse.getDenominator());
		// assertEquals(1, E_inverse.mDenominator);

		// Nontrivial matrix.
		final int[][] M1_entries = { { 1, 1, 0, 2 }, { 1, 0, 1, 1 }, { 0, 0, 1, -1 }, { 0, 0, 0, 1 } };
		final QuadraticMatrix M1 = intToBigInteger(M1_entries);
		final RationalMatrix Inverse1 = QuadraticMatrix.computeInverse(M1);
		final QuadraticMatrix E1 = QuadraticMatrix.scalarMultiplication(Inverse1.getDenominator(),
				QuadraticMatrix.constructIdentityMatrix(4));
		checkMatrixEquality(QuadraticMatrix.multiplication(M1, Inverse1.getIntMatrix()), E1);
		checkMatrixEquality(QuadraticMatrix.multiplication(Inverse1.getIntMatrix(), M1), E1);

		// Nontrivial matrix with non-integer entries in inverse.
		final int[][] M2_entries = { { 2, 3, 1 }, { 2, 4, -1 }, { -2, 0, 1 } };
		final QuadraticMatrix M2 = intToBigInteger(M2_entries);
		final RationalMatrix Inverse2 = QuadraticMatrix.computeInverse(M2);
		final QuadraticMatrix E2 = QuadraticMatrix.scalarMultiplication(Inverse2.getDenominator(),
				QuadraticMatrix.constructIdentityMatrix(3));
		checkMatrixEquality(QuadraticMatrix.multiplication(M2, Inverse2.getIntMatrix()), E2);
		checkMatrixEquality(QuadraticMatrix.multiplication(Inverse2.getIntMatrix(), M2), E2);
	}

	/**
	 * Tests the function {@link QuadraticMatrix#computeSmallEigenvalues()}.
	 */
	@Test
	public void testSmallEigenvalues() {
		// Identity matrix.
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(4);
		final boolean[] E_eigenvalues = E.computeSmallEigenvalues();
		assertEquals(false, E_eigenvalues[0]);
		assertEquals(false, E_eigenvalues[1]);
		assertEquals(true, E_eigenvalues[2]);

		// Zero-matrix.
		final QuadraticMatrix Zero = QuadraticMatrix.constructZeroMatrix(5);
		final boolean[] Zero_eigenvalues = Zero.computeSmallEigenvalues();
		assertEquals(false, Zero_eigenvalues[0]);
		assertEquals(true, Zero_eigenvalues[1]);
		assertEquals(false, Zero_eigenvalues[2]);

		// Non-trivial matrix with eigenvalues -1,0,1.
		final int[][] M_entries = { { -1, 0, 3 }, { -1, 0, 2 }, { 0, 0, 1 } };
		final QuadraticMatrix M = intToBigInteger(M_entries);
		final boolean[] M_eigenvalues = M.computeSmallEigenvalues();
		assertEquals(true, M_eigenvalues[0]);
		assertEquals(true, M_eigenvalues[1]);
		assertEquals(true, M_eigenvalues[2]);
	}

	/**
	 * Tests the function {@link QuadraticMatrix#swapRows(int, int)}.
	 */
	@Test
	public void testSwapRows() {
		final int[][] entries = { { 1, 2, 3 }, { 4, 5, 6 }, { 7, 8, 9 } };
		final int[][] entries_swapped = { { 4, 5, 6 }, { 1, 2, 3 }, { 7, 8, 9 } };
		final QuadraticMatrix M = intToBigInteger(entries);
		final QuadraticMatrix M_swapped = intToBigInteger(entries_swapped);
		// Test whether rows are swapped correctly.
		M.swapRows(0, 1);
		checkMatrixEquality(M_swapped, M);
	}

	/**
	 * Tests the function {@link QuadraticMatrix#gaussElimination(QuadraticMatrix)}.
	 */
	@Test
	public void testGaussElimination() {
		// First case: identity matrix.
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(4);
		final BigInteger denominator = BigInteger.valueOf(1);
		final RationalMatrix GE = new RationalMatrix(BigInteger.valueOf(1), E);
		assertEquals(denominator, GE.getDenominator());
		checkMatrixEquality(E, GE.getIntMatrix());

		// Second case: random upper triangle matrix.
		final int[][] entries_1 = new int[4][4];
		final Random random = new Random(10);
		for (int i = 0; i < 4; i++) {
			for (int j = 0; j < 4; j++) {
				if (i <= j) {
					entries_1[i][j] = random.nextInt();
				} else {
					entries_1[i][j] = 0;
				}
			}
		}
		final QuadraticMatrix M_1 = intToBigInteger(entries_1);
		final RationalMatrix GM_1 = new RationalMatrix(BigInteger.valueOf(1), M_1);
		assertEquals(denominator, GM_1.getDenominator());
		checkMatrixEquality(M_1, GM_1.getIntMatrix());

		// Third case: nontrivial matrix.
		final int[][] entries_2 = { { 1, -2, 5, 1 }, { 2, 1, -1, 0 }, { 0, 0, 1, 2 }, { -1, 2, 3, 0 } };
		final QuadraticMatrix M_2 = intToBigInteger(entries_2);
		final int[][] entries_res = { { 2, 1, -1, 0 }, { 0, -5, 11, 2 }, { 0, 0, -16, -2 }, { 0, 0, 0, -30 } };
		final QuadraticMatrix Res = intToBigInteger(entries_res);
		checkMatrixEquality(Res, QuadraticMatrix.gaussElimination(M_2));
	}

	/**
	 * Tests the function {@link QuadraticMatrix#backwardSubstitution(QuadraticMatrix, int)}.
	 */
	@Test
	public void testBackwardSubstitution() {
		// Identity matrix.
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(4);
		final QuadraticMatrix GE = QuadraticMatrix.gaussElimination(E);
		final Rational[] x = QuadraticMatrix.backwardSubstitution(GE, 1);
		for (int i = 0; i < 3; i++) {
			checkBigIntegerEquality(BigInteger.valueOf(0), x[i].numerator());
			// assertEquals(0, x[i].numerator());
		}

		// Nontrivial matrix.
		final int[][] M1_entries = { { 1, -2, 5 }, { 2, 1, -1 }, { 0, 0, 1 } };
		final QuadraticMatrix M1 = intToBigInteger(M1_entries);
		final QuadraticMatrix GM1 = QuadraticMatrix.gaussElimination(M1);
		final Rational[] xM1 = QuadraticMatrix.backwardSubstitution(GM1, 1);
		checkBigIntegerEquality(BigInteger.valueOf(3), xM1[0].numerator());
		// assertEquals(3, xM1[0].numerator());
		checkBigIntegerEquality(BigInteger.valueOf(5), xM1[0].denominator());
		// assertEquals(5, xM1[0].denominator());
		checkBigIntegerEquality(BigInteger.valueOf(-11), xM1[1].numerator());
		// assertEquals(11, xM1[1].numerator());
		checkBigIntegerEquality(BigInteger.valueOf(5), xM1[1].denominator());
		// assertEquals(-5, xM1[1].denominator());

		// Another nontrivial matrix.
		final int[][] M2_entries = { { 1, 1, 0, 2 }, { 1, 0, 1, 1 }, { 0, 0, 1, -1 }, { 0, 0, 0, 1 } };
		final QuadraticMatrix M2 = intToBigInteger(M2_entries);
		final QuadraticMatrix GM2 = QuadraticMatrix.gaussElimination(M2);
		final Rational[] xM2 = QuadraticMatrix.backwardSubstitution(GM2, 1);
		checkBigIntegerEquality(BigInteger.valueOf(2), xM2[0].numerator());
		// assertEquals(2, xM2[0].numerator());
		checkBigIntegerEquality(BigInteger.valueOf(1), xM2[0].denominator());
		// assertEquals(1, xM2[0].denominator());
		checkBigIntegerEquality(BigInteger.valueOf(0), xM2[1].numerator());
		// assertEquals(0, xM2[1].numerator());
		checkBigIntegerEquality(BigInteger.valueOf(-1), xM2[2].numerator());
		// assertEquals(-1, xM2[2].numerator());
		checkBigIntegerEquality(BigInteger.valueOf(1), xM2[2].denominator());
		// assertEquals(1, xM2[2].denominator());
	}

	/**
	 * Tests the function {@link QuadraticMatrix#computeRank()}.
	 */
	@Test
	public void testRank() {
		// identity matrix.
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(4);
		assertEquals(4, E.computeRank());

		// zero matrix.
		final QuadraticMatrix Zero = QuadraticMatrix.constructZeroMatrix(10);
		assertEquals(0, Zero.computeRank());

		// Non trivial matrix with full rank.
		final int[][] M1_entries = { { 1, 2, -1 }, { 0, 1, 2 }, { 0, 0, 1 } };
		final QuadraticMatrix M1 = intToBigInteger(M1_entries);
		assertEquals(3, M1.computeRank());

		// Non trivial matrix with not full rank.
		final int[][] M2_entries = { { 1, 2, -1, 0 }, { 0, 1, 2, 0 }, { 1, 3, 1, 0 }, { 0, 0, 0, 1 } };
		final QuadraticMatrix M2 = intToBigInteger(M2_entries);
		assertEquals(3, M2.computeRank());

		// Non trivial matrix with not full rank.
		final int[][] M3_entries = { { 1, 2, -1 }, { 0, 1, 2 }, { 1, 3, 1 } };
		final QuadraticMatrix M3 = intToBigInteger(M3_entries);
		assertEquals(2, M3.computeRank());
	}

	/**
	 * Tests the function {@link QuadraticMatrix#computeGeometricMultiplicity(int)}.
	 */
	@Test
	public void testGeometricMultiplicity() {
		// identity matrix, eigenvalue 1.
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(4);
		assertEquals(4, E.computeGeometricMultiplicity(1));

		// Zero matrix, eigenvalue 0.
		final QuadraticMatrix Zero = QuadraticMatrix.constructZeroMatrix(3);
		assertEquals(3, Zero.computeGeometricMultiplicity(0));

		// nontrivial matrix.
		final int[][] M_entries = { { -1, 0, 3 }, { -1, 0, 2 }, { 0, 0, 1 } };
		final QuadraticMatrix M = intToBigInteger(M_entries);
		assertEquals(1, M.computeGeometricMultiplicity(-1));
		assertEquals(1, M.computeGeometricMultiplicity(0));
		assertEquals(1, M.computeGeometricMultiplicity(1));
	}

	/**
	 * Tests the function {@link QuadraticMatrix#computeNumberOfBlocks(int, int)}.
	 */
	@Test
	public void testNumberOfBlocks() {
		// Identity matrix
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(4);
		assertEquals(4, E.computeNumberOfBlocks(1, 1));
		assertEquals(0, E.computeNumberOfBlocks(1, 2));
		assertEquals(0, E.computeNumberOfBlocks(-1, 1));
		assertEquals(0, E.computeNumberOfBlocks(-1, 2));

		// Nontrivial matrix.
		final int[][] M_entries = { { -1, 0, 3 }, { -1, 0, 2 }, { 0, 0, 1 } };
		final QuadraticMatrix M = intToBigInteger(M_entries);
		assertEquals(1, M.computeNumberOfBlocks(-1, 1));
		assertEquals(1, M.computeNumberOfBlocks(0, 1));
		assertEquals(1, M.computeNumberOfBlocks(1, 1));
		assertEquals(0, M.computeNumberOfBlocks(1, 2));
	}

	/**
	 * Tests the function {@link QuadraticMatrix#createJordanBlock(int, int)}.
	 */
	@Test
	public void testCreateJordanBlock() {
		final int[][] Res1_entries = { { 1 } };
		final QuadraticMatrix Res1 = intToBigInteger(Res1_entries);
		final QuadraticMatrix J1 = QuadraticMatrix.createJordanBlock(1, 1);
		checkMatrixEquality(Res1, J1);

		final int[][] Res2_entries = { { -1, 1, 0, 0 }, { 0, -1, 1, 0 }, { 0, 0, -1, 1 }, { 0, 0, 0, -1 } };
		final QuadraticMatrix Res2 = intToBigInteger(Res2_entries);
		final QuadraticMatrix J2 = QuadraticMatrix.createJordanBlock(-1, 4);
		checkMatrixEquality(Res2, J2);

		final int[][] Res3_entries = { { 0, 1, 0 }, { 0, 0, 1 }, { 0, 0, 0 } };
		final QuadraticMatrix Res3 = intToBigInteger(Res3_entries);
		final QuadraticMatrix J3 = QuadraticMatrix.createJordanBlock(0, 3);
		checkMatrixEquality(Res3, J3);
	}

	/**
	 * Tests the function {@link QuadraticMatrix#addJordanBlock(QuadraticMatrix, int)}.
	 */
	@Test
	public void testAddJordanBlock() {
		final QuadraticMatrix J = QuadraticMatrix.constructZeroMatrix(4);
		final QuadraticMatrix block = QuadraticMatrix.createJordanBlock(1, 2);
		J.addJordanBlock(block, 1);
		final int[][] Res_entries = { { 0, 0, 0, 0 }, { 0, 1, 1, 0 }, { 0, 0, 1, 0 }, { 0, 0, 0, 0 } };
		final QuadraticMatrix Res = intToBigInteger(Res_entries);
		checkMatrixEquality(Res, J);
	}

	/**
	 * Tests the function {@link QuadraticMatrix#computeJordanMatrix()}.
	 */
	@Test
	public void testJordanMatrix() {
		// Identity matrix.
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(5);
		final QuadraticMatrix J_E = E.constructJordanDecomposition().getJnf();
		checkMatrixEquality(E, J_E);

		// Zero matrix.
		final QuadraticMatrix Zero = QuadraticMatrix.constructZeroMatrix(6);
		final QuadraticMatrix J_Zero = Zero.constructJordanDecomposition().getJnf();
		checkMatrixEquality(Zero, J_Zero);

		// Nontrivial matrix 1.
		final int[][] M1_entries = { { -1, 0, 3 }, { -1, 0, 2 }, { 0, 0, 1 } };
		final QuadraticMatrix M1 = intToBigInteger(M1_entries);
		final QuadraticMatrix J1 = M1.constructJordanDecomposition().getJnf();
		final int[][] res1_entries = { { -1, 0, 0 }, { 0, 0, 0 }, { 0, 0, 1 } };
		final QuadraticMatrix Res1 = intToBigInteger(res1_entries);
		checkMatrixEquality(Res1, J1);

		// Nontrivial matrix 2.
		final int[][] M2_entries = { { 1, 0, 1 }, { 0, 1, 0 }, { 0, 1, 1 } };
		final QuadraticMatrix M2 = intToBigInteger(M2_entries);
		final QuadraticMatrix J2 = M2.constructJordanDecomposition().getJnf();
		final int[][] res2_entries = { { 1, 1, 0 }, { 0, 1, 1 }, { 0, 0, 1 } };
		final QuadraticMatrix Res2 = intToBigInteger(res2_entries);
		checkMatrixEquality(Res2, J2);

		// Nontrivial matrix 3.
		final int[][] M3_entries = { { -1, 0, 1, 3 }, { 0, 1, 0, 2 }, { 0, 1, -1, 1 }, { 0, 0, 0, 1 } };
		final QuadraticMatrix M3 = intToBigInteger(M3_entries);
		final QuadraticMatrix J3 = M3.constructJordanDecomposition().getJnf();
		final int[][] res3_entries = { { -1, 1, 0, 0 }, { 0, -1, 0, 0 }, { 0, 0, 1, 1 }, { 0, 0, 0, 1 } };
		final QuadraticMatrix Res3 = intToBigInteger(res3_entries);
		checkMatrixEquality(Res3, J3);
	}

	/**
	 * Tests the function {@link QuadraticMatrix#constructLes(QuadraticMatrix, Rational[])}.
	 */
	@Test
	public void testLes() {
		final int[][] matrixEntries = { { 1, 3, 4, 2 }, { -1, 0, 0, 1 }, { 2, 1, -2, 1 }, { 1, 0, 0, 0 } };
		final QuadraticMatrix matrix = intToBigInteger(matrixEntries);
		final Rational[] p = new Rational[4];
		for (int i = 0; i < 4; i++) {
			p[i] = Rational.valueOf(BigInteger.valueOf(1), BigInteger.valueOf(i + 1));
		}
		final BigInteger expectedDenominator = BigInteger.valueOf(12);
		final int[][] expectedMatrixEntries = { { 12, 36, 48, 24, 12 }, { -12, 0, 0, 12, 6 }, { 24, 12, -24, 12, 4 },
				{ 12, 0, 0, 0, 3 }, { 0, 0, 0, 0, 1 } };
		final QuadraticMatrix expectedMatrix = intToBigInteger(expectedMatrixEntries);
		final RationalMatrix result = QuadraticMatrix.constructLes(matrix, p);
		checkBigIntegerEquality(expectedDenominator, result.getDenominator());
		checkMatrixEquality(expectedMatrix, result.getIntMatrix());
	}

	/**
	 * Tests the function {@link QuadraticMatrix#matrixVectorMultiplication(QuadraticMatrix, Rational[])}.
	 */
	@Test
	public void testMatrixVectorMultiplication() {
		final int[][] matrixEntries = { { 1, 3, 4, 2 }, { -1, 0, 0, 1 }, { 2, 1, -2, 1 }, { 1, 0, 0, 0 } };
		final QuadraticMatrix matrix = intToBigInteger(matrixEntries);
		final Rational[] p = new Rational[4];
		for (int i = 0; i < 4; i++) {
			p[i] = Rational.valueOf(BigInteger.valueOf(1), BigInteger.valueOf(i + 1));
		}
		final Rational[] expectedResult = new Rational[4];
		expectedResult[0] = Rational.valueOf(BigInteger.valueOf(13), BigInteger.valueOf(3));
		expectedResult[1] = Rational.valueOf(BigInteger.valueOf(-3), BigInteger.valueOf(4));
		expectedResult[2] = Rational.valueOf(BigInteger.valueOf(25), BigInteger.valueOf(12));
		expectedResult[3] = Rational.valueOf(BigInteger.valueOf(1), BigInteger.valueOf(1));
		final Rational[] result = QuadraticMatrix.matrixVectorMultiplication(matrix, p);
		for (int i = 0; i < 4; i++) {
			checkBigIntegerEquality(expectedResult[i].numerator(), result[i].numerator());
			checkBigIntegerEquality(expectedResult[i].denominator(), result[i].denominator());
		}
	}

	/**
	 * Tests the function {@link QuadraticMatrix#computeModalMatrix(QuadraticMatrix, QuadraticMatrix)}.
	 */
	@Test
	public void testModalMatrix() {
		// identity matrix.
		final QuadraticMatrix E = QuadraticMatrix.constructIdentityMatrix(5);
		final QuadraticMatrix JE = E.constructJordanDecomposition().getJnf();
		final RationalMatrix PE = QuadraticMatrix.computeModalMatrix(E, JE);
		final RationalMatrix PE_inverse = RationalMatrix.computeInverse(PE);
		checkMatrixEquality(E, JE);
		checkMatrixEquality(E, PE.getIntMatrix());
		checkMatrixEquality(E, PE_inverse.getIntMatrix());
		checkBigIntegerEquality(BigInteger.valueOf(1), PE.getDenominator());
		checkBigIntegerEquality(BigInteger.valueOf(1), PE_inverse.getDenominator());

		// nontrivial matrix.
		final int[][] M1_entries = { { 1, 0, 1 }, { 0, 1, 0 }, { 0, 1, 1 } };
		final QuadraticMatrix M1 = intToBigInteger(M1_entries);
		final QuadraticMatrix J1 = M1.constructJordanDecomposition().getJnf();
		final RationalMatrix P1 = QuadraticMatrix.computeModalMatrix(M1, J1);
		final RationalMatrix P1_inverse = RationalMatrix.computeInverse(P1);
		final QuadraticMatrix Right11 = QuadraticMatrix.multiplication(P1.getIntMatrix(), J1);
		final QuadraticMatrix Right1 = QuadraticMatrix.multiplication(Right11, P1_inverse.getIntMatrix());
		checkBigIntegerEquality(BigInteger.valueOf(1), P1.getDenominator().multiply(P1_inverse.getDenominator()));
		final BigInteger denominator1 = P1.getDenominator().multiply(P1_inverse.getDenominator());
		for (int i = 0; i < M1.getDimension(); i++) {
			for (int j = 0; j < M1.getDimension(); j++) {
				Right1.setEntry(i, j, Right1.getEntry(i, j).divide(denominator1));
			}
		}
		checkMatrixEquality(M1, Right1);

		// nontrivial matrix.
		final int[][] M2_entries = { { 1, 1, 1 }, { 0, 1, 1 }, { 0, 0, 1 } };
		final QuadraticMatrix M2 = intToBigInteger(M2_entries);
		final QuadraticMatrix J2 = M2.constructJordanDecomposition().getJnf();
		final RationalMatrix P2 = QuadraticMatrix.computeModalMatrix(M2, J2);
		final RationalMatrix P2_inverse = RationalMatrix.computeInverse(P2);
		final QuadraticMatrix Right21 = QuadraticMatrix.multiplication(P2.getIntMatrix(), J2);
		final QuadraticMatrix Right2 = QuadraticMatrix.multiplication(Right21, P2_inverse.getIntMatrix());
		final BigInteger denominator2 = P2.getDenominator().multiply(P2_inverse.getDenominator());
		for (int i = 0; i < M2.getDimension(); i++) {
			for (int j = 0; j < M2.getDimension(); j++) {
				Right2.setEntry(i, j, Right2.getEntry(i, j).divide(denominator2));
			}
		}
		checkMatrixEquality(M2, Right2);

		// nontrivial matrix.
		final int[][] M3_entries = { { -1, 0, 3 }, { -1, 0, 2 }, { 0, 0, 1 } };
		final QuadraticMatrix M3 = intToBigInteger(M3_entries);
		final QuadraticMatrix J3 = M3.constructJordanDecomposition().getJnf();
		final RationalMatrix P3 = QuadraticMatrix.computeModalMatrix(M3, J3);
		final RationalMatrix P3_inverse = RationalMatrix.computeInverse(P3);
		final QuadraticMatrix Right31 = QuadraticMatrix.multiplication(P3.getIntMatrix(), J3);
		final QuadraticMatrix Right3 = QuadraticMatrix.multiplication(Right31, P3_inverse.getIntMatrix());
		final BigInteger denominator3 = P3.getDenominator().multiply(P3_inverse.getDenominator());
		for (int i = 0; i < M3.getDimension(); i++) {
			for (int j = 0; j < M3.getDimension(); j++) {
				Right3.setEntry(i, j, Right3.getEntry(i, j).divide(denominator3));
			}
		}
		checkMatrixEquality(M3, Right3);

		// nontrivial matrix.
		final int[][] M4_entries = { { 0, 1, -1, 2 }, { 1, 0, 0, -1 }, { 0, 0, 1, 2 }, { 0, 0, 0, 1 } };
		final QuadraticMatrix M4 = intToBigInteger(M4_entries);
		final QuadraticMatrix J4 = M4.constructJordanDecomposition().getJnf();
		final RationalMatrix P4 = QuadraticMatrix.computeModalMatrix(M4, J4);
		final RationalMatrix P4_inverse = RationalMatrix.computeInverse(P4);
		final QuadraticMatrix Right41 = QuadraticMatrix.multiplication(P4.getIntMatrix(), J4);
		final QuadraticMatrix Right4 = QuadraticMatrix.multiplication(Right41, P4_inverse.getIntMatrix());
		final BigInteger denominator4 = P4.getDenominator().multiply(P4_inverse.getDenominator());
		for (int i = 0; i < M4.getDimension(); i++) {
			for (int j = 0; j < M4.getDimension(); j++) {
				Right4.setEntry(i, j, Right4.getEntry(i, j).divide(denominator4));
			}
		}
		checkMatrixEquality(M4, Right4);

		// nontrivial matrix.
		final int[][] M5_entries = { { 1, 1, -1, 3 }, { 0, 1, 0, 0 }, { 0, 1, -1, 3 }, { 0, 0, 0, 1 } };
		final QuadraticMatrix M5 = intToBigInteger(M5_entries);
		final QuadraticMatrix J5 = M5.constructJordanDecomposition().getJnf();
		final RationalMatrix P5 = QuadraticMatrix.computeModalMatrix(M5, J5);
		final RationalMatrix P5_inverse = RationalMatrix.computeInverse(P5);
		final QuadraticMatrix Right51 = QuadraticMatrix.multiplication(P5.getIntMatrix(), J5);
		final QuadraticMatrix Right5 = QuadraticMatrix.multiplication(Right51, P5_inverse.getIntMatrix());
		final BigInteger denominator5 = P5.getDenominator().multiply(P5_inverse.getDenominator());
		for (int i = 0; i < M5.getDimension(); i++) {
			for (int j = 0; j < M5.getDimension(); j++) {
				Right5.setEntry(i, j, Right5.getEntry(i, j).divide(denominator5));
			}
		}
		checkMatrixEquality(M5, Right5);

		// abfuck matrix
		final int[][] matrix6Entries = { { -1, 0, -1, 1, 1, 3, 0 }, { 0, 1, 0, 0, 0, 0, 0 }, { 2, 1, 2, -1, -1, -6, 0 },
				{ -2, 0, -1, 2, 1, 3, 0 }, { 0, 0, 0, 0, 1, 0, 0 }, { 0, 0, 0, 0, 0, 1, 0 },
				{ -1, -1, 0, 1, 2, 4, 1 } };
		final QuadraticMatrix matrix6 = intToBigInteger(matrix6Entries);
		final QuadraticMatrix jordan6 = matrix6.constructJordanDecomposition().getJnf();
		final RationalMatrix modal6 = QuadraticMatrix.computeModalMatrix(matrix6, jordan6);
		final RationalMatrix modal6Inverse = RationalMatrix.computeInverse(modal6);
		final QuadraticMatrix Right61 = QuadraticMatrix.multiplication(modal6.getIntMatrix(), jordan6);
		final QuadraticMatrix Right6 = QuadraticMatrix.multiplication(Right61, modal6Inverse.getIntMatrix());
		final BigInteger denominator6 = modal6.getDenominator().multiply(modal6Inverse.getDenominator());
		for (int i = 0; i < matrix6.getDimension(); i++) {
			for (int j = 0; j < matrix6.getDimension(); j++) {
				Right6.setEntry(i, j, Right6.getEntry(i, j).divide(denominator6));
			}
		}
		checkMatrixEquality(matrix6, Right6);
		final QuadraticMatrix matrixModal6 = QuadraticMatrix.multiplication(matrix6, modal6.getIntMatrix());
		final QuadraticMatrix modalJordan6 = QuadraticMatrix.multiplication(modal6.getIntMatrix(), jordan6);
		checkMatrixEquality(matrixModal6, modalJordan6);
	}
}
