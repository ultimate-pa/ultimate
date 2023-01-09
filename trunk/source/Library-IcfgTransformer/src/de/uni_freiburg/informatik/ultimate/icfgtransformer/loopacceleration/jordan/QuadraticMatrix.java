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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanDecomposition.JordanDecompositionStatus;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Class for quadratic integer matrices. Goal: compute Jordan normal form for matrices with eigenvalues only -1,0,1.
 *
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuadraticMatrix {
	/**
	 * mDimension is an integer representing the number of rows/columns of the matrix.
	 */
	private final int mDimension;
	/**
	 * mEntries is an integer array of arrays representing the entries of the matrix.
	 */
	private final BigInteger[][] mEntries;

	public QuadraticMatrix(final BigInteger[][] matrixEntries) {
		// Check if given array of arrays is quadratic.
		final int numberOfRows = matrixEntries.length;
		for (int i = 0; i < numberOfRows; i++) {
			if (numberOfRows != matrixEntries[i].length) {
				throw new AssertionError("Some matrix is not quadratic");
			}
		}
		// Set member variables.
		mEntries = matrixEntries;
		mDimension = numberOfRows;
	}

	/**
	 * @param n
	 *            dimension
	 * @return identity matrix of dimension n
	 */
	public static QuadraticMatrix constructIdentityMatrix(final int n) {
		final BigInteger[][] identityEntries = new BigInteger[n][n];
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				if (i == j) {
					identityEntries[i][j] = BigInteger.valueOf(1);
				} else {
					identityEntries[i][j] = BigInteger.valueOf(0);
				}
			}
		}
		final QuadraticMatrix identity = new QuadraticMatrix(identityEntries);
		return identity;
	}

	/**
	 * @param n
	 *            dimension
	 * @return zero matrix of dimension n
	 */
	public static QuadraticMatrix constructZeroMatrix(final int n) {
		final BigInteger[][] zeroEntries = new BigInteger[n][n];
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				zeroEntries[i][j] = BigInteger.valueOf(0);
			}
		}
		final QuadraticMatrix zero = new QuadraticMatrix(zeroEntries);
		return zero;
	}

	/**
	 * Copies the matrix M. Used to make sure to not change the matrix when applying functions.
	 *
	 * @param matrix
	 * @return copy of matrix
	 */
	public static QuadraticMatrix copyMatrix(final QuadraticMatrix matrix) {
		final int n = matrix.mDimension;
		final BigInteger[][] copiedEntries = new BigInteger[n][n];
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				copiedEntries[i][j] = matrix.mEntries[i][j];
			}
		}
		final QuadraticMatrix matrixCopied = new QuadraticMatrix(copiedEntries);
		return matrixCopied;
	}

	/**
	 * Usual matrix addition for quadratic matrices if the matrices are of the same dimension.
	 *
	 * @param matrix1
	 *            quadratic matrix
	 * @param matrix2
	 *            quadratic matrix
	 * @return new quadratic matrix sumMatrix = matrix1 + matrix 2
	 */
	public static QuadraticMatrix addition(final QuadraticMatrix matrix1, final QuadraticMatrix matrix2) {
		// Check if both matrices are of the same dimension.
		if (matrix1.mDimension != matrix2.mDimension) {
			throw new AssertionError("Some matrices for addition are not of the same dimension.");
		}
		final int n = matrix1.mDimension;
		final BigInteger[][] sumEntries = new BigInteger[n][n];
		final QuadraticMatrix matrixSum = new QuadraticMatrix(sumEntries);

		// Compute usual matrix addition.
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				matrixSum.mEntries[i][j] = matrix1.mEntries[i][j].add(matrix2.mEntries[i][j]);
			}
		}
		return matrixSum;
	}

	/**
	 * Usual multiplication of scalar with matrix.
	 *
	 * @param a
	 * @param matrix
	 * @return new quadratic matrix scMult = a*matrix
	 */
	public static QuadraticMatrix scalarMultiplication(final BigInteger a, final QuadraticMatrix matrix) {
		final int n = matrix.mDimension;
		final BigInteger[][] scMultEntries = new BigInteger[n][n];
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				scMultEntries[i][j] = a.multiply(matrix.mEntries[i][j]);
			}
		}
		final QuadraticMatrix scMult = new QuadraticMatrix(scMultEntries);
		return scMult;
	}

	/**
	 * Usual matrix multiplication for quadratic matrices if the matrices are of the same dimension.
	 *
	 * @param matrix1
	 *            quadratic matrix
	 * @param matrix2
	 *            quadratic matrix
	 * @return new quadratic matrix productMatrix = matrix1 * matrix 2
	 */
	public static QuadraticMatrix multiplication(final QuadraticMatrix matrix1, final QuadraticMatrix matrix2) {
		// Check if both matrices have the same dimension.
		if (matrix1.mDimension != matrix2.mDimension) {
			throw new AssertionError("Some matrices for multiplication are not of the same dimension");
		}
		// Compute usual matrix multiplication.
		final int n = matrix1.mDimension;
		final QuadraticMatrix productMatrix = constructZeroMatrix(n);
		for (int i = 0; i < n; i++) {
			for (int k = 0; k < n; k++) {
				for (int j = 0; j < n; j++) {
					productMatrix.mEntries[i][k] =
							(productMatrix.mEntries[i][k]).add(matrix1.mEntries[i][j].multiply(matrix2.mEntries[j][k]));
				}
			}
		}
		return productMatrix;
	}

	/**
	 * @param matrix
	 *            quadratic matrix
	 * @param s
	 * @return new quadratic matrix powerMatrix = matrix^s
	 */
	public static QuadraticMatrix power(final QuadraticMatrix matrix, final int s) {
		final int n = matrix.mDimension;
		if (s == 0) {
			return constructIdentityMatrix(n);
		}
		if (s == 1) {
			return matrix;
		}
		QuadraticMatrix powerMatrix = copyMatrix(matrix);
		for (int i = 2; i <= s; i++) {
			powerMatrix = multiplication(powerMatrix, matrix);
		}
		return powerMatrix;
	}

	/**
	 * Recursice computation of the determinant of a quadratic matrix M using Laplace expansion.
	 */
	public BigInteger computeDet() {
		final int n = mDimension;
		// Base cases.
		// 1x1 matrices.
		if (n == 1) {
			return mEntries[0][0];
		}
		// 2x2 matrices.
		if (n == 1) {
			return (mEntries[0][0].multiply(mEntries[1][1])).subtract(mEntries[0][1].multiply(mEntries[1][0]));
		}
		// 3x3 matrices.
		if (n == 3) {
			return (mEntries[0][0].multiply(mEntries[1][1]).multiply(mEntries[2][2]))
					.add(mEntries[0][1].multiply(mEntries[1][2]).multiply(mEntries[2][0]))
					.add(mEntries[0][2].multiply(mEntries[1][0]).multiply(mEntries[2][1]))
					.subtract(mEntries[2][0].multiply(mEntries[1][1]).multiply(mEntries[0][2]))
					.subtract(mEntries[2][1].multiply(mEntries[1][2]).multiply(mEntries[0][0]))
					.subtract(mEntries[2][2].multiply(mEntries[1][0]).multiply(mEntries[0][1]));
		}
		// Recursive case: nxn matrices for n>3.
		BigInteger det = BigInteger.valueOf(0);
		// Delete last row and one column after the other.
		for (int k = 0; k < n; k++) {
			final BigInteger[][] kTmp = new BigInteger[n - 1][n - 1];
			for (int i = 0; i < n - 1; i++) {
				for (int j = 0; j < k; j++) {
					kTmp[i][j] = mEntries[i][j];
				}
				for (int j = k + 1; j < n; j++) {
					kTmp[i][j - 1] = mEntries[i][j];
				}
			}
			final QuadraticMatrix kMatrix = new QuadraticMatrix(kTmp);
			if ((n + k - 1) % 2 == 0) {
				det = det.add(mEntries[n - 1][k].multiply(kMatrix.computeDet()));
			} else {
				det = det.subtract(mEntries[n - 1][k].multiply(kMatrix.computeDet()));
			}
		}
		return det;
	}

	/**
	 * Computes the inverse of a quadratic matrix where inverse is a RationalMatrix consisting of a quadratic integer
	 * matrix and a main denominator for all entries.
	 *
	 * @param matrix
	 * @return inverse of matrix
	 */
	public static RationalMatrix computeInverse(final QuadraticMatrix matrix) {
		// Check if matrix is invertible. If not, stop.
		final int n = matrix.mDimension;
		if ((matrix.computeDet()).equals(BigInteger.valueOf(0))) {
			throw new AssertionError("Matrix is not invertible");
		}
		// For every column of the matrix M
		// construct LES for inverse matrix: M*M^-1 = E.
		final QuadraticMatrix inverseInt = constructZeroMatrix(n);
		final RationalMatrix inverse = new RationalMatrix(BigInteger.valueOf(1), inverseInt);
		for (int k = 0; k < n; k++) {
			final BigInteger[][] lesEntries = new BigInteger[n + 1][n + 1];
			for (int i = 0; i < n; i++) {
				for (int j = 0; j < n; j++) {
					lesEntries[i][j] = matrix.mEntries[i][j];
				}
			}
			for (int i = 0; i < n; i++) {
				if (i == k) {
					lesEntries[i][n] = BigInteger.valueOf(1);
				} else {
					lesEntries[i][n] = BigInteger.valueOf(0);
				}
			}
			for (int j = 0; j < n; j++) {
				lesEntries[n][j] = BigInteger.valueOf(0);
			}
			lesEntries[n][n] = BigInteger.valueOf(1);
			final QuadraticMatrix lesMatrix = new QuadraticMatrix(lesEntries);
			// Solve LES using gaussian elimination and backwards substitution
			// For every column of the inverse matrix.
			final QuadraticMatrix lesMatrixGauss = gaussElimination(lesMatrix);
			final Rational[] xk = backwardSubstitution(lesMatrixGauss, 1);
			inverse.addColumnToMatrix(k, xk);
		}
		return inverse;
	}

	/**
	 * Checks if -1,0,1 are eigenvalues of the quadratic matrix.
	 *
	 * @return boolean array of size 3 where the i-th entry is true iff i-1 is an eigenvalue of the matrix.
	 */
	public boolean[] computeSmallEigenvalues() {
		final boolean[] eigenvalues = new boolean[3];
		for (int i = 0; i < 3; i++) {
			eigenvalues[i] = false;
		}
		// Check if i is an eigenvalue for i = -1,0,1
		// By checking if i is a zero of the characteristic polynomial.
		final int n = mDimension;
		final QuadraticMatrix identity = constructIdentityMatrix(n);
		for (int i = -1; i < 2; i++) {
			if ((addition(this, scalarMultiplication(BigInteger.valueOf(-i), identity))).computeDet()
					.equals(BigInteger.valueOf(0))) {
				eigenvalues[i + 1] = true;
			}
		}
		return eigenvalues;
	}

	/**
	 * Swaps the rows i and j of the quadratic matrix. Warning: Changes the matrix!
	 *
	 * @param i
	 *            row index
	 * @param j
	 *            row index
	 */
	public void swapRows(final int i, final int j) {
		final int n = mDimension;
		final BigInteger[] iRow = new BigInteger[n];
		for (int k = 0; k < n; k++) {
			iRow[k] = mEntries[i][k];
			mEntries[i][k] = mEntries[j][k];
			mEntries[j][k] = iRow[k];
		}
	}

	/**
	 * Applies Gaussian elimination to a quadratic matrix. Uses multiplication instead of division to keep values
	 * integral.
	 *
	 * @param matrix
	 * @return quadratic matrix in row echelon form as upper triangle matrix.
	 */
	public static QuadraticMatrix gaussElimination(final QuadraticMatrix matrix) {
		final int n = matrix.mDimension;
		// Copy of M that will be edited.
		final QuadraticMatrix nMatrix = copyMatrix(matrix);
		// Gaussian Elimination with multiplication instead of division.
		int h = 0;
		int k = 0;
		while (h < n && k < n) {
			int i_max = h;
			for (int i = h; i < n; i++) {
				if (((nMatrix.mEntries[i][k]).abs()).compareTo((nMatrix.mEntries[i_max][k]).abs()) > 0) {
					i_max = i;
				}
			}
			if ((nMatrix.mEntries[i_max][k]).equals(BigInteger.valueOf(0))) {
				k = k + 1;
			} else {
				nMatrix.swapRows(h, i_max);
				for (int i = h + 1; i < n; i++) {
					BigInteger f1 = BigInteger.valueOf(0);
					BigInteger f2 = BigInteger.valueOf(0);
					BigInteger gcd = BigInteger.valueOf(0);
					f1 = nMatrix.mEntries[i][k];
					f2 = nMatrix.mEntries[h][k];
					gcd = Rational.gcd(f1, f2);
					f1 = f1.divide(gcd);
					f2 = f2.divide(gcd);
					nMatrix.mEntries[i][k] = BigInteger.valueOf(0);
					for (int j = k + 1; j < n; j++) {
						nMatrix.mEntries[i][j] =
								(f2.multiply(nMatrix.mEntries[i][j])).subtract(f1.multiply(nMatrix.mEntries[h][j]));
					}
				}
				h = h + 1;
				k = k + 1;
			}
		}
		// Bring in correct row echelon form.
		for (int l = 1; l < n; l++) {
			final BigInteger[][] entriesL = new BigInteger[n - l][n - l];
			for (int i = 0; i < n - l; i++) {
				for (int j = 0; j < n - l; j++) {
					entriesL[i][j] = nMatrix.mEntries[i + l][j + l];
				}
			}
			final QuadraticMatrix nL = new QuadraticMatrix(entriesL);
			final QuadraticMatrix nLGauss = gaussElimination(nL);
			for (int i = 0; i < n - l; i++) {
				for (int j = 0; j < n - l; j++) {
					nMatrix.mEntries[i + l][j + l] = nLGauss.mEntries[i][j];
				}
			}
		}
		return nMatrix;
	}

	/**
	 * Computes a solution of the LES as a Rational array. When having choices, take s-th choice 1, other choices 0.
	 * Warning: Only works if M is in row echelon form, an upper triangle matrix and has a row 0,...,0,1.
	 *
	 * @param matrix
	 *            that represents an LES Ax = b
	 * @param s
	 * @return solution of the LES as an array of Rationals.
	 */
	public static Rational[] backwardSubstitution(final QuadraticMatrix matrix, final int s) {
		final QuadraticMatrix N = copyMatrix(matrix);
		final int n = N.mDimension;
		if (!((N.mEntries[N.computeRank() - 1][n - 1]).equals(BigInteger.valueOf(1)))) {
			throw new AssertionError("LES unsolvable.");
		}
		final Rational[] p = new Rational[n - 1];
		int expected = n - 2;
		for (int i = 0; i < n - 1; i++) {
			p[i] = Rational.valueOf(BigInteger.valueOf(0), BigInteger.valueOf(1));
		}
		int s0 = 0;
		for (int i = N.computeRank() - 2; i >= 0; i--) {
			// Determine first column j with N.entries[i][j] != 0.
			int j = i;
			for (int l = i; l < n; l++) {
				if (!(N.mEntries[i][l]).equals(BigInteger.valueOf(0))) {
					j = l;
					break;
				}
			}
			while (j < expected) {
				s0 = s0 + 1;
				if (s0 == s) {
					p[expected] = Rational.valueOf(BigInteger.valueOf(1), BigInteger.valueOf(1));
				}
				expected = expected - 1;
			}
			expected = j - 1;
			p[j] = Rational.valueOf(N.mEntries[i][n - 1], BigInteger.valueOf(1));
			for (int k = j + 1; k < n - 1; k++) {
				final Rational tmp =
						Rational.valueOf((N.mEntries[i][k].negate()).multiply(p[k].numerator()), p[k].denominator());
				p[j] = p[j].add(tmp);
				p[j] = Rational.valueOf(p[j].numerator(), p[j].denominator());
			}
			p[j] = Rational.valueOf(p[j].numerator(), (p[j].denominator()).multiply(N.mEntries[i][j]));
		}
		while (expected > -1) {
			s0 = s0 + 1;
			if (s0 == s) {
				p[expected] = Rational.valueOf(BigInteger.valueOf(1), BigInteger.valueOf(1));
			}
			expected = expected - 1;
		}
		return p;
	}

	/**
	 * Computes the rank of a quadratic matrix computing the row echelon form first using Gaussian elimination and then
	 * counting the number of zero rows.
	 */
	public int computeRank() {
		final QuadraticMatrix matrixCopy = copyMatrix(this);
		final QuadraticMatrix matrixGauss = gaussElimination(matrixCopy);
		final int n = matrixGauss.mDimension;
		int zeroRows = 0;
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				if (!((matrixGauss.mEntries[i][j]).equals(BigInteger.valueOf(0)))) {
					break;
				}
				if (j == n - 1 && (matrixGauss.mEntries[i][j]).equals(BigInteger.valueOf(0))) {
					zeroRows = zeroRows + 1;
				}
			}
		}
		return n - zeroRows;
	}

	/**
	 * Computes the geometric multiplicity of an eigenvalue lambda with regard to a quadratic matrix M, the dimension of
	 * ker(matrix-lambda*E) where E is the identity matrix. To compute the dimension of the kernel the dimension formula
	 * is used. The geometric multiplicity corresponds to the number of Jordan blocks for lambda. This method also works
	 * for integral eigenvalues not equal to -1,0 or 1.
	 *
	 * @param lambda
	 *            an eigenvalue
	 * @return geometric multiplicity of lambda
	 */
	public int computeGeometricMultiplicity(final int lambda) {
		final int n = mDimension;
		final QuadraticMatrix identity = constructIdentityMatrix(n);
		final QuadraticMatrix eigenvalueMatrix =
				addition(this, scalarMultiplication(BigInteger.valueOf(-lambda), identity));
		return n - eigenvalueMatrix.computeRank();
	}

	/**
	 * Computes the number of Jordan blocks for eigenvalue lambda of size s with regard to a quadratic matrix. This
	 * method also works for integral eigenvalues not equal to -1,0 or 1.
	 *
	 * @param lambda
	 *            eigenvalue
	 * @param s
	 */
	public int computeNumberOfBlocks(final int lambda, final int s) {
		final int n = mDimension;
		final QuadraticMatrix identity = constructIdentityMatrix(n);
		final QuadraticMatrix eigenvalueMatrix =
				addition(this, scalarMultiplication(BigInteger.valueOf(-lambda), identity));
		return (2 * (power(eigenvalueMatrix, s)).computeGeometricMultiplicity(0))
				- ((power(eigenvalueMatrix, s + 1)).computeGeometricMultiplicity(0))
				- ((power(eigenvalueMatrix, s - 1)).computeGeometricMultiplicity(0));
	}

	/**
	 * Creates a Jordan block of size s with eigenvalue lambda. This method also works for integral eigenvalues not
	 * equal to -1,0 or 1.
	 *
	 * @param lambda
	 *            eigenvalue
	 * @param s
	 *            size of block
	 */
	public static QuadraticMatrix createJordanBlock(final int lambda, final int s) {
		final QuadraticMatrix block = constructZeroMatrix(s);
		for (int i = 0; i < s; i++) {
			block.mEntries[i][i] = BigInteger.valueOf(lambda);
			if (i != s - 1) {
				block.mEntries[i][i + 1] = BigInteger.valueOf(1);
			}
		}
		return block;
	}

	/**
	 * Adds jordan block to quadratic jordan matrix beginning at row start. This method also works for integral
	 * eigenvalues not equal to -1,0 or 1.
	 */
	public void addJordanBlock(final QuadraticMatrix block, final int start) {
		if (mDimension < block.mDimension + start) {
			throw new AssertionError("Block does not fit into Jordan matrix");
		}
		final int s = block.mDimension;
		for (int i = 0; i < s; i++) {
			for (int j = 0; j < s; j++) {
				mEntries[i + start][j + start] = block.mEntries[i][j];
			}
		}
	}

	/**
	 * Computes triples (ev, bs, occ) meaning that there are occ blocks of size bs for eigenvalue ev.
	 */
	private NestedMap2<Integer, Integer, Integer> computeJordanBlockSizes() {
		final NestedMap2<Integer, Integer, Integer> jordanBlockSizes = new NestedMap2<Integer, Integer, Integer>();
		final boolean[] eigenvalues = computeSmallEigenvalues();
		final int n = mDimension;
		for (int e = -1; e <= 1; e++) {
			if (eigenvalues[e + 1]) {
				final int geomMult = computeGeometricMultiplicity(e);
				final int[] numberOfBlocks = new int[n + 1];
				int sum = 0;
				while (sum < geomMult) {
					for (int sE = 1; sE <= n; sE++) {
						numberOfBlocks[sE] = computeNumberOfBlocks(e, sE);
						sum = sum + numberOfBlocks[sE];
					}
				}
				for (int s = 1; s <= n; s++) {
					if (numberOfBlocks[s] != 0) {
						jordanBlockSizes.put(e, s, numberOfBlocks[s]);
					}
				}
			}
		}
		return jordanBlockSizes;
	}

	/**
	 * Computes the jordan matrix of a given quadratic matrix given jordanBlockSizes which contains triples (eigenvalue,
	 * blocksize, occurrence). This method also works for integral eigenvalues not equal to -1,0 or 1, only need to
	 * change eigenvalues array.
	 * @param linearUpdate
	 */
	public JordanDecomposition constructJordanDecomposition() {
		final int n = mDimension;
		if (n >= 11) {
			throw new UnsupportedOperationException(
					"Vector space has " + n + " dimensions. Computation of eigenvalues may not terminate.");
		}
		final QuadraticMatrix jordanMatrix = constructZeroMatrix(n);
		final NestedMap2<Integer, Integer, Integer> jordanBlockSizes = computeJordanBlockSizes();
		JordanDecompositionStatus status;
		int current = 0;
		for (int e = -1; e <= 1; e++) {
			if (jordanBlockSizes.get(e) != null) {
				for (final Integer blockSize : jordanBlockSizes.get(e).keySet()) {
					if (blockSize != null) {
						for (int occ = 1; occ <= jordanBlockSizes.get(e, blockSize); occ++) {
							final QuadraticMatrix block = createJordanBlock(e, blockSize);
							jordanMatrix.addJordanBlock(block, current);
							current = current + blockSize;
						}
					}
				}
			}
		}
		final JordanDecomposition decomp;
		if (current != n) {
			status = JordanDecompositionStatus.UNSUPPORTED_EIGENVALUES;
			decomp = new JordanDecomposition(status, null, null, null, null);
		} else {
			status = JordanDecompositionStatus.SUCCESS;
			final RationalMatrix modal = computeModalMatrix(this, jordanMatrix);
			final RationalMatrix inverseModal = RationalMatrix.computeInverse(modal);
			assert checkCorrectnessofJordanDecomposition(this, modal, jordanMatrix, inverseModal);
			decomp = new JordanDecomposition(status, jordanMatrix, modal, inverseModal, jordanBlockSizes);
		}
		return decomp;
	}

	/**
	 * Constructs the matrix representing the les matrix*x=b.
	 */
	public static RationalMatrix constructLes(final QuadraticMatrix matrix, final Rational[] b) {
		final int n = matrix.mDimension;
		final QuadraticMatrix intLes = QuadraticMatrix.constructZeroMatrix(n + 1);
		final RationalMatrix les = new RationalMatrix(BigInteger.valueOf(1), intLes);
		for (int j = 0; j < n; j++) {
			final Rational p[] = new Rational[n + 1];
			for (int i = 0; i < n; i++) {
				p[i] = Rational.valueOf(matrix.mEntries[i][j], BigInteger.valueOf(1));
			}
			p[n] = Rational.valueOf(BigInteger.valueOf(0), BigInteger.valueOf(1));
			les.addColumnToMatrix(j, p);
		}
		les.addColumnToMatrix(n, b);
		les.getIntMatrix().mEntries[n][n] = BigInteger.valueOf(1);
		return les;
	}

	/**
	 * Usual matrix vector multiplication where matrix entries are BigInteger, vector is Rational.
	 */
	public static Rational[] matrixVectorMultiplication(final QuadraticMatrix matrix, final Rational[] vector) {
		if (matrix.mDimension != vector.length) {
			throw new AssertionError("Matrix dimension is not vector length.");
		}
		final int n = matrix.mDimension;
		final Rational[] result = new Rational[n];
		for (int i = 0; i < n; i++) {
			result[i] = Rational.valueOf(BigInteger.valueOf(0), BigInteger.valueOf(1));
			for (int j = 0; j < n; j++) {
				result[i] = result[i].add(Rational.valueOf(((matrix.mEntries[i][j]).multiply(vector[j].numerator())),
						vector[j].denominator()));
			}
		}
		return result;
	}

	/**
	 * Computes the modal matrix for a given matrix and its jordan matrix. For each block it computes a generalized
	 * eigenvector first and then its jordan chain. The generalized eigenvectors are computed using linear equation
	 * systems ((matrix - lambda*identity)^s)*p = 0 and checking that ((matrix - lambda*identity)^s-1)*p != 0. Linear
	 * independence of two generalized eigenvectors for the same block size is guaranteed by adding the other
	 * generalized eigenvectors to the linear equation system (scalar product 0 implies linear independence). This
	 * method also works for integral eigenvalues not equal to -1,0 or 1.
	 *
	 * @param matrix
	 * @param jordanMatrix
	 * @return modal matrix
	 */
	public static RationalMatrix computeModalMatrix(final QuadraticMatrix matrix, final QuadraticMatrix jordanMatrix) {
		final int n = matrix.mDimension;
		final QuadraticMatrix modalIntMatrix = constructZeroMatrix(n);
		final RationalMatrix modalMatrix = new RationalMatrix(BigInteger.valueOf(1), modalIntMatrix);
		// Hashmap that assigns order to list of columns corresponding to that order.
		final HashMap<Integer, ArrayList<Integer>> columnOrder = new HashMap<Integer, ArrayList<Integer>>();
		// current column in modal matrix.
		int current = n;
		final Rational[] zeroVector = new Rational[n];
		for (int i = 0; i < n; i++) {
			zeroVector[i] = Rational.valueOf(BigInteger.valueOf(0), BigInteger.valueOf(1));
		}
		for (int lambda = 1; lambda >= -1; lambda--) {
			if (matrix.computeSmallEigenvalues()[lambda + 1]) {
				final QuadraticMatrix eigenvalueMatrix =
						addition(matrix, scalarMultiplication(BigInteger.valueOf(-lambda), constructIdentityMatrix(n)));
				int blockSize = n;
				while (matrix.computeNumberOfBlocks(lambda, blockSize) == 0) {
					blockSize = blockSize - 1;
				}
				// s is the size of the greatest jordan block for lambda.
				// initialize columnOrder hashmap.
				for (int order = 1; order <= blockSize; order++) {
					final ArrayList<Integer> orderList = new ArrayList<Integer>();
					columnOrder.put(order, orderList);
				}
				while (blockSize > 0) {
					final int numberOfBlocks = matrix.computeNumberOfBlocks(lambda, blockSize);
					if (numberOfBlocks == 0) {
						blockSize = blockSize - 1;
						continue;
					}
					final RationalMatrix lesMatrix = constructLes(power(eigenvalueMatrix, blockSize), zeroVector);
					final ArrayList<Integer> constrainingColumns = columnOrder.get(blockSize);
					final int numberOfConstraints = constrainingColumns.size();
					final ArrayList<Integer> freeChoice = new ArrayList<Integer>();
					for (int c = 1; c <= n; c++) {
						freeChoice.add(c);
					}
					for (int k = 0; k < numberOfBlocks; k++) {
						final Rational[][] constraints = new Rational[numberOfConstraints + numberOfBlocks - 1][n];
						for (int i = 0; i < numberOfConstraints; i++) {
							for (int j = 0; j < n; j++) {
								constraints[i][j] = Rational.valueOf(
										modalMatrix.getIntMatrix().mEntries[j][constrainingColumns.get(i)],
										modalMatrix.getDenominator());
							}
						}
						for (int i = numberOfConstraints; i < numberOfConstraints + numberOfBlocks - 1; i++) {
							for (int j = 0; j < n; j++) {
								constraints[i][j] = Rational.valueOf(BigInteger.valueOf(0), BigInteger.valueOf(1));
							}
						}
						// Compute Solution.
						int choice = 0;
						boolean isGeneralizedEigenvector = false;
						final QuadraticMatrix checkMatrix = power(eigenvalueMatrix, blockSize - 1);
						Rational[] solution = RationalMatrix.solveLes(lesMatrix, constraints, freeChoice.get(choice));
						while (!isGeneralizedEigenvector) {
							int i = 0;
							while (i < solution.length) {
								final Rational[] next = matrixVectorMultiplication(checkMatrix, solution);
								if (!(next[i].equals(Rational.ZERO))) {
									// Entry not equal to 0 found
									isGeneralizedEigenvector = true;
									freeChoice.remove(choice);
									break;
								}
								i = i + 1;
							}
							if (i == solution.length && !isGeneralizedEigenvector) {
								choice = choice + 1;
								solution = RationalMatrix.solveLes(lesMatrix, constraints, freeChoice.get(choice));
							}
						}
						// Add solution to matrix.
						modalMatrix.addColumnToMatrix(current - k * blockSize - 1, solution);
						// Solution is new constraint for LES.
						(columnOrder.get(blockSize)).add(current - k * blockSize - 1);
						for (int l = blockSize - 1; l > 0; l--) {
							// Compute and add vectors of same block to matrix.
							solution = matrixVectorMultiplication(eigenvalueMatrix, solution);
							modalMatrix.addColumnToMatrix(current - k * blockSize - blockSize + l - 1, solution);
							(columnOrder.get(l)).add(current - k * blockSize - blockSize + l - 1);
						}
					}
					current = current - numberOfBlocks * blockSize;
					blockSize = blockSize - 1;
				}
			}
		}
		return modalMatrix;
	}

	/**
	 * Check if Jordan decomposition was computed correctly, check matrix = modalMatrix * jordanMatrix *
	 * inverseModalMatrix.
	 */
	public static boolean checkCorrectnessofJordanDecomposition(final QuadraticMatrix matrix,
			final RationalMatrix modalMatrix, final QuadraticMatrix jordanMatrix,
			final RationalMatrix inverseModalMatrix) {
		final QuadraticMatrix decomposition =
				QuadraticMatrix.multiplication(QuadraticMatrix.multiplication(modalMatrix.getIntMatrix(), jordanMatrix),
						inverseModalMatrix.getIntMatrix());
		if (matrix.getDimension() != decomposition.getDimension()) {
			throw new AssertionError("Mistake in Jordan decomposition!");
		}
		final BigInteger denominator = modalMatrix.getDenominator().multiply(inverseModalMatrix.getDenominator());
		for (int i = 0; i < matrix.getDimension(); i++) {
			for (int j = 0; j < matrix.getDimension(); j++) {
				if (matrix.getEntry(i, j).intValue() != decomposition.getEntry(i, j).divide(denominator).intValue()) {
					throw new AssertionError("Mistake in Jordan decomposition.");
				}
			}
		}
		return true;
	}

	public int getDimension() {
		return mDimension;
	}

	public BigInteger getEntry(final int i, final int j) {
		return mEntries[i][j];
	}

	public void setEntry(final int i, final int j, final BigInteger value) {
		mEntries[i][j] = value;
	}

	@Override
	public String toString() {
		return Arrays.deepToString(mEntries);
	}
}
