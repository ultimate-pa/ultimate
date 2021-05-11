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

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Class for rational integer matrices consisting of a QuadraticMatrix and a main denominator for all entries.
 *
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class RationalMatrix {
	/**
	 * mIntMatrix is a quadratic matrix with only BigInteger entries.
	 */
	private final QuadraticMatrix mIntMatrix;
	/**
	 * mDenominator represents the common denominator of all matrix entries.
	 */
	private BigInteger mDenominator;

	public RationalMatrix(final BigInteger matrixDenominator, final QuadraticMatrix matrix) {
		mDenominator = matrixDenominator;
		mIntMatrix = matrix;
	}

	/**
	 * Computes the inverse of the matrix using the inverse of the integer matrix: (c*M)^-1 = c^-1 * M ^-1.
	 */
	public static RationalMatrix computeInverse(final RationalMatrix matrix) {
		final int n = matrix.mIntMatrix.getDimension();
		final RationalMatrix matrixInverse = QuadraticMatrix.computeInverse(matrix.mIntMatrix);
		Rational factorInverse = Rational.valueOf(matrix.mDenominator, matrixInverse.mDenominator);
		factorInverse = Rational.valueOf(factorInverse.numerator(), factorInverse.denominator());
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				matrix.mIntMatrix.setEntry(i, j, matrix.mIntMatrix.getEntry(i, j).multiply(factorInverse.numerator()));
			}
		}
		matrixInverse.mDenominator = factorInverse.denominator();
		return matrixInverse;
	}

	/**
	 * Adds vector to j-th column of matrix. If number of entries in vector is smaller than number of rows in matrix,
	 * then vector is still written in matrix, starting at row zero.
	 *
	 * @param j
	 *            column in which vector is written
	 * @param vector
	 *            to be written in matrix.
	 */
	public void addColumnToMatrix(final int j, final Rational[] vector) {
		final QuadraticMatrix intMatrix = mIntMatrix;
		final int n = intMatrix.getDimension();
		for (int i = 0; i < vector.length; i++) {
			vector[i] = Rational.valueOf(vector[i].numerator(), vector[i].denominator());
			final BigInteger gcd = Rational.gcd(vector[i].denominator(), mDenominator);
			intMatrix.setEntry(i, j, vector[i].numerator().multiply(mDenominator.divide(gcd)));
			mDenominator = mDenominator.multiply(vector[i].denominator().divide(gcd));
			for (int l = 0; l < n; l++) {
				for (int k = 0; k < n; k++) {
					intMatrix.setEntry(l, k, intMatrix.getEntry(l, k).multiply(vector[i].denominator().divide(gcd)));
				}
			}
			intMatrix.setEntry(i, j, intMatrix.getEntry(i, j).divide(vector[i].denominator().divide(gcd)));
		}
	}

	/**
	 * Adds vector to i-th row of matrix. If number of entries in vector is smaller than number of columns in matrix,
	 * then vector is still written in matrix, starting at column zero.
	 *
	 * @param i
	 *            row in which vector is written
	 * @param vector
	 *            to be written in matrix.
	 */
	public void addRowToMatrix(final int i, final Rational[] vector) {
		final QuadraticMatrix intMatrix = mIntMatrix;
		final int n = intMatrix.getDimension();
		for (int j = 0; j < vector.length; j++) {
			vector[j] = Rational.valueOf(vector[j].numerator(), vector[j].denominator());
			final BigInteger gcd = Rational.gcd(vector[j].denominator(), mDenominator);
			intMatrix.setEntry(i, j, vector[j].numerator().multiply(mDenominator.divide(gcd)));
			mDenominator = mDenominator.multiply(vector[j].denominator().divide(gcd));
			for (int k = 0; k < n; k++) {
				for (int l = 0; l < n; l++) {
					intMatrix.setEntry(k, l, intMatrix.getEntry(k, l).multiply(vector[j].denominator().divide(gcd)));
				}
			}
			intMatrix.setEntry(i, j, intMatrix.getEntry(i, j).divide(vector[j].denominator().divide(gcd)));
		}
	}

	/**
	 * Solves a linear equation system les, with k-th choice 1, all other choices 0, with
	 * additional constraints that solution of linear equation system and constraining vectors are
	 * linearly independent. To achieve this, the constraining vectors are added to the linear equation
	 * system with right-hand side 0 (scalar product of constraint and solution is 0).
	 */
	public static Rational[] solveLes(final RationalMatrix les, final Rational[][] constraints, final int k) {
		final int numberOfConstraints = constraints.length;
		final RationalMatrix lesGauss1 =
				new RationalMatrix(BigInteger.valueOf(1), QuadraticMatrix.gaussElimination(les.mIntMatrix));
		final int rank = lesGauss1.mIntMatrix.computeRank();
		for (int i = 0; i < numberOfConstraints; i++) {
			lesGauss1.addRowToMatrix(rank + i, constraints[i]);
		}
		// Keep 1 in last non-zero row.
		lesGauss1.mIntMatrix.setEntry(lesGauss1.mIntMatrix.computeRank() - 1, lesGauss1.mIntMatrix.getDimension() - 1,
				BigInteger.valueOf(1));
		final QuadraticMatrix lesGauss2 = QuadraticMatrix.gaussElimination(lesGauss1.mIntMatrix);
		final Rational[] solution = QuadraticMatrix.backwardSubstitution(lesGauss2, k);
		return solution;
	}

	public QuadraticMatrix getIntMatrix() {
		return mIntMatrix;
	}

	public BigInteger getDenominator() {
		return mDenominator;
	}
}