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

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanLoopAcceleration.Iterations;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 *
 * Class for quadratic polynomialTerm matrices used for closed form computation given Jodran decomposition.
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class PolynomialTermMatrix {
	/**
	* mDimension is an integer representing the number of rows/columns of the matrix.
	*/
	private final int mDimension;
	/**
	 * mEntries is an IPolynomialTerm array of arrays representing the entries of the matrix.
	 */
	private final IPolynomialTerm[][] mEntries;
	/**
	* mDenominator is the main denominator of the matrix.
	*/
	private BigInteger mDenominator;

	public PolynomialTermMatrix(final BigInteger denominator, final IPolynomialTerm[][] matrixEntries) {
		final int numberOfRows = matrixEntries.length;
		for (int i=0; i<numberOfRows; i++) {
			if (numberOfRows != matrixEntries[i].length) {
				throw new AssertionError("Some matrix is not quadratic");
			}
		}
		mEntries = matrixEntries;
		mDimension = numberOfRows;
		mDenominator = denominator;
	}

	/**
	 * Construct a matrix of dimension n where all entries are constant polynomial 0.
	 */
	private static PolynomialTermMatrix constructConstantZeroMatrix(final ManagedScript mgdScript, final int n) {
		final Script script = mgdScript.getScript();
		final IPolynomialTerm[][] zeroMatrixEntries = new IPolynomialTerm[n][n];
		final Sort sort = SmtSortUtils.getIntSort(script);
		final AffineTerm zero = AffineTerm.constructConstant(sort, Rational.ZERO);
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				zeroMatrixEntries[i][j] = zero;
			}
		}
		final PolynomialTermMatrix zeroMatrix = new PolynomialTermMatrix(BigInteger.ONE, zeroMatrixEntries);
		return zeroMatrix;
	}

	/**
	 * Takes a RationalMatrix and transforms it to a PolynomialTermMatrix.
	 */
	public static PolynomialTermMatrix rationalMatrix2TermMatrix(final Script script, final RationalMatrix matrix) {
		final int n = matrix.getIntMatrix().getDimension();
		final Sort sort = SmtSortUtils.getIntSort(script);
		final IPolynomialTerm[][] termMatrixEntries = new IPolynomialTerm[n][n];
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				final Rational entry = Rational.valueOf(matrix.getIntMatrix().getEntry(i,j), BigInteger.ONE);
				termMatrixEntries[i][j] = AffineTerm.constructConstant(sort, entry);
			}
		}
		final PolynomialTermMatrix termMatrix = new PolynomialTermMatrix(matrix.getDenominator(), termMatrixEntries);
		return termMatrix;
	}

	/**
	 * Construct the term itc(itc-1)*...*(itc-j) which is the numerator of the
	 * entries of the itc-th power of the Jordan matrix. Multiply this term by
	 * (k+1)*(k+2)*...*(itc-blockSize+1) to make sure that fractions in
	 * PolynomialTermMatrix are reduced.
	 * @param itc {@link IPolynomialTerm} that represents the exponent
	 */
	private static IPolynomialTerm constructBinomialCoefficientNumerator(final Script script,
			final IPolynomialTerm itc, final int k, final int blockSize) {
		final Sort sort = SmtSortUtils.getIntSort(script);
		if (k == 0) {
			return AffineTerm.constructConstant(sort, computeFacultyWithStartValue(1, blockSize - 1));
		} else if (k == 1) {
			return PolynomialTerm.mulPolynomials(
					AffineTerm.constructConstant(sort, computeFacultyWithStartValue(1, blockSize - 1)), itc);
		}
		final IPolynomialTerm facultyFactor = AffineTerm.constructConstant(sort,
				computeFacultyWithStartValue(k + 1, blockSize - 1));
		IPolynomialTerm varMinusKFaculty = PolynomialTerm.mulPolynomials(facultyFactor, itc);
		for (int i = 1; i < k; i++) {
			final IPolynomialTerm constant = AffineTerm.constructConstant(sort, -i);
			final IPolynomialTerm varMinusConstant = PolynomialTerm.sum(itc, constant);
			varMinusKFaculty = PolynomialTerm.mulPolynomials(varMinusKFaculty, varMinusConstant);
		}
		return varMinusKFaculty;
	}

	/**
	 * Compute start*(start+1)*...*k which represents the main denominator of the it-th power of the Jordan matrix.
	 */
	private static BigInteger computeFacultyWithStartValue(final int start, final int k) {
		BigInteger faculty = BigInteger.ONE;
		for (int i=start; i<=k; i++) {
			faculty = faculty.multiply(BigInteger.valueOf(i));
		}
		return faculty;
	}

	/**
	 * Create a block of the it-th power of the Jordan matrix of size blockSize for eigenvalue lamda.
	 * if !restrictedVersionPossible, it is represented by 2*itHalf if itEven and 2*itHalf+1 if !itEven.
	 */
	private static PolynomialTermMatrix createBlock(final ManagedScript mgdScript, final IPolynomialTerm itc,
			final int lambda, final int blockSize, final Iterations itKind) {
		if (lambda != -1 && lambda != 0 && lambda != 1) {
			throw new UnsupportedOperationException("Only eigenvalues -1,0,1 are supported");
		}
		final Script script = mgdScript.getScript();
		final PolynomialTermMatrix block = constructConstantZeroMatrix(mgdScript, blockSize);
		if (lambda == 0) {
			// In this case we return a block filled with zeros.
			return block;
		}
		final Sort sort = SmtSortUtils.getIntSort(script);
		// iterate over all columns j
		for (int j = 0; j < blockSize; j++) {
			// first row
			final IPolynomialTerm matrixEntry;
			final IPolynomialTerm tmp = constructBinomialCoefficientNumerator(script, itc, j, blockSize);
			if (lambda == -1 && (itKind == Iterations.EVEN) != (j % 2 == 0)) {
				// If the eigenvalue lambda is negative, we might have to multiply the matrix
				// entry by -1. If we consider only even iteration numbers, then entries of the
				// odd columns are multiplied by -1. If we consider only odd numbers, the
				// entries of the even columns are multiplied by -1.
				matrixEntry = PolynomialTerm.mulPolynomials(tmp, AffineTerm.constructConstant(sort, -1));
			} else {
				matrixEntry = tmp;
			}
			block.mEntries[0][j] = matrixEntry;
			// all other rows
			if (j != 0) {
				// we omit the first colum (colum 0) since it is filled with zeros anyway
				for (int i = 1; i < blockSize; i++) {
					block.mEntries[i][j] = block.mEntries[i - 1][j - 1];
				}
			}
		}
		block.mDenominator = computeFacultyWithStartValue(1, blockSize - 1);
		return block;
	}

	/**
	 * Adds a block to the it-th power of the Jordan matrix. Makes sure that main denominator stays correct and all
	 * fractions are reduced.
	 */
	private void addBlockToJordanPower(final ManagedScript mgdScript, final PolynomialTermMatrix block,
			final int start) {
		if (mDimension < block.mDimension + start) {
			throw new AssertionError("Block does not fit into matrix");
		}
		final Sort sort = SmtSortUtils.getIntSort(mgdScript.getScript());
		final int s = block.mDimension;
		final BigInteger gcd = Rational.gcd(mDenominator, block.mDenominator);
		for (int i=0; i<s; i++) {
			for (int j=0; j<s; j++) {
				mEntries[i+start][j+start] = PolynomialTerm.mulPolynomials(block.mEntries[i][j],
						AffineTerm.constructConstant(sort, mDenominator.divide(gcd)));
			}
		}
		mDenominator = mDenominator.multiply(block.mDenominator.divide(gcd));
		for (int k=0; k<start; k++) {
			for (int l=0; l<mDimension; l++) {
				mEntries[k][l] = PolynomialTerm.mulPolynomials(mEntries[k][l],
						AffineTerm.constructConstant(sort, block.mDenominator.divide(gcd)));
			}
		}
		for (int k=start+s; k<mDimension; k++) {
			for (int l=0; l<mDimension; l++) {
				mEntries[k][l] = PolynomialTerm.mulPolynomials(mEntries[k][l],
						AffineTerm.constructConstant(sort, block.mDenominator.divide(gcd)));
			}
		}
	}

	/**
	 * Create the it-th power of a Jordan matrix out of the Jordan matrix.
	 */
	public static PolynomialTermMatrix jordan2JordanPower(final ManagedScript mgdScript, final IPolynomialTerm itc,
			final Iterations itKind, final JordanDecomposition decomp) {
		final int n = decomp.getJnf().getDimension();
		final PolynomialTermMatrix jordanPower = constructConstantZeroMatrix(mgdScript, n);
		final NestedMap2<Integer, Integer, Integer> jordanBlockSizes = decomp.getJordanBlockSizes();
		int current = 0;
		for (int lambda=-1; lambda<=1; lambda++) {
			if (jordanBlockSizes.get(lambda) != null) {
				for (final Integer blockSize : jordanBlockSizes.get(lambda).keySet()) {
					if (blockSize != null) {
						for (int occ=1; occ<=jordanBlockSizes.get(lambda, blockSize); occ++) {
							final PolynomialTermMatrix block = createBlock(mgdScript, itc, lambda, blockSize,
									itKind);
							jordanPower.addBlockToJordanPower(mgdScript, block, current);
							current = current + blockSize;
						}
					}
				}
			}
		}
		return jordanPower;
	}

	/**
	 * Computes matrix that represents closed form for `itc` iterations.
	 */
	public static PolynomialTermMatrix computeClosedFormMatrix(final ManagedScript mgdScript,
			final JordanDecomposition decomp, final IPolynomialTerm itc, final Iterations itKind) {
		final int n = decomp.getJnf().getDimension();
		final Script script = mgdScript.getScript();
		final RationalMatrix modalUpdate = decomp.getModal();
		final RationalMatrix inverseModalUpdate = decomp.getInverseModal();
		PolynomialTermMatrix closedFormMatrix = constructConstantZeroMatrix(mgdScript, n);
		final PolynomialTermMatrix jordanUpdatePower = jordan2JordanPower(mgdScript, itc, itKind, decomp);
		final PolynomialTermMatrix tmp = multiplication(mgdScript, rationalMatrix2TermMatrix(script, modalUpdate),
				jordanUpdatePower);
		closedFormMatrix = multiplication(mgdScript, tmp, rationalMatrix2TermMatrix(script, inverseModalUpdate));
		return PolynomialTermMatrix.cancelDenominator(mgdScript, closedFormMatrix);
	}

	/**
	 * Computes matrix that represents the jordanUpdate that is multiplied k times
	 * with itself.
	 */
	public static PolynomialTermMatrix computeClosedFormMatrix(final ManagedScript mgdScript,
			final JordanDecomposition decomp, final int k) {
		final Script script = mgdScript.getScript();
		final RationalMatrix modalUpdate = decomp.getModal();
		final RationalMatrix inverseModalUpdate = decomp.getInverseModal();
		final QuadraticMatrix powerQm = QuadraticMatrix.power(decomp.getJnf(), k);
		final PolynomialTermMatrix jordanUpdatePower = rationalMatrix2TermMatrix(script,
				new RationalMatrix(BigInteger.ONE, powerQm));
		final PolynomialTermMatrix tmp = multiplication(mgdScript, rationalMatrix2TermMatrix(script, modalUpdate),
				jordanUpdatePower);
		final PolynomialTermMatrix closedFormMatrix = multiplication(mgdScript, tmp,
				rationalMatrix2TermMatrix(script, inverseModalUpdate));
		return PolynomialTermMatrix.cancelDenominator(mgdScript, closedFormMatrix);
	}

	/**
	 * Multiplication of two PolynomialTermMatrices.
	 */
	public static PolynomialTermMatrix multiplication(final ManagedScript mgdScript,
			final PolynomialTermMatrix matrix1, final PolynomialTermMatrix matrix2) {
		if (matrix1.mDimension != matrix2.mDimension) {
			throw new AssertionError("Some matrices for multiplication are not of the same dimension.");
		}
		final int n = matrix1.mDimension;
		final PolynomialTermMatrix product = constructConstantZeroMatrix(mgdScript, n);
		final Sort sort = SmtSortUtils.getIntSort(mgdScript);
		for (int i=0; i<n; i++) {
			for (int k=0; k<n; k++) {
				IPolynomialTerm sum = AffineTerm.constructConstant(sort, Rational.ZERO);
				for (int j=0; j<n; j++) {
					final IPolynomialTerm summand = PolynomialTerm.mulPolynomials(matrix1.mEntries[i][j],
							matrix2.mEntries[j][k]);
					sum = PolynomialTerm.sum(sum, summand);
				}
				product.mEntries[i][k] = sum;
			}
		}
		product.mDenominator = matrix1.mDenominator.multiply(matrix2.mDenominator);
		return product;
	}

	public IPolynomialTerm getEntry(final int i, final int j) {
		return mEntries[i][j];
	}

	public void setEntry(final int i, final int j, final IPolynomialTerm value) {
		mEntries[i][j] = value;
	}

	public BigInteger getDenominator() {
		return mDenominator;
	}

	public int getDimension() {
		return mDimension;
	}

	public static PolynomialTermMatrix cancelDenominator(final ManagedScript mgdScript,
			final PolynomialTermMatrix matrix) {
		final PolynomialTermMatrix result = constructConstantZeroMatrix(mgdScript, matrix.getDimension());
		for (int i = 0; i < result.getDimension(); i++) {
			for (int j = 0; j < result.getDimension(); j++) {
				final IPolynomialTerm entry = matrix.getEntry(i, j);
				final IPolynomialTerm newEntry = entry
						.divInvertible(Rational.valueOf(matrix.getDenominator(), BigInteger.ONE));
				if (newEntry == null) {
					return null;
				}
				result.setEntry(i, j, newEntry);
			}
		}
		return result;
	}
}
