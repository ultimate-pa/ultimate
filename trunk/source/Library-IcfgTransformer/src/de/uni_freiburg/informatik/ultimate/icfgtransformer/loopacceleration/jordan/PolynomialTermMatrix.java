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

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.QuadraticMatrix.JordanTransformationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
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
	 * Construct the term it(it-1)*...*(it-j) which is the numerator of the entries of the it-th power of the
	 * Jordan matrix. Multiply this term by (k+1)*(k+2)*...*(it-blockSize+1) to make sure that fractions in
	 * PolynomialTermMatrix are reduced.
	 */
	private static IPolynomialTerm constructBinomialCoefficientNumerator(final Script script, final TermVariable it,
			final TermVariable itHalf, final int k, final int blockSize, final boolean itEven,
			final boolean restrictedVersionPossible) {
		final Sort sort = SmtSortUtils.getIntSort(script);
		final IPolynomialTerm iterCount = constructIterationCounter(script, restrictedVersionPossible, itEven, it, itHalf);
		if (k==0) {
			return AffineTerm.constructConstant(sort, Rational.valueOf(
					computeFacultyWithStartValue(1,blockSize-1), BigInteger.ONE));
		} else if (k==1) {
			return PolynomialTerm.mulPolynomials(AffineTerm.constructConstant(sort, Rational.valueOf(
					computeFacultyWithStartValue(1,blockSize-1), BigInteger.ONE)),iterCount);
		}
		final IPolynomialTerm facultyFactor = AffineTerm.constructConstant(sort, Rational.valueOf(
				computeFacultyWithStartValue(k+1,blockSize-1), BigInteger.ONE));
		IPolynomialTerm varMinusKFaculty = PolynomialTerm.mulPolynomials(facultyFactor,iterCount);
		for (int i=1; i<k; i++) {
			final IPolynomialTerm constant = AffineTerm.constructConstant(sort, Rational.valueOf(BigInteger.valueOf(-i),
					BigInteger.ONE));
			final IPolynomialTerm varMinusConstant = PolynomialTerm.sum(iterCount, constant);
			varMinusKFaculty = PolynomialTerm.mulPolynomials(varMinusKFaculty, varMinusConstant);
		}
		return varMinusKFaculty;
	}

	/**
	 * Construct an {@link IPolynomialTerm} that represents the current iteration
	 * (which is also the exponent of the Jordan matrix that we construct). The
	 * result can be
	 * <li>`it` (can represent all iterations)
	 * <li>`2*itHalf` (can represent even iterations)
	 * <li>`2*itHalf+1` (can represent odd iterations)
	 *
	 * Note: We have to distinguish even and odd transitions
	 * <li> if some eigenvalue is negative (currently we only support -1) or
	 * <li> if some Jordan block is greater than 2.
	 */
	private static IPolynomialTerm constructIterationCounter(final Script script,
			final boolean restrictedVersionPossible, final boolean itEven, final TermVariable it,
			final TermVariable itHalf) {
		final Sort sort = SmtSortUtils.getIntSort(script);
		final IPolynomialTerm result;
		if (restrictedVersionPossible) {
			result = AffineTerm.constructVariable(it);
		} else {
			if (itEven) {
				result = PolynomialTerm.mulPolynomials(AffineTerm.constructConstant(sort, Rational.TWO),
						AffineTerm.constructVariable(itHalf));
			} else {
				result = PolynomialTerm.sum(
						PolynomialTerm.mulPolynomials(AffineTerm.constructConstant(sort, Rational.TWO),
								AffineTerm.constructVariable(itHalf)),
						AffineTerm.constructConstant(sort, Rational.ONE));
			}
		}
		return result;
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
	private static PolynomialTermMatrix createBlock(final ManagedScript mgdScript, final TermVariable it,
			final TermVariable itHalf, final int lambda, final int blockSize, final boolean itEven,
			final boolean restrictedVersionPossible) {
		final Script script = mgdScript.getScript();
		final PolynomialTermMatrix block = constructConstantZeroMatrix(mgdScript, blockSize);
		if (lambda == 1) {
			for (int j=0; j<blockSize; j++) {
				// first row
				block.mEntries[0][j] = constructBinomialCoefficientNumerator(script, it, itHalf, j, blockSize, itEven,
						restrictedVersionPossible);
				// all other rows
				if (j!=0) {
					for (int i=1; i<blockSize; i++) {
						block.mEntries[i][j] = block.mEntries[i-1][j-1];
					}
				}
			}
			block.mDenominator = computeFacultyWithStartValue(1,blockSize-1);
		} else if (lambda == -1) {
			final Sort sort = SmtSortUtils.getIntSort(script);
			// iterate over all columns j
			for (int j=0; j<blockSize; j++) {
				// first row
				if (itEven == (j % 2 == 0)) {
					block.mEntries[0][j] = constructBinomialCoefficientNumerator(script, it, itHalf, j, blockSize,
							itEven, restrictedVersionPossible);
				} else {
					block.mEntries[0][j] = PolynomialTerm.mulPolynomials(constructBinomialCoefficientNumerator(script,
							it, itHalf, j, blockSize, itEven, restrictedVersionPossible),
							AffineTerm.constructConstant(sort, Rational.valueOf(BigInteger.valueOf(-1),
									BigInteger.ONE)));
				}
				// all other rows
				if (j!=0) {
					// we omit the first colum (colum 0) since it is filled with zeros anyway
					for (int i=1; i<blockSize; i++) {
						block.mEntries[i][j] = block.mEntries[i-1][j-1];
					}
				}
			}
			block.mDenominator = computeFacultyWithStartValue(1,blockSize-1);
		}
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
						AffineTerm.constructConstant(sort, Rational.valueOf(mDenominator.divide(gcd),
								BigInteger.ONE)));
			}
		}
		mDenominator = mDenominator.multiply(block.mDenominator.divide(gcd));
		for (int k=0; k<start; k++) {
			for (int l=0; l<mDimension; l++) {
				mEntries[k][l] = PolynomialTerm.mulPolynomials(mEntries[k][l],
						AffineTerm.constructConstant(sort, Rational.valueOf(block.mDenominator.divide(gcd),
								BigInteger.ONE)));
			}
		}
		for (int k=start+s; k<mDimension; k++) {
			for (int l=0; l<mDimension; l++) {
				mEntries[k][l] = PolynomialTerm.mulPolynomials(mEntries[k][l],
						AffineTerm.constructConstant(sort, Rational.valueOf(block.mDenominator.divide(gcd),
								BigInteger.ONE)));
			}
		}
	}

	/**
	 * Create the it-th power of a Jordan matrix out of the Jordan matrix.
	 */
	public static PolynomialTermMatrix jordan2JordanPower(final ManagedScript mgdScript, final TermVariable it,
			final TermVariable itHalf, final boolean itEven, final JordanTransformationResult jordan,
			final boolean restrictedVersionPossible) {
		final int n = jordan.getJnf().getDimension();
		final PolynomialTermMatrix jordanPower = constructConstantZeroMatrix(mgdScript, n);
		final NestedMap2<Integer, Integer, Integer> jordanBlockSizes = jordan.getJordanBlockSizes();
		int current = 0;
		for (int e=-1; e<=1; e++) {
			if (jordanBlockSizes.get(e) != null) {
				for (final Integer blockSize : jordanBlockSizes.get(e).keySet()) {
					if (blockSize != null) {
						for (int occ=1; occ<=jordanBlockSizes.get(e, blockSize); occ++) {
							final PolynomialTermMatrix block = createBlock(mgdScript, it, itHalf, e, blockSize, itEven,
									restrictedVersionPossible);
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
	 * Method that computes matrix that represents closed form out of the jordan decomposition.
	 * If !restrictedVersionPossible computes two closed form matrices for the two cases that
	 * the iteration count is even or odd.
	 */
	public static PolynomialTermMatrix computeClosedFormMatrix(final ManagedScript mgdScript,
			final JordanTransformationResult jordanUpdate, final TermVariable it, final TermVariable itHalf,
			final boolean itEven, boolean restrictedVersionPossible) {
		final int n = jordanUpdate.getJnf().getDimension();
		final Script script = mgdScript.getScript();
		final Sort sort = SmtSortUtils.getIntSort(script);
		final RationalMatrix modalUpdate = jordanUpdate.getModal();
		final RationalMatrix inverseModalUpdate = jordanUpdate.getInverseModal();
		PolynomialTermMatrix closedFormMatrix = constructConstantZeroMatrix(mgdScript, n);
		if (restrictedVersionPossible) {
			final PolynomialTermMatrix jordanUpdatePower = jordan2JordanPower(mgdScript, it, itHalf, itEven, jordanUpdate,
					restrictedVersionPossible);
			final PolynomialTermMatrix tmp = multiplication(mgdScript,
					rationalMatrix2TermMatrix(script, modalUpdate), jordanUpdatePower);
			closedFormMatrix = multiplication(mgdScript, tmp,
					rationalMatrix2TermMatrix(script, inverseModalUpdate));
			final IPolynomialTerm denom = AffineTerm.constructConstant(sort, Rational.valueOf(BigInteger.ONE,
					closedFormMatrix.getDenominator()));

			for (int i=0; i<n; i++) {
				for (int j=0; j<n; j++) {
					final Rational constant = closedFormMatrix.getEntry(i,j).getConstant();
					for (final Rational coeff : closedFormMatrix.getEntry(i,j).getMonomial2Coefficient().values()) {
						if (coeff.numerator().intValue() % closedFormMatrix.getDenominator().intValue() != 0) {
							restrictedVersionPossible = false;
//							final Pair<PolynomialTermMatrix, Boolean> result = new Pair<>(null, false);
//							return result;
							// TODO Matthias: Check if this is really dead code.
							throw new AssertionError("Case should never occur");
						}
						if (constant.numerator().intValue() % closedFormMatrix.getDenominator().intValue() != 0) {
							restrictedVersionPossible = false;
//							final Pair<PolynomialTermMatrix, Boolean> result = new Pair<>(null, false);
//							return result;
							// TODO Matthias: Check if this is really dead code.
							throw new AssertionError("Case should never occur");
						}
					}
					closedFormMatrix.setEntry(i,j,PolynomialTerm.mulPolynomials(
							closedFormMatrix.getEntry(i,j), denom));
				}
			}
		}
		if (!restrictedVersionPossible) {
			final PolynomialTermMatrix jordanUpdatePower = jordan2JordanPower(mgdScript, it, itHalf, itEven, jordanUpdate,
					restrictedVersionPossible);
			final PolynomialTermMatrix tmp = multiplication(mgdScript,
					rationalMatrix2TermMatrix(script, modalUpdate), jordanUpdatePower);
			closedFormMatrix = multiplication(mgdScript, tmp,
					rationalMatrix2TermMatrix(script, inverseModalUpdate));
			final IPolynomialTerm denom = AffineTerm.constructConstant(sort, Rational.valueOf(BigInteger.ONE,
					closedFormMatrix.getDenominator()));
			for (int i=0; i<n; i++) {
				for (int j=0; j<n; j++) {
					final Rational constant = closedFormMatrix.getEntry(i,j).getConstant();
					for (final Rational coeff : closedFormMatrix.getEntry(i,j).getMonomial2Coefficient().values()) {
						if (coeff.numerator().intValue() % closedFormMatrix.getDenominator().intValue() != 0) {
							throw new AssertionError("Non-integer value found. Computation of closed form not"
									+ "possible.");
						}
						if (constant.numerator().intValue() % closedFormMatrix.getDenominator().intValue() != 0) {
							throw new AssertionError("Non-integer value found. Computation of closed form not"
									+ "possible.");
						}
					}
					closedFormMatrix.setEntry(i,j,PolynomialTerm.mulPolynomials(
							closedFormMatrix.getEntry(i,j), denom));
				}
			}
		}
		closedFormMatrix.mDenominator = BigInteger.ONE;
		return closedFormMatrix;
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
}
