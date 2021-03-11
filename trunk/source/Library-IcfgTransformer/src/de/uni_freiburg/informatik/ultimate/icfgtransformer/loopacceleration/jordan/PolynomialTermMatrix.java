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

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

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
	private int mDimension;
	/**
	 * mEntries is an ApplicationTerm array of arrays representing the entries of the matrix.
	 */
	private IPolynomialTerm[][] mEntries;
	/**
	* mDenominator is the main denominator of the matrix.
	*/
	private BigInteger mDenominator;
		
	public PolynomialTermMatrix(BigInteger denominator, IPolynomialTerm[][] matrixEntries) {
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
	 * Construct a matrix where all entries are constant polynomial 0.
	 * @param mgdScript
	 * @param n
	 * @return
	 */
	private static PolynomialTermMatrix constantZeroMatrix(ManagedScript mgdScript, int n) {
		Script script = mgdScript.getScript();
		IPolynomialTerm[][] zeroMatrixEntries = new IPolynomialTerm[n][n];
		Sort sort = SmtSortUtils.getIntSort(script);
		AffineTerm zero = AffineTerm.constructConstant(sort, Rational.ZERO);
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				zeroMatrixEntries[i][j] = zero;
			}
		}
		PolynomialTermMatrix zeroMatrix = new PolynomialTermMatrix(BigInteger.ONE, zeroMatrixEntries);
		return zeroMatrix;
	}
	
	/**
	 * Takes a RationalMatrix and transforms it to a PolynomialTermMatrix.
	 * @param script
	 * @param matrix
	 * @return
	 */
	public static PolynomialTermMatrix rationalMatrix2TermMatrix(Script script, RationalMatrix matrix) {
		final int n = matrix.getIntMatrix().getDimension();
		final Sort sort = SmtSortUtils.getIntSort(script);
		IPolynomialTerm[][] termMatrixEntries = new IPolynomialTerm[n][n];
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				Rational entry = Rational.valueOf(matrix.getIntMatrix().getEntry(i,j), BigInteger.ONE);
				termMatrixEntries[i][j] = AffineTerm.constructConstant(sort, entry);
			}
		}
		PolynomialTermMatrix termMatrix = new PolynomialTermMatrix(matrix.getDenominator(), termMatrixEntries);
		return termMatrix;
	}

	/**
	 * Construct the term n(n-1)*...*(n-j) which is the numerator of the entries of the n-th power of the
	 * Jordan matrix. Multiply this term by (k+1)*(k+2)*...*(n-blockSize+1) to make sure that fractions in 
	 * PolynomialTermMatrix are reduced.
	 * Substitute n = 2k if nEven, n = 2k+1 if !nEven
	 * @param script
	 * @param it
	 * @param k
	 * @param blockSize
	 * @return
	 */
	private static IPolynomialTerm binomialCoefficientNumerator(final Script script, final TermVariable itHalf,
			final int k, final int blockSize, boolean nEven) {
		final Sort sort = SmtSortUtils.getIntSort(script);
		IPolynomialTerm var = AffineTerm.constructVariable(itHalf);
		if (nEven) {
			var = PolynomialTerm.mulPolynomials(AffineTerm.constructConstant(sort, Rational.TWO),
					AffineTerm.constructVariable(itHalf));
		} else {
			var = PolynomialTerm.mulPolynomials(AffineTerm.constructConstant(sort, Rational.TWO),
					AffineTerm.constructVariable(itHalf));
			var = PolynomialTerm.sum(var, AffineTerm.constructConstant(sort,Rational.ONE));
		}
		if (k==0) {
			return AffineTerm.constructConstant(sort, Rational.valueOf(
					facultyWithStartValue(1,blockSize-1), BigInteger.ONE));
		}
		if (k==1) {
			return PolynomialTerm.mulPolynomials(AffineTerm.constructConstant(sort, Rational.valueOf(
					facultyWithStartValue(1,blockSize-1), BigInteger.ONE)),var);
		}
		IPolynomialTerm facultyFactor = AffineTerm.constructConstant(sort, Rational.valueOf(
				facultyWithStartValue(k+1,blockSize-1), BigInteger.ONE));
		IPolynomialTerm varMinusKFaculty = PolynomialTerm.mulPolynomials(facultyFactor,var);
		for (int i=1; i<k; i++) {
			IPolynomialTerm constant = AffineTerm.constructConstant(sort, Rational.valueOf(BigInteger.valueOf(-i),
					BigInteger.ONE));
			IPolynomialTerm varMinusConstant = PolynomialTerm.sum(var, constant);
			varMinusKFaculty = PolynomialTerm.mulPolynomials(varMinusKFaculty, varMinusConstant);
		}
		return varMinusKFaculty;
	}
	
	/**
	 * Compute start*(start+1)*...*k which represents the main denominator of the n-th power of the Jordan matrix.
	 * @param start
	 * @param k
	 * @return
	 */
	private static BigInteger facultyWithStartValue(final int start, final int k) {
		BigInteger faculty = BigInteger.ONE;
		for (int i=start; i<=k; i++) {
			faculty = faculty.multiply(BigInteger.valueOf(i));
		}
		return faculty;
	}
	
	/**
	 * Create a block of the n-th power of the Jordan matrix of size blockSize for eigenvalue lamda.
	 * @param mgdScript
	 * @param it
	 * @param lambda
	 * @param blockSize
	 * @param nEven
	 * @return
	 */
	private static PolynomialTermMatrix createBlock(final ManagedScript mgdScript, final TermVariable it,
			final int lambda, final int blockSize, final boolean nEven) {
		final Script script = mgdScript.getScript();
		final Sort sort = SmtSortUtils.getIntSort(script);
		PolynomialTermMatrix block = constantZeroMatrix(mgdScript, blockSize);
		if (lambda == 1) {
			for (int j=0; j<blockSize; j++) {
				// first row
				block.mEntries[0][j] = binomialCoefficientNumerator(script, it, j, blockSize, true);
				// all other rows
				if (j!=0) {
					for (int i=1; i<blockSize; i++) {
						block.mEntries[i][j] = block.mEntries[i-1][j-1];
					}
				}
			}
			block.mDenominator = facultyWithStartValue(1,blockSize-1);
		}
		if (lambda == -1) {
			if (nEven) {
				for (int j=0; j<blockSize; j++) {
					// first row
					if (j % 2 == 0) {
						block.mEntries[0][j] = binomialCoefficientNumerator(script, it, j, blockSize, true);
					} else {
						block.mEntries[0][j] = PolynomialTerm.mulPolynomials(binomialCoefficientNumerator(script, it,
								j, blockSize, true), AffineTerm.constructConstant(sort, Rational.valueOf(
										BigInteger.valueOf(-1), BigInteger.ONE)));
					}
					// all other rows
					if (j!=0) {
						for (int i=j; i<blockSize; i++) {
							block.mEntries[i][j] = block.mEntries[i-1][j-1];
						}
					}
				}
			} else {
				for (int j=0; j<blockSize; j++) {
					// first row
					if (j % 2 != 0) {
						block.mEntries[0][j] = binomialCoefficientNumerator(script, it, j, blockSize, false);
					} else {
						block.mEntries[0][j] = PolynomialTerm.mulPolynomials(binomialCoefficientNumerator(script, it,
								j, blockSize, false), AffineTerm.constructConstant(sort, Rational.valueOf(
										BigInteger.valueOf(-1), BigInteger.ONE)));
					}
					// all other rows
					if (j!=0) {
						for (int i=j; i<blockSize; i++) {
							block.mEntries[i][j] = block.mEntries[i-1][j-1];
						}
					}
				}
			}
			block.mDenominator = facultyWithStartValue(1,blockSize-1);
		}
		return block;
	}
	
	/**
	 * Add a block to the n-th power of the Jordan matrix. Make sure that main denominator stays correct and all
	 * fractions are reduced.
	 * @param mgdScript
	 * @param block
	 * @param start
	 */
	private void addBlockToJordanPower(ManagedScript mgdScript, final PolynomialTermMatrix block, final int start) {
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
	 * Create the n-th power of a Jordan matrix out of the Jordan matrix.
	 * @param matrix
	 * @param mgdScript
	 * @param it
	 * @param jordan
	 * @param nEven
	 * @return
	 */
	public static PolynomialTermMatrix jordanToJordanPower(QuadraticMatrix matrix, final ManagedScript mgdScript,
			final TermVariable it, final QuadraticMatrix jordan, boolean nEven) {
		final int n = jordan.getDimension();
		PolynomialTermMatrix jordanPower = constantZeroMatrix(mgdScript, n);
		final boolean[] eigenvalues = matrix.smallEigenvalues();
		// for each eigenvalue compute number of Jordan blocks.
		int current = 0;
		for (int e=-1; e<=1; e++) {
			if(eigenvalues[e+1]) {
				final int geomMult = matrix.geometricMultiplicity(e);
				int[] numberOfBlocks = new int[n+1];
				int sum = 0;
				while (sum < geomMult) {
					for (int sE=1; sE<=n; sE++) {
						numberOfBlocks[sE] = matrix.numberOfBlocks(e, sE);
						sum = sum + numberOfBlocks[sE];
					}
				}
				for (int s=1; s<=n; s++) {
					for (int i=0; i<numberOfBlocks[s]; i++) {
						final PolynomialTermMatrix block = createBlock(mgdScript, it, e, s, nEven);
						jordanPower.addBlockToJordanPower(mgdScript, block, current);
						current = current + s;
					}
				}
			}
		}
		return jordanPower;
	}
	
	/**
	 * Multiplication of two PolynomialTermMatrices.
	 * @param mgdScript
	 * @param matrix1
	 * @param matrix2
	 * @return
	 */
	public static PolynomialTermMatrix multiplication(ManagedScript mgdScript, PolynomialTermMatrix matrix1,
			PolynomialTermMatrix matrix2) {
		if (matrix1.mDimension != matrix2.mDimension) {
			throw new AssertionError("Some matrices for multiplication are not of the same dimension.");
		}
		final int n = matrix1.mDimension;
		PolynomialTermMatrix product = constantZeroMatrix(mgdScript, n);
		final Sort sort = SmtSortUtils.getIntSort(mgdScript);
		for (int i=0; i<n; i++) {
			for (int k=0; k<n; k++) {
				IPolynomialTerm sum = AffineTerm.constructConstant(sort, Rational.ZERO);
				for (int j=0; j<n; j++) {
					IPolynomialTerm summand = PolynomialTerm.mulPolynomials(matrix1.mEntries[i][j],
							matrix2.mEntries[j][k]);
					sum = PolynomialTerm.sum(sum, summand);
				}
				product.mEntries[i][k] = sum;
			}
		}
		product.mDenominator = matrix1.mDenominator.multiply(matrix2.mDenominator);
		return product;
	}
	
	/**
	 * Method that computes matrix that represents closed form out of the jordan decomposition.
	 * Computes two closed form matrices for the two cases that the iteration count is even or odd.
	 * They are different if -1 is an eigenvalue.
	 * @param mgdScript
	 * @param updateMatrix
	 * @param modalUpdate
	 * @param jordanUpdate
	 * @param inverseModalUpdate
	 * @param it
	 * @param nEven
	 * @return
	 */
	public static PolynomialTermMatrix closedFormMatrix(ManagedScript mgdScript, QuadraticMatrix updateMatrix,
			RationalMatrix modalUpdate, QuadraticMatrix jordanUpdate, RationalMatrix inverseModalUpdate,
			TermVariable it, boolean nEven) {
		final int n = jordanUpdate.getDimension();
		final Script script = mgdScript.getScript();
		Sort sort = it.getSort();
		if (nEven) {
			final PolynomialTermMatrix jordanUpdatePowerNEven = jordanToJordanPower(updateMatrix, mgdScript, it,
					jordanUpdate, true);
			final PolynomialTermMatrix tmpEven = multiplication(mgdScript,
					rationalMatrix2TermMatrix(script, modalUpdate), jordanUpdatePowerNEven);
			final PolynomialTermMatrix closedFormEvenMatrix = multiplication(mgdScript, tmpEven,
					rationalMatrix2TermMatrix(script, inverseModalUpdate));
			
			IPolynomialTerm denom = AffineTerm.constructConstant(sort, Rational.valueOf(BigInteger.ONE,
					closedFormEvenMatrix.getDenominator()));
			for (int i=0; i<n; i++) {
				for (int j=0; j<n; j++) {
					Rational constEven = closedFormEvenMatrix.getEntry(i,j).getConstant();
					for (Rational coeffEven : closedFormEvenMatrix.getEntry(i,j).getMonomial2Coefficient().values()) {
						if (coeffEven.numerator().intValue() % closedFormEvenMatrix.getDenominator().intValue() != 0) {
							throw new AssertionError("Non-integer value found. Computation of closed form not possible.");
						}
						if (constEven.numerator().intValue() % closedFormEvenMatrix.getDenominator().intValue() != 0) {
							throw new AssertionError("Non-integer value found. Computation of closed form not possible.");
						}
					}
					closedFormEvenMatrix.setEntry(i,j,PolynomialTerm.mulPolynomials(
							closedFormEvenMatrix.getEntry(i,j), denom));
				}
			}
			closedFormEvenMatrix.mDenominator = BigInteger.ONE;
			return closedFormEvenMatrix;
		} else {
			final PolynomialTermMatrix jordanUpdatePowerNOdd = jordanToJordanPower(updateMatrix, mgdScript, it,
					jordanUpdate, false);
			final PolynomialTermMatrix tmpOdd = multiplication(mgdScript,
					rationalMatrix2TermMatrix(script, modalUpdate), jordanUpdatePowerNOdd);
			final PolynomialTermMatrix closedFormOddMatrix = multiplication(mgdScript, tmpOdd,
					rationalMatrix2TermMatrix(script, inverseModalUpdate));
			
			IPolynomialTerm denom = AffineTerm.constructConstant(sort, Rational.valueOf(BigInteger.ONE,
					closedFormOddMatrix.getDenominator()));
			for (int i=0; i<n; i++) {
				for (int j=0; j<n; j++) {
					Rational constEven = closedFormOddMatrix.getEntry(i,j).getConstant();
					for (Rational coeffEven : closedFormOddMatrix.getEntry(i,j).getMonomial2Coefficient().values()) {
						if (coeffEven.numerator().intValue() % closedFormOddMatrix.getDenominator().intValue() != 0) {
							throw new AssertionError("Non-integer value found. Computation of closed form not possible.");
						}
						if (constEven.numerator().intValue() % closedFormOddMatrix.getDenominator().intValue() != 0) {
							throw new AssertionError("Non-integer value found. Computation of closed form not possible.");
						}
					}
					closedFormOddMatrix.setEntry(i,j,PolynomialTerm.mulPolynomials(
							closedFormOddMatrix.getEntry(i,j), denom));
				}
			}
			closedFormOddMatrix.mDenominator = BigInteger.ONE;
			return closedFormOddMatrix;
		}
	}
	
	public IPolynomialTerm getEntry(int i, int j) {
		return mEntries[i][j];
	}
	
	public void setEntry(int i, int j, IPolynomialTerm value) {
		mEntries[i][j] = value;
	}
	
	public BigInteger getDenominator() {
		return mDenominator;
	}
	
	public int getDimension() {
		return mDimension;
	}
}
