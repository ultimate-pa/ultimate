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
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;

/**
 * Class for quadratic term matrices used for closed form computation given Jodran decomposition.
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class TermMatrix {
	/**
	 * mDimension is an integer representing the number of rows/columns of the matrix.
	 */
	private int mDimension;
	/**
	 * mEntries is an ApplicationTerm array of arrays representing the entries of the matrix.
	 */
	private Term[][] mEntries;
	
	public TermMatrix(Term[][] matrixEntries) {
		final int numberOfRows = matrixEntries.length;
		for (int i=0; i<numberOfRows; i++) {
			if (numberOfRows != matrixEntries[i].length) {
				throw new AssertionError("Some matrix is not quadratic");
			}
		}
		mEntries = matrixEntries;
		mDimension = numberOfRows;
	}
	
	/**
	 * Construct a matrix of dimension n where all entries are constant term 0.
	 * @param n
	 */
	private static TermMatrix constantZeroMatrix(Script script, int n) {
		Term[][] zeroMatrixEntries = new Term[n][n];
		Term zero = script.numeral(BigInteger.ZERO);
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				zeroMatrixEntries[i][j] = zero;
			}
		}
		TermMatrix zeroMatrix = new TermMatrix(zeroMatrixEntries);
		return zeroMatrix;
	}
	
	/**
	 * Takes a RationalMatrix and transforms it to a TermMatrix with constant terms where each term is represented as
	 * reduced fraction (/ a b).
	 * @param script
	 * @param matrix
	 * @return
	 */
	public static TermMatrix rationalMatrix2TermMatrix(Script script, RationalMatrix matrix) {
		final int n = matrix.getIntMatrix().getDimension();
		Term[][] matrixAsTermMatrixEntries = new Term[n][n];
		for (int i=0; i<n; i++) {
			for (int j=0; j<n; j++) {
				if (matrix.getIntMatrix().getEntry(i, j).intValue() == 0) {
					matrixAsTermMatrixEntries[i][j] = script.numeral(BigInteger.ZERO);
					continue;
				}
				final BigInteger gcd = Rational.gcd(matrix.getIntMatrix().getEntry(i, j), matrix.getDenominator());
				if (matrix.getDenominator().divide(gcd).intValue() == 1) {
					matrixAsTermMatrixEntries[i][j] = script.numeral(matrix.getIntMatrix().getEntry(i, j).divide(gcd));
				} else {
					matrixAsTermMatrixEntries[i][j] = script.term("/", script.numeral(matrix.getIntMatrix().getEntry(
							i, j).divide(gcd)), script.numeral(matrix.getDenominator().divide(gcd)));
				}
			}
		}
		TermMatrix matrixAsTermMatrix = new TermMatrix(matrixAsTermMatrixEntries);
		return matrixAsTermMatrix;
	}
	
	/**
	 * Construct term (n over k) = 1/k! * n*(n-1)*...*(n-k+1). Used for n-th power of jordan matrix.
	 * @param script
	 * @param it
	 * @param k
	 * @return
	 */
	private static Term binomialCoefficient2Term(final Script script, final TermVariable it, final int k) {
		if (k==0) {
			return script.numeral(BigInteger.ONE);
		}
		if (k==1) {
			return it;
		}
		BigInteger faculty = BigInteger.ONE;
		for (int i=1; i<=k; i++) {
			faculty = faculty.multiply(BigInteger.valueOf(i));
		}
		final Term kFaculty = script.numeral(faculty);
		/*Term[] facultyLeaves = new Term[k];
		for (int i=1; i<=k; i++) {
			facultyLeaves[i-1] = script.numeral(BigInteger.valueOf(i));
		}
		final Term kFaculty = script.term("*", facultyLeaves);*/
		Term[] nMinusK = new Term[k];
		nMinusK[0] = it;
		for (int i=1; i<k; i++) {
			nMinusK[i] = script.term("-", it, script.numeral(BigInteger.valueOf(i)));
		}
		final Term nMinusKFaculty = script.term("*", nMinusK);
		final Term binomialCoefficient = script.term("/", nMinusKFaculty, kFaculty);
		return binomialCoefficient;
	}
	
	/**
	 * Method to create a block of the n-th power of a jordan matrix for an eigenvalue lambda of size blockSize.
	 * If eigenvalue lambda is -1, then the block depends on whether n is even or not (nEven).
	 * @param script
	 * @param it
	 * @param lambda
	 * @param blockSize
	 * @param nEven
	 * @return
	 */
	private static TermMatrix createBlock(final Script script, final TermVariable it, final int lambda, final int blockSize,
			final boolean nEven) {
		TermMatrix block = constantZeroMatrix(script, blockSize);
		if (lambda == 1) {
			for (int j=0; j<blockSize; j++) {
				// first row
				block.mEntries[0][j] = binomialCoefficient2Term(script, it, j);
				// all other rows
				if (j!=0) {
					for (int i=1; i<blockSize; i++) {
						block.mEntries[i][j] = block.mEntries[i-1][j-1];
					}
				}
			}
		}
		if (lambda == -1) {
			if (nEven) {
				for (int j=0; j<blockSize; j++) {
					// first row
					if (j % 2 == 0) {
						block.mEntries[0][j] = binomialCoefficient2Term(script, it, j);
					} else {
						block.mEntries[0][j] = script.term("-", binomialCoefficient2Term(script, it, j));
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
						block.mEntries[0][j] = binomialCoefficient2Term(script, it, j);
					} else {
						block.mEntries[0][j] = script.term("-", binomialCoefficient2Term(script, it, j));
					}
					// all other rows
					if (j!=0) {
						for (int i=j; i<blockSize; i++) {
							block.mEntries[i][j] = block.mEntries[i-1][j-1];
						}
					}
				}
			}
		}
		return block;
	}
	
	/**
	 * Adds block to existing power of jordan matrix beginning at index start.
	 * @param block
	 * @param start
	 */
	private void addBlockToJordanPower(final TermMatrix block, final int start) {
		if (mDimension < block.mDimension + start) {
			throw new AssertionError("Block does not fit into matrix");
		}
		final int s = block.mDimension;
		for (int i=0; i<s; i++) {
			for (int j=0; j<s; j++) {
				mEntries[i+start][j+start] = block.mEntries[i][j];
			}
		}
	}
	
	/**
	 * Method to create the ApplicationTermMatrix jordan^n out of a Jordan matrix. Analogous to jordanMatrix in
	 * QuadraticMatrix class. Warning: Only works if jordan is corresponding jordan matrix to matrix.
	 * @param matrix
	 * @param script
	 * @param it
	 * @param jordan
	 * @param nEven
	 * @return
	 */
	public static TermMatrix jordanToJordanPower(QuadraticMatrix matrix, final Script script, final TermVariable it,
			final QuadraticMatrix jordan, boolean nEven) {
		final int n = jordan.getDimension();
		TermMatrix jordanPower = constantZeroMatrix(script, n);
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
						final TermMatrix block = createBlock(script, it, e, s, nEven);
						jordanPower.addBlockToJordanPower(block, current);
						current = current + s;
					}
				}
			}
		}
		return jordanPower;
	}
	
	/**
	 * Takes two Term matrices and returns a new ApplicationTermMatrix which is the usual matrix product of the two
	 * input matrices. Simplifies terms but not completely.
	 * TODO: Find better way to simplify terms.
	 * @param matrix1
	 * @param matrix2
	 * @return
	 */
	public static TermMatrix multiplication(Script script, TermMatrix matrix1, TermMatrix matrix2) {
		if (matrix1.mDimension != matrix2.mDimension) {
			throw new AssertionError("Some matrices for multiplication are not of the same dimension.");
		}
		final int n = matrix1.mDimension;
		TermMatrix product = constantZeroMatrix(script, n);
		for (int i=0; i<n; i++) {
			for (int k=0; k<n; k++) {
				Term[] summands = new Term[n];
				int current = 0;
				for (int j=0; j<n; j++) {
					Term factor1 = matrix1.mEntries[i][j];
					Term factor2 = matrix2.mEntries[j][k];
					Rational factor1Rational = Rational.ZERO;
					Rational factor2Rational = Rational.ZERO;
					if (isConstant(matrix1.mEntries[i][j])) {
						factor1Rational = getRationalValue(script, matrix1.mEntries[i][j]);
						if (factor1Rational.denominator().intValue() == 1 ||
								factor1Rational.numerator().intValue() == 0) {
							factor1 = script.numeral(factor1Rational.numerator());
						} else {
							factor1 = script.term("/", script.numeral(factor1Rational.numerator()),
									script.numeral(factor1Rational.denominator()));
						}
						if (factor1Rational.numerator().intValue() == 0) {
							continue;
						}
					}
					if (isConstant(matrix2.mEntries[j][k])) {
						factor2Rational = getRationalValue(script, matrix2.mEntries[j][k]);
						if (factor2Rational.denominator().intValue() == 1 ||
								factor2Rational.numerator().intValue() == 0) {
							factor2 = script.numeral(factor2Rational.numerator());
						} else {
							factor2 = script.term("/", script.numeral(factor2Rational.numerator()),
									script.numeral(factor2Rational.denominator()));
						}
						if (factor2Rational.numerator().intValue() == 0) {
							continue;
						}
					}
					if (factor1Rational.numerator().intValue() == 1 &&
							factor1Rational.denominator().intValue() == 1) {
						summands[current] = factor2;
						current = current + 1;
						continue;
					}
					if (factor2Rational.numerator().intValue() == 1 &&
							factor2Rational.denominator().intValue() == 1) {
						summands[current] = factor1;
						current = current + 1;
						continue;
					}
					summands[current] = script.term("*", factor1, factor2);
					if (isConstant(summands[current])) {
						Rational rationalSummand = getRationalValue(script, summands[current]);
						if (rationalSummand.numerator().intValue() == 0) {
							continue;
						}
						if (rationalSummand.denominator().intValue() == 1) {
							summands[current] = script.numeral(rationalSummand.numerator());
							current = current + 1;
							continue;
						} else {
							summands[current] = script.term("/", script.numeral(rationalSummand.numerator()),
									script.numeral(rationalSummand.denominator()));
							current = current + 1;
							continue;
						}
					}
					current = current + 1;
				}
				if (current == 0) {
					product.mEntries[i][k] = script.numeral(BigInteger.ZERO);
				} else if (current == 1) {
					product.mEntries[i][k] = summands[0];
				} else {
					product.mEntries[i][k] = script.term("+", Arrays.copyOfRange(summands,0,current));
					if (isConstant(product.mEntries[i][k])) {
						Rational productRational = getRationalValue(script, product.mEntries[i][k]);
						if (productRational.numerator().intValue() == 0 || productRational.denominator().intValue() == 1) {
							product.mEntries[i][k] = script.numeral(productRational.numerator());
						} else {
							product.mEntries[i][k] = script.term("/", script.numeral(productRational.numerator()),
									script.numeral(productRational.denominator()));
						}
					} else {
						// TODO: addition with all constant summands.
					}
				}
			}
		}
		return product;
	}
	
	/**
	 * Checks if a term represents a constant, that means, all leaves in the term tree are ConstantTerm.
	 * @param term
	 * @return
	 */
	public static boolean isConstant(Term term) {
		if (term instanceof ConstantTerm) {
			return true;
		} else if(term instanceof TermVariable) {
			return false;
		} else {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			Term[] param = appTerm.getParameters();
			boolean isConstant = true;
			for (int i=0; i<param.length; i++) {
				if (!isConstant(param[i])) {
					isConstant = false;
					break;
				}
			}
			return isConstant;
		}
	}
	
	/**
	 * Computes the rational value of a term, if the term represents a constant.
	 * @param script
	 * @param term
	 * @return
	 */
	public static Rational getRationalValue(Script script, Term term) {
		if (!isConstant(term)) {
			throw new AssertionError("Term is not constant.");
		}
		if (term instanceof ConstantTerm) {
			return (Rational) ((ConstantTerm) term).getValue();
		} else {
			ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().getName().equals("+")) {
				Rational sum = Rational.ZERO;
				for (int i=0; i<appTerm.getParameters().length; i++) {
					Rational summand = getRationalValue(script, appTerm.getParameters()[i]);
					sum = sum.add(summand);
				}
				return sum;
			} else if (appTerm.getFunction().getName().equals("*")) {
				Rational product = Rational.ONE;
				for (int i=0; i<appTerm.getParameters().length; i++) {
					Rational factor = getRationalValue(script, appTerm.getParameters()[i]);
					product = product.mul(factor);
				}
				return product;
			} else if (appTerm.getFunction().getName().equals("-")) {
				Rational difference = Rational.ZERO;
				for (int i=0; i<appTerm.getParameters().length; i++) {
					Rational subtr = getRationalValue(script, appTerm.getParameters()[i]);
					difference = difference.sub(subtr);
				}
				return difference;
			} else if (appTerm.getFunction().getName().equals("/")) {
				Rational quotient = Rational.ONE;
				for (int i=0; i<appTerm.getParameters().length; i++) {
					Rational denom = getRationalValue(script, appTerm.getParameters()[i]);
					quotient = quotient.div(denom);
				}
				return quotient;
			}
		}
		return Rational.ZERO;
	}
	
	public int getDimension() {
		return mDimension;
	}
	
	public Term getEntry(int i, int j) {
		return mEntries[i][j];
	}
}
