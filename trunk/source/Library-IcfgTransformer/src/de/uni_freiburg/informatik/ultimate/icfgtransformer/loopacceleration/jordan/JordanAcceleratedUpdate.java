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
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanLoopAcceleration.Iterations;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.QuadraticMatrix.JordanTransformationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Our Jordan-based loop acceleration works with closed forms of the variables
 * updates that are done in the loop. This class provides (static) methods that
 * construct these closed forms.
 *
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class JordanAcceleratedUpdate {

	private JordanAcceleratedUpdate() {
		// do not instantiate
	}

	/**
	 * Go through terms, get all variables and create a hash map varMatrixIndex with
	 * variables as key and corresponding matrix index as value to save which column
	 * corresponds to which variable and which row corresponds to which update.
	 */
	static HashMap<Term, Integer> determineMatrixIndices(final LinearUpdate linearUpdate) {
		final HashMap<Term, Integer> varMatrixIndex = new HashMap<>();
		int i = 0;
		// add all updated variables.
		for (final TermVariable updatedVar : linearUpdate.getUpdateMap().keySet()) {
			assert !varMatrixIndex.containsKey(updatedVar) : "cannot add same variable twice";
			varMatrixIndex.put(updatedVar, i);
			i++;
		}
		// add all variables that are only read in updates
		for (final Term var : linearUpdate.getReadonlyVariables()) {
			assert !varMatrixIndex.containsKey(var) : "cannot add same variable twice";
			varMatrixIndex.put(var, i);
			i++;
		}
		return varMatrixIndex;
	}

	/**
	 * Compute the update matrix out of the simultaneous update.
	 */
	static QuadraticMatrix computeUpdateMatrix(final LinearUpdate linearUpdate,
			final HashMap<Term, Integer> varMatrixIndexMap) {
		final int n = varMatrixIndexMap.size() + 1;
		// Initialize update matrix with identity matrix (every variable assigned to
		// itself).
		final QuadraticMatrix updateMatrix = QuadraticMatrix.constructIdentityMatrix(n);
		// Fill update matrix.
		for (final Entry<TermVariable, AffineTerm> update : linearUpdate.getUpdateMap().entrySet()) {
			fillMatrixRow(updateMatrix, varMatrixIndexMap, update.getValue(), update.getKey());
			for (int j = 0; j < n; j++) {
				if (updateMatrix.getEntry(varMatrixIndexMap.get(update.getKey()), j) == null) {
					return null;
				}
			}
		}
		return updateMatrix;
	}

	/**
	 * Fills the row corresponding to variable of the updateMatrix where variable is
	 * updated with polyRhs.
	 */
	private static void fillMatrixRow(final QuadraticMatrix updateMatrix,
			final HashMap<Term, Integer> varMatrixIndexMap, final AffineTerm affineRhs, final TermVariable tv) {

		final int n = updateMatrix.getDimension() - 1;
		updateMatrix.setEntry(n, n, BigInteger.valueOf(1));
		// Set diagonal entry to 0 for case variable assignment does not depend on
		// variable itself
		// (matrix was initialized as identity matrix).
		updateMatrix.setEntry(varMatrixIndexMap.get(tv), varMatrixIndexMap.get(tv), BigInteger.valueOf(0));

		// Fill row.
		for (final Term termVar : varMatrixIndexMap.keySet()) {
			updateMatrix.setEntry(varMatrixIndexMap.get(tv), varMatrixIndexMap.get(termVar),
					determineCoefficient(affineRhs, termVar));
			if (updateMatrix.getEntry(varMatrixIndexMap.get(tv), varMatrixIndexMap.get(termVar)) == null) {
				// not a linear term.
				break;
			}
			updateMatrix.setEntry(varMatrixIndexMap.get(tv), n, determineConstant(affineRhs));
		}
	}

	/**
	 * Determine the coefficient of termVar in the {@link AffineTerm} affineRhs.
	 */
	private static BigInteger determineCoefficient(final AffineTerm affineRhs, final Term termVar) {
		final Rational coefficient = affineRhs.getVariable2Coefficient().get(termVar);
		if (coefficient != null) {
			if (!coefficient.isIntegral()) {
				throw new AssertionError("Some coefficient is not integral.");
			}
			return coefficient.numerator();

		} else {
			return BigInteger.ZERO;
		}
	}

	/**
	 * Determine the constant term in the polynomial polyRhs.
	 */
	private static BigInteger determineConstant(final IPolynomialTerm polyRhs) {
		final Rational constant = polyRhs.getConstant();
		if (!constant.denominator().equals(BigInteger.valueOf(1))) {
			throw new AssertionError("Constant in some term is not integral.");
		}
		return constant.numerator();
	}

	/**
	 * @return true iff -1 is an eigenvalue or for eigenvalue 1 there is a Jordan
	 *         block of size greater than 2.
	 */
	static boolean isAlternatingClosedFormRequired(final JordanTransformationResult jordanUpdate) {
		final boolean minus1isEigenvalue = jordanUpdate.getJordanBlockSizes().containsKey(-1);
		final boolean ev1hasBlockGreater2 = hasEv1JordanBlockStrictlyGreater2(jordanUpdate);
		return (minus1isEigenvalue || ev1hasBlockGreater2);
	}

	/**
	 * @return true iff there is some Jordan block for eigenvalue 1 whose size is
	 *         strictly greater than 2
	 */
	private static boolean hasEv1JordanBlockStrictlyGreater2(final JordanTransformationResult jordanUpdate) {
		if (jordanUpdate.getJordanBlockSizes().containsKey(0)) {
			for (final int blockSize : jordanUpdate.getJordanBlockSizes().get(0).keySet()) {
				if (blockSize >= 2 && (jordanUpdate.getJordanBlockSizes().get(0).get(blockSize) != 0)) {
					throw new UnsupportedOperationException(
							"Need separate disjuncts for first iterations: " + blockSize);
				}
			}
		}
		boolean ev1hasBlockGreater2 = false;
		for (final int blockSize : jordanUpdate.getJordanBlockSizes().get(1).keySet()) {
			if (blockSize > 2 && (jordanUpdate.getJordanBlockSizes().get(1).get(blockSize) != 0)) {
				ev1hasBlockGreater2 = true;
			}
		}
		return ev1hasBlockGreater2;
	}

	static HashMap<TermVariable, Term> constructClosedForm(final ManagedScript mgdScript,
			final LinearUpdate linearUpdate, final HashMap<Term, Integer> varMatrixIndexMap,
			final JordanTransformationResult jordanUpdate, final TermVariable it, final TermVariable itHalf,
			final Iterations itKind) {
		// Compute matrix that represents closed form.
		final PolynomialTermMatrix closedFormMatrix = PolynomialTermMatrix.computeClosedFormMatrix(mgdScript,
				jordanUpdate, it, itHalf, itKind);
		final HashMap<TermVariable, Term> closedFormMap = constructClosedForm(mgdScript, closedFormMatrix, linearUpdate,
				varMatrixIndexMap);
		return closedFormMap;
	}

	private static HashMap<TermVariable, Term> constructClosedForm(final ManagedScript mgdScript,
			final PolynomialTermMatrix closedFormMatrix, final LinearUpdate linearUpdate,
			final HashMap<Term, Integer> var2MatrixIndex) {
		// Array to get TermVariable from matrix index.
		final Term[] matrixIndex2Var = new Term[var2MatrixIndex.size()];
		for (final Term var : var2MatrixIndex.keySet()) {
			matrixIndex2Var[var2MatrixIndex.get(var)] = var;
		}
		final HashMap<TermVariable, Term> closedForm = new HashMap<>();
		for (final TermVariable tv : linearUpdate.getUpdateMap().keySet()) {
			final Term sum = constructClosedForm(mgdScript, closedFormMatrix, var2MatrixIndex, matrixIndex2Var, tv);
			closedForm.put(tv, sum);
		}
		return closedForm;
	}

	private static Term constructClosedForm(final ManagedScript mgdScript, final PolynomialTermMatrix closedFormMatrix,
			final HashMap<Term, Integer> var2MatrixIndex, final Term[] matrixIndex2Var, final TermVariable tv) {
		final int varIndex = var2MatrixIndex.get(tv);
		final int n = closedFormMatrix.getDimension();
		final Term[] summands = new Term[n];
		int current = 0;
		for (int j = 0; j < n - 1; j++) {
			// Ignore if matrix entry is 0.
			if (closedFormMatrix.getEntry(varIndex, j).isConstant()) {
				final Rational entryRational = closedFormMatrix.getEntry(varIndex, j).getConstant();
				if (entryRational.numerator().intValue() == 0) {
					continue;
				}
			}
			// If matrix entry is 1, only add variable.
			if (closedFormMatrix.getEntry(varIndex, j).isConstant()) {
				final Rational entryRational = closedFormMatrix.getEntry(varIndex, j).getConstant();
				if (entryRational.numerator().intValue() == 1 && entryRational.denominator().intValue() == 1) {
					summands[current] = matrixIndex2Var[j];
				} else {
					summands[current] = mgdScript.getScript().term("*",
							closedFormMatrix.getEntry(varIndex, j).toTerm(mgdScript.getScript()), matrixIndex2Var[j]);
				}
			} else {
				summands[current] = mgdScript.getScript().term("*",
						closedFormMatrix.getEntry(varIndex, j).toTerm(mgdScript.getScript()), matrixIndex2Var[j]);
			}
			current = current + 1;
		}
		// Add constant term if it is not zero.
		if (closedFormMatrix.getEntry(varIndex, n - 1).isConstant()) {
			final Rational entryRational = closedFormMatrix.getEntry(varIndex, n - 1).getConstant();
			if (entryRational.numerator().intValue() != 0) {
				summands[current] = closedFormMatrix.getEntry(varIndex, n - 1).toTerm(mgdScript.getScript());
				current = current + 1;
			}
		} else {
			summands[current] = closedFormMatrix.getEntry(varIndex, n - 1).toTerm(mgdScript.getScript());
			current = current + 1;
		}
		Term sum = mgdScript.getScript().numeral(BigInteger.ZERO);
		if (current == 0) {
			sum = mgdScript.getScript().numeral(BigInteger.ZERO);
		} else if (current == 1) {
			sum = summands[0];
		} else {
			sum = mgdScript.getScript().term("+", Arrays.copyOfRange(summands, 0, current));
		}
		return sum;
	}

	/**
	 * The sum of the sizes of all block is the sum of the number of assigned scalar
	 * variables, the number of readonly variables and one (one is for the numbers
	 * that are added in the loop).
	 */
	static boolean isBlockSizeConsistent(final int numberOfAssignedVariables, final int numberOfReadonlyVariables,
			final JordanTransformationResult jordanUpdate) {
		int blockSizeSum = 0;
		for (final Triple<Integer, Integer, Integer> triple : jordanUpdate.getJordanBlockSizes().entrySet()) {
			blockSizeSum += triple.getSecond() * triple.getThird();
		}
		return (numberOfAssignedVariables + numberOfReadonlyVariables + 1 == blockSizeSum);
	}

	public static class LinearUpdate {
		Map<TermVariable, AffineTerm> mUpdateMap;
		Set<Term> mReadonlyVariables;

		public LinearUpdate(final Map<TermVariable, AffineTerm> updateMap, final Set<Term> readonlyVariables) {
			super();
			mUpdateMap = updateMap;
			mReadonlyVariables = readonlyVariables;
		}

		public Map<TermVariable, AffineTerm> getUpdateMap() {
			return mUpdateMap;
		}

		public Set<Term> getReadonlyVariables() {
			return mReadonlyVariables;
		}
	}
}
