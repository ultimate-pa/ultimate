/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 Miriam Herzig
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanDecomposition.JordanDecompositionStatus;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanLoopAcceleration.Iterations;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * This class represents a linear update by a list of Jordan decompositions.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class JordanUpdate {

	private final List<JordanUpdatePart> mParts;
	private final JordanDecomposition.JordanDecompositionStatus mJordanDecompositionStatus;
	private final NestedMap2<Integer, Integer, Integer> mJordanBlockSizes;

	public JordanUpdate(final JordanDecompositionStatus jordanDecompositionStatus, final List<JordanUpdatePart> parts) {
		super();
		mJordanDecompositionStatus = jordanDecompositionStatus;
		mParts = parts;
		if (jordanDecompositionStatus == JordanDecompositionStatus.UNSUPPORTED_EIGENVALUES) {
			mJordanBlockSizes = null;
		} else {
			mJordanBlockSizes = new NestedMap2<>();
			for (final JordanUpdatePart part : parts) {
				addJordanCodeBlockSizes(mJordanBlockSizes, part.getJordanDecomp().getJordanBlockSizes());
			}
		}
	}

	public static JordanUpdate fromLinearUpdate(final LinearUpdate linearUpdate) {
		final List<LinearUpdate> lineareUpdates = linearUpdate.partition();
		final List<JordanUpdatePart> parts = new ArrayList<>();
		for (final LinearUpdate linearUpdatePart : lineareUpdates) {
			// HashMap to get matrix index from TermVariable.
			final Map<Term, Integer> varMatrixIndexMap = determineMatrixIndices(linearUpdatePart);
			final QuadraticMatrix updateMatrix = computeUpdateMatrix(linearUpdatePart, varMatrixIndexMap);
			final JordanDecomposition jordanDecomp = updateMatrix.constructJordanDecomposition();
			if (jordanDecomp.getStatus() == JordanDecompositionStatus.UNSUPPORTED_EIGENVALUES) {
				return new JordanUpdate(jordanDecomp.getStatus(), null);
			}
			parts.add(new JordanUpdatePart(linearUpdatePart, varMatrixIndexMap, jordanDecomp));
		}
		return new JordanUpdate(JordanDecompositionStatus.SUCCESS, parts);
	}

	public JordanDecompositionStatus getStatus() {
		return mJordanDecompositionStatus;
	}

	public NestedMap2<Integer, Integer, Integer> getJordanBlockSizes() {
		return mJordanBlockSizes;
	}

	/**
	 * Go through terms, get all variables and create a hash map varMatrixIndex with
	 * variables as key and corresponding matrix index as value to save which column
	 * corresponds to which variable and which row corresponds to which update.
	 */
	private static HashMap<Term, Integer> determineMatrixIndices(final LinearUpdate linearUpdate) {
		final HashMap<Term, Integer> varMatrixIndex = new HashMap<>();
		int i = 0;
		// add all updated variables.
		for (final TermVariable updatedVar : linearUpdate.getUpdateMap().keySet()) {
			assert !varMatrixIndex.containsKey(updatedVar) : "cannot add same variable twice";
			varMatrixIndex.put(updatedVar, i);
			i++;
		}
		// add all variables that are only read in updates
		for (final Term raVar : linearUpdate.getReadonlyVariables()) {
			assert !varMatrixIndex.containsKey(raVar) : "cannot add same variable twice";
			varMatrixIndex.put(raVar, i);
			i++;
		}
		return varMatrixIndex;
	}

	/**
	 * Compute the update matrix out of the simultaneous update.
	 */
	private static QuadraticMatrix computeUpdateMatrix(final LinearUpdate linearUpdate,
			final Map<Term, Integer> varMatrixIndexMap) {
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
			final Map<Term, Integer> varMatrixIndexMap, final AffineTerm affineRhs, final TermVariable tv) {

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
	private static IPolynomialTerm constructIterationCounter(final Script script, final Iterations itKind,
			final TermVariable it, final TermVariable itHalf) {
		final Sort sort = SmtSortUtils.getIntSort(script);
		final IPolynomialTerm result;
		switch (itKind) {
		case ALL:
			result = AffineTerm.constructVariable(it);
			break;
		case EVEN:
			result = PolynomialTerm.mulPolynomials(AffineTerm.constructConstant(sort, Rational.TWO),
					AffineTerm.constructVariable(itHalf));
			break;
		case ODD:
			result = PolynomialTerm.sum(PolynomialTerm.mulPolynomials(AffineTerm.constructConstant(sort, Rational.TWO),
					AffineTerm.constructVariable(itHalf)), AffineTerm.constructConstant(sort, Rational.ONE));
			break;
		default:
			throw new AssertionError("unknown value: " + itKind);
		}
		return result;
	}

	/**
	 * Construct map that assigns to the default TermVariable its closed from, where each
	 * variable in the closed form is represented by its default TermVariable.
	 */
	public Map<TermVariable, Term> constructClosedForm(final ManagedScript mgdScript, final TermVariable it,
			final TermVariable itHalf, final Iterations itKind) {
		final IPolynomialTerm itc = constructIterationCounter(mgdScript.getScript(), itKind, it, itHalf);
		return constructClosedForm(mgdScript, itc, itKind);
	}

	private Map<TermVariable, Term> constructClosedForm(final ManagedScript mgdScript, final IPolynomialTerm itc,
			final Iterations itKind) {
		final Map<TermVariable, Term> closedFormMap = new HashMap<>();
		for (final JordanUpdatePart part : mParts) {
			// Compute matrix that represents closed form.
			final PolynomialTermMatrix closedFormMatrix = PolynomialTermMatrix.computeClosedFormMatrix(mgdScript,
					part.getJordanDecomp(), itc, itKind);
			final Map<TermVariable, Term> closedFormPart = constructClosedForm(mgdScript, closedFormMatrix,
					part.getLinearUpdate(), part.getVarMatrixIndexMap());
			closedFormMap.putAll(closedFormPart);
		}
		return closedFormMap;
	}

	/**
	 * Construct map that assigns to the default TermVariable its closed from, where
	 * each variable in the closed form is represented by its default TermVariable.
	 */
	public Map<TermVariable, Term> constructClosedForm(final ManagedScript mgdScript, final int k) {
		final Map<TermVariable, Term> closedFormMap = new HashMap<>();
		for (final JordanUpdatePart part : mParts) {
			// Compute matrix that represents closed form.
			final PolynomialTermMatrix closedFormMatrix = PolynomialTermMatrix.computeClosedFormMatrix(mgdScript,
					part.getJordanDecomp(), k);
			final Map<TermVariable, Term> closedFormPart = constructClosedForm(mgdScript, closedFormMatrix,
					part.getLinearUpdate(), part.getVarMatrixIndexMap());
			closedFormMap.putAll(closedFormPart);
		}
		return closedFormMap;
	}

	private Map<TermVariable, Term> constructClosedForm(final ManagedScript mgdScript,
			final PolynomialTermMatrix closedFormMatrix, final LinearUpdate linearUpdate,
			final Map<Term, Integer> var2MatrixIndex) {
		// Array to get TermVariable from matrix index.
		final Term[] matrixIndex2Var = new Term[var2MatrixIndex.size()];
		for (final Term var : var2MatrixIndex.keySet()) {
			matrixIndex2Var[var2MatrixIndex.get(var)] = var;
		}
		final Map<TermVariable, Term> closedForm = new HashMap<>();
		for (final TermVariable tv : linearUpdate.getUpdateMap().keySet()) {
			final Term sum = constructClosedForm(mgdScript, closedFormMatrix, var2MatrixIndex, matrixIndex2Var, tv);
			closedForm.put(tv, sum);
		}
		return closedForm;
	}

	private static Term constructClosedForm(final ManagedScript mgdScript, final PolynomialTermMatrix closedFormMatrix,
			final Map<Term, Integer> var2MatrixIndex, final Term[] matrixIndex2Var, final TermVariable tv) {
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
		final Term sum;
		if (current == 0) {
			sum = mgdScript.getScript().numeral(BigInteger.ZERO);
		} else if (current == 1) {
			sum = summands[0];
		} else {
			sum = mgdScript.getScript().term("+", Arrays.copyOfRange(summands, 0, current));
		}
		return sum;
	}

	private static void addJordanCodeBlockSizes(final NestedMap2<Integer, Integer, Integer> sizes, final NestedMap2<Integer, Integer, Integer> addedSizes) {
		for (final Triple<Integer, Integer, Integer> triple : addedSizes.entrySet()) {
			final Integer amount = sizes.get(triple.getFirst(), triple.getSecond());
			if (amount == null) {
				sizes.put(triple.getFirst(), triple.getSecond(), triple.getThird());
			} else {
				sizes.put(triple.getFirst(), triple.getSecond(), amount + triple.getThird());
			}
		}
	}


	/**
	 * @return true iff -1 is an eigenvalue or for eigenvalue 1 there is a Jordan
	 *         block of size greater than 2.
	 */
	public boolean isAlternatingClosedFormRequired() {
		final boolean minus1isEigenvalue = mJordanBlockSizes.containsKey(-1);
		final boolean ev1hasBlockGreater2 = hasEv1JordanBlockStrictlyGreater2();
		return (minus1isEigenvalue || ev1hasBlockGreater2);
	}

	/**
	 * @return true iff there is some Jordan block for eigenvalue 1 whose size is
	 *         strictly greater than 2
	 */
	public boolean hasEv1JordanBlockStrictlyGreater2() {
		if (!mJordanBlockSizes.containsKey(1)) {
			return false;
		}
		boolean ev1hasBlockGreater2 = false;
		for (final int blockSize : mJordanBlockSizes.get(1).keySet()) {
			if (blockSize > 2 && (mJordanBlockSizes.get(1).get(blockSize) != 0)) {
				ev1hasBlockGreater2 = true;
			}
		}
		return ev1hasBlockGreater2;
	}

	public int computeSizeOfLargestEv0Block() {
		if (!mJordanBlockSizes.containsKey(0)) {
			return 0;
		} else {
			int max = 0;
			for (final int blockSize : mJordanBlockSizes.get(0).keySet()) {
				if (blockSize > max) {
					max = blockSize;
				}
			}
			assert max > 0;
			return max;
		}
	}

	/**
	 * The sum of the sizes of all block is the sum of the number of assigned scalar
	 * variables, the number of readonly variables and one (one is for the numbers
	 * that are added in the loop).
	 */
	public boolean isBlockSizeConsistent(final int numberOfAssignedVariables, final int numberOfReadonlyVariables) {
		int blockSizeSum = 0;
		for (final Triple<Integer, Integer, Integer> triple : mJordanBlockSizes.entrySet()) {
			blockSizeSum += triple.getSecond() * triple.getThird();
		}
		return (numberOfAssignedVariables + numberOfReadonlyVariables + mParts.size() == blockSizeSum);
	}

	private static class JordanUpdatePart {
		private final LinearUpdate mLinearUpdate;
		private final Map<Term, Integer> mVarMatrixIndexMap;
		private final JordanDecomposition mJordanDecomp;
		public JordanUpdatePart(final LinearUpdate linearUpdate, final Map<Term, Integer> varMatrixIndexMap,
				final JordanDecomposition jordanDecomp) {
			super();
			mLinearUpdate = linearUpdate;
			mVarMatrixIndexMap = varMatrixIndexMap;
			mJordanDecomp = jordanDecomp;
		}
		public LinearUpdate getLinearUpdate() {
			return mLinearUpdate;
		}
		public Map<Term, Integer> getVarMatrixIndexMap() {
			return mVarMatrixIndexMap;
		}
		public JordanDecomposition getJordanDecomp() {
			return mJordanDecomp;
		}
	}
}