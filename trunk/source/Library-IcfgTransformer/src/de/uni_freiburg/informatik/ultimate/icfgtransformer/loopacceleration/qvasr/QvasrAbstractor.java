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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * This class is used to compute a {@link QvasrAbstraction} for a given {@link Term} by solving various sets of linear
 * equation systems.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 */
public class QvasrAbstractor {

	/**
	 *
	 * Define which kind of base matrix. Resets: Where the outvars only depend on the invars and addition vector a.
	 * Additions: Where outvars depend on invars and addition vector a.
	 *
	 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
	 */
	private enum BaseType {
		RESETS, ADDITIONS
	}

	/**
	 * Computes a Q-Vasr-abstraction (S, V), with linear simulation matrix S and Q-Vasr V. A transition formula can be
	 * overapproximated using a Q-Vasr-abstraction.
	 */
	public QvasrAbstractor() {
		// Prevent instantiation of this utility class
	}

	/**
	 * Compute a Q-Vasr-abstraction for a given transition formula.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 *
	 * @param transitionFormula
	 *            A transition formula from which an overapproximative qvasr-abstraction is computed.
	 * @return A {@link QvasrAbstraction} that overapproximates the changes to variables of the transition formula.
	 */
	public static QvasrAbstraction computeAbstraction(final IUltimateServiceProvider services, final ManagedScript script,
			final UnmodifiableTransFormula transitionFormula) {
		if (!SmtUtils.isArrayFree(transitionFormula.getFormula())
				|| !SmtUtils.containsArrayVariables(transitionFormula.getFormula())) {
			throw new UnsupportedOperationException("Cannot deal with arrays.");
		}
		final Map<TermVariable, Term> updatesInFormulaAdditions =
				getUpdates(services, script, transitionFormula, BaseType.ADDITIONS);
		final Map<TermVariable, Term> updatesInFormulaResets = getUpdates(services, script, transitionFormula,
				BaseType.RESETS);
		final Term[][] newUpdatesMatrixResets = constructBaseMatrix(script, updatesInFormulaResets, transitionFormula);
		final Term[][] newUpdatesMatrixAdditions =
				constructBaseMatrix(script, updatesInFormulaAdditions, transitionFormula);
		final Term[][] solutionsAdditionsGaussJordan = gaussianSolve(script, newUpdatesMatrixAdditions);
		final Term[][] solutionsResetGaussJordan = gaussianSolve(script, newUpdatesMatrixResets);

		final Rational[][] resetVectorSpaceBasis =
				QvasrVectorSpaceBasisConstructor.computeVectorSpaceBasis(script, solutionsResetGaussJordan);
		final Rational[][] additionVectorSpaceBasis =
				QvasrVectorSpaceBasisConstructor.computeVectorSpaceBasis(script, solutionsAdditionsGaussJordan);
		return QvasrAbstractionBuilder.constructQvasrAbstraction(resetVectorSpaceBasis, additionVectorSpaceBasis);
	}

	/**
	 * Solve a given matrix, containing logical Terms such as {@link TermVariable}, using Gauss-Jordan Elimination.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 *
	 * @param matrix
	 *            A matrix representing changes to variables. Can contain logical terms.
	 * @return The solved matrix in reduced echelon form.
	 */
	public static Term[][] gaussianSolve(final ManagedScript script, final Term[][] matrix) {
		final Term[][] gaussPartialPivot = gaussPartialPivot(script, matrix);
		Term[][] gaussedAdditionsPruned = removeZeroRows(script, gaussPartialPivot);
		gaussedAdditionsPruned = removeDuplicateRows(script, gaussedAdditionsPruned);
		gaussedAdditionsPruned = gaussRowEchelonFormJordan(script, gaussedAdditionsPruned);
		gaussedAdditionsPruned = removeZeroRows(script, gaussedAdditionsPruned);
		return gaussedAdditionsPruned;
	}

	/**
	 * Bring a given matrix, containing logical terms, into upper triangle form using the gaussian partial pivot method.
	 *
	 * @param matrix
	 *            A matrix in non-upper triangle form.
	 * @return A matrix in upper-triangle form
	 */
	private static Term[][] gaussPartialPivot(final ManagedScript script, Term[][] matrix) {
		for (int k = 0; k < matrix.length - 1; k++) {
			int max = -1;
			if ((k + 1) < matrix.length && (k + 1) < matrix[0].length) {
				max = findPivot(script, matrix, k);
			}
			if (max == -1) {
				return matrix;
			}
			if (max != 0) {
				matrix = swap(matrix, k, max);
			}
			final Term pivot = matrix[k][k];
			// i is the row
			for (int i = k + 1; i < matrix.length; i++) {
				final Term toBeEliminated = matrix[i][k];
				matrix[i][k] = script.getScript().decimal("0");
				final Term newDiv = QvasrAbstractor.simplifyRealDivision(script, toBeEliminated, pivot);

				// k is the column
				for (int j = k + 1; j < matrix[0].length; j++) {
					final Term currentColumn = matrix[k][j];
					final Term currentEntry = matrix[i][j];
					final Term newMul = QvasrAbstractor.simplifyRealMultiplication(script, newDiv, currentColumn);
					final Term newSub = QvasrAbstractor.simplifyRealSubtraction(script, currentEntry, newMul);
					matrix[i][j] = newSub;
				}
			}
		}
		return matrix;
	}

	/**
	 * Convert a matrix in upper triangular form into row echelon form -> only leading 1s using Standard Real Division.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 *
	 * @param matrix
	 *            A matrix in upper triangle form.
	 * @return A matrix in row echelon form.
	 *
	 */
	private static Term[][] gaussRowEchelonFormJordan(final ManagedScript script, final Term[][] matrix) {
		for (int i = matrix.length - 1; 0 <= i; i--) {
			for (int j = 0; j < matrix[0].length; j++) {
				if (!QvasrUtils.checkTermEquiv(script, matrix[i][j], script.getScript().decimal("0"))) {
					final Term dividerInverse = getDivisionInverse(script, matrix[i][j]);
					for (int k = j; k < matrix[0].length; k++) {
						final Term toBeDivided = matrix[i][k];
						final Term mult =
								QvasrAbstractor.simplifyRealMultiplication(script, toBeDivided, dividerInverse);
						matrix[i][k] = mult;
					}
					for (int l = i - 1; l >= 0; l--) {
						final Term toBeEliminatedMult = matrix[l][j];
						for (int m = j; m < matrix[0].length; m++) {
							final Term rowEntry = matrix[i][m];
							final Term rowEntryToBeEliminated = matrix[l][m];
							final Term multRow =
									QvasrAbstractor.simplifyRealMultiplication(script, toBeEliminatedMult, rowEntry);
							final Term subRow =
									QvasrAbstractor.simplifyRealSubtraction(script, rowEntryToBeEliminated, multRow);
							matrix[l][m] = subRow;
						}
					}
					break;
				}
			}
		}
		return matrix;
	}

	/**
	 * Convert a real division into its inverse, for example, 2/x -> x/2
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 * @param term
	 *            A real division.
	 * @return The inverse of the division.
	 */
	public static Term getDivisionInverse(final ManagedScript script, final Term term) {
		Term result;
		if (QvasrUtils.isApplicationTerm(term) && ("/".equals(((ApplicationTerm) term).getFunction().getName()))) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final Term dividend = appTerm.getParameters()[0];
			final Term divisor = appTerm.getParameters()[1];
			result = SmtUtils.divReal(script.getScript(), divisor, dividend);
		} else {
			result = SmtUtils.divReal(script.getScript(), script.getScript().decimal("1"), term);
		}
		return result;
	}

	/**
	 * Remove rows with all 0s from a given matrix.
	 *
	 * @param matrix
	 *            A matrix containing rows with only 0s.
	 * @return A matrix with only non-zero rows.
	 */
	private static Term[][] removeZeroRows(final ManagedScript script, final Term[][] matrix) {
		final Set<Integer> toBeEliminated = new HashSet<>();
		for (int i = 0; i < matrix.length; i++) {
			for (int j = 0; j < matrix[0].length; j++) {
				if (!QvasrUtils.checkTermEquiv(script, matrix[i][j], script.getScript().decimal("0"))) {
					break;
				}
				if (j == matrix[0].length - 1) {
					toBeEliminated.add(i);
				}
			}
		}
		final int prunedLength = matrix.length - toBeEliminated.size();
		if (prunedLength > 0) {
			final Term[][] prunedMatrix = new Term[prunedLength][matrix[0].length];
			int cnt = 0;
			for (int k = 0; k < matrix.length; k++) {
				if (!toBeEliminated.contains(k)) {
					for (int l = 0; l < matrix[0].length; l++) {
						prunedMatrix[cnt][l] = matrix[k][l];
					}
					cnt++;
				}
			}
			return prunedMatrix;
		} else {
			return matrix;
		}

	}

	/**
	 * Remove rows from a matrix that are identical.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 *
	 * @param matrix
	 *            with duplicate rows.
	 * @return A matrix with only distinct rows.
	 */
	private static Term[][] removeDuplicateRows(final ManagedScript script, final Term[][] matrix) {
		final Set<Integer> toBeEliminated = new HashSet<>();
		for (int i = 0; i < matrix.length; i++) {
			final Set<Integer> possibleDuplicates = new HashSet<>();
			for (int j = i + 1; j < matrix.length; j++) {
				if (QvasrUtils.checkTermEquiv(script, matrix[i][0], matrix[j][0])) {
					possibleDuplicates.add(j);
				}
				final Set<Integer> trueDuplicates = new HashSet<>(possibleDuplicates);
				for (final Integer k : possibleDuplicates) {
					for (int l = 0; l < matrix[0].length; l++) {
						if (!QvasrUtils.checkTermEquiv(script, matrix[k][l], matrix[i][l])) {
							trueDuplicates.remove(k);
						}
					}
				}
				for (final Integer m : trueDuplicates) {
					toBeEliminated.add(m);
				}
			}
		}
		final int prunedLength = matrix.length - toBeEliminated.size();
		if (prunedLength > 0) {
			final Term[][] prunedMatrix = new Term[prunedLength][matrix[0].length];
			int cnt = 0;
			for (int k = 0; k < matrix.length; k++) {
				if (!toBeEliminated.contains(k)) {
					for (int l = 0; l < matrix[0].length; l++) {
						prunedMatrix[cnt][l] = matrix[k][l];
					}
					cnt++;
				}
			}
			return prunedMatrix;
		} else {
			return matrix;

		}

	}

	/**
	 * Factors out coefficients from sums.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 * @param sum
	 *            A term representing a sum of summands.
	 * @return A term where summands has been factored out.
	 */
	private static Term factorOutRealSum(final ManagedScript script, final Term sum) {
		if (QvasrUtils.isApplicationTerm(sum)) {
			final ApplicationTerm sumAppTerm = (ApplicationTerm) sum;
			final List<Term> summands = getApplicationTermSumParams(sumAppTerm);
			final List<Term> simplifiedSummands = new ArrayList<>();

			for (final Term summandOne : summands) {
				if (QvasrUtils.isApplicationTerm(summandOne)
						&& ("+".equals(((ApplicationTerm) summandOne).getFunction().getName()))) {
					final List<Term> factors = getApplicationTermMultiplicationParams(script, summandOne);
					final Term occurencesMult = script.getScript()
							.decimal(Integer.toString(Collections.frequency(factors, summandOne)) + 1);
					int occurences = 1;
					Term factorToBeFactored = summandOne;
					Term factorNotToBeFactored = summandOne;
					for (final Term factor : factors) {
						factorToBeFactored = factor;
						if (occurences > 1) {
							continue;
						}
						occurences = Collections.frequency(summands, factor) + 1;
						factorNotToBeFactored = factor;
					}
					final Term summandOneSimplified = SmtUtils.mul(script.getScript(), "*", occurencesMult,
							factorNotToBeFactored, SmtUtils.sum(script.getScript(), "+",
									script.getScript().decimal(Integer.toString(occurences)), factorToBeFactored));
					simplifiedSummands.add(summandOneSimplified);
				}
			}
			return SmtUtils.sum(script.getScript(), "+",
					simplifiedSummands.toArray(new Term[simplifiedSummands.size()]));
		}
		return sum;
	}

	/**
	 * Expand a multiplication of two factors. For example (x + 1) * (y + 4) -> xy + 4x + y + 4. The order of the
	 * factors does not matter, the Associative property holds.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 *
	 * @param factorOne
	 *            The first factor in the multiplication.
	 * @param factorTwo
	 *            The second factor in the multiplication.
	 * @return An out factored multiplication.
	 */
	public static Term expandRealMultiplication(final ManagedScript script, final Term factorOne,
			final Term factorTwo) {
		final List<Term> factorOneVars = new ArrayList<>();
		final List<Term> factorTwoVars = new ArrayList<>();
		if (QvasrUtils.isApplicationTerm(factorOne) && QvasrUtils.isApplicationTerm(factorTwo)) {
			final ApplicationTerm factorOneAppTerm = (ApplicationTerm) factorOne;
			final ApplicationTerm factorTwoAppTerm = (ApplicationTerm) factorTwo;
			if ("+".equals(factorOneAppTerm.getFunction().getName())) {
				for (final Term param : factorOneAppTerm.getParameters()) {
					if (QvasrUtils.isApplicationTerm(param)) {
						factorOneVars.addAll(getApplicationTermSumParams((ApplicationTerm) param));
					} else {
						factorOneVars.add(param);
					}
				}
			} else {
				factorOneVars.add(factorOneAppTerm);
			}
			if ("+".equals(factorTwoAppTerm.getFunction().getName())) {
				for (final Term param : factorTwoAppTerm.getParameters()) {
					if (QvasrUtils.isApplicationTerm(param)) {
						factorTwoVars.addAll(getApplicationTermSumParams((ApplicationTerm) param));
					} else {
						factorTwoVars.add(param);
					}
				}
			} else {
				factorTwoVars.add(factorTwoAppTerm);
			}

		}

		if (!(QvasrUtils.isApplicationTerm(factorOne)) && QvasrUtils.isApplicationTerm(factorTwo)) {
			final ApplicationTerm factorTwoAppTerm = (ApplicationTerm) factorTwo;
			factorOneVars.add(factorOne);
			if ("+".equals(factorTwoAppTerm.getFunction().getName())) {
				for (final Term param : factorTwoAppTerm.getParameters()) {
					if (QvasrUtils.isApplicationTerm(param)) {
						factorTwoVars.addAll(getApplicationTermSumParams((ApplicationTerm) param));
					} else {
						factorTwoVars.add(param);
					}
				}
			} else {
				factorTwoVars.add(factorTwoAppTerm);
			}
		}

		if (QvasrUtils.isApplicationTerm(factorOne) && !(QvasrUtils.isApplicationTerm(factorTwo))) {
			final ApplicationTerm factorOneAppTerm = (ApplicationTerm) factorOne;
			factorTwoVars.add(factorTwo);
			if ("+".equals(factorOneAppTerm.getFunction().getName())) {
				for (final Term param : factorOneAppTerm.getParameters()) {
					if (QvasrUtils.isApplicationTerm(param)) {
						factorOneVars.addAll(getApplicationTermSumParams((ApplicationTerm) param));
					} else {
						factorOneVars.add(param);
					}
				}
			} else {
				factorOneVars.add(factorOneAppTerm);
			}
		}

		if (!(QvasrUtils.isApplicationTerm(factorOne)) && !(QvasrUtils.isApplicationTerm(factorTwo))) {
			factorOneVars.add(factorOne);
			factorTwoVars.add(factorTwo);
		}

		Term result = script.getScript().decimal("0");
		for (final Term factorOneParam : factorOneVars) {
			for (final Term factorTwoParam : factorTwoVars) {
				final Term mult = SmtUtils.mul(script.getScript(), "*", factorOneParam, factorTwoParam);
				result = SmtUtils.sum(script.getScript(), "+", result, mult);
			}
		}
		return result;
	}

	/**
	 * Expand a multiplication of two or more factors.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 *
	 * @param factors
	 *            A list of factors, for multiplications containing more than two factors.
	 *
	 * @return An out factored multiplication.
	 */
	public static Term expandRealMultiplication(final ManagedScript script, final List<Term> factors) {
		if (factors.size() < 2) {
			return factors.get(0);
		}
		Term result = script.getScript().decimal("0");
		final Deque<Term> factorStack = new ArrayDeque<>(factors);
		while (!factorStack.isEmpty()) {
			final Term factorOne = factorStack.pop();
			for (final Term factorTwo : factorStack) {
				if (QvasrUtils.isApplicationTerm(factorOne)) {
					final ApplicationTerm factorOneAppTerm = (ApplicationTerm) factorOne;
					if (QvasrUtils.isApplicationTerm(factorTwo)) {
						final ApplicationTerm factorTwoAppTerm = (ApplicationTerm) factorTwo;
						for (final Term paramFactorOne : factorOneAppTerm.getParameters()) {
							for (final Term paramFactorTwo : factorTwoAppTerm.getParameters()) {
								final Term mult = SmtUtils.mul(script.getScript(), "*", paramFactorOne, paramFactorTwo);
								result = SmtUtils.sum(script.getScript(), "+", result, mult);
							}
						}
					} else {
						for (final Term paramFactorOne : factorOneAppTerm.getParameters()) {
							final Term mult = SmtUtils.mul(script.getScript(), "*", paramFactorOne, factorTwo);
							result = SmtUtils.sum(script.getScript(), "+", result, mult);
						}
					}
				} else if (QvasrUtils.isApplicationTerm(factorTwo)) {
					final ApplicationTerm factorTwoAppTerm = (ApplicationTerm) factorTwo;
					for (final Term paramFactorTwo : factorTwoAppTerm.getParameters()) {
						final Term mult = SmtUtils.mul(script.getScript(), "*", paramFactorTwo, factorOne);
						result = SmtUtils.sum(script.getScript(), "+", result, mult);
					}
				} else {
					final Term mult = SmtUtils.mul(script.getScript(), "*", factorOne, factorTwo);
					result = SmtUtils.sum(script.getScript(), "+", result, mult);
				}
			}
		}
		return result;
	}

	/**
	 * Simplify a division of reals formed by paramters dividend and divisor. For example x/2x -> 1/2
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 *
	 * @param dividend
	 *            The dividend of the division.
	 * @param divisor
	 *            The divisor of the division.
	 * @return A simplied division of dividend/divisor.
	 */
	public static Term simplifyRealDivision(final ManagedScript script, final Term dividend, final Term divisor) {
		final Term zero = script.getScript().decimal("0");

		/*
		 * Can be represented by AffineTerm -> less expensive
		 */
		if (QvasrUtils.checkTermEquiv(script, divisor, zero)) {
			throw new UnsupportedOperationException("cannot divide by 0!");
		}
		if (QvasrUtils.checkTermEquiv(script, divisor, script.getScript().decimal("1"))) {
			return dividend;
		}
		if (QvasrUtils.checkTermEquiv(script, dividend, zero)) {
			return zero;
		}

		final Term one = script.getScript().decimal("1");
		if (QvasrUtils.checkTermEquiv(script, dividend, divisor)) {
			return one;
		}

		Term result = SmtUtils.divReal(script.getScript(), dividend, divisor);
		if (QvasrUtils.isApplicationTerm(dividend) && QvasrUtils.isApplicationTerm(divisor)) {
			final ApplicationTerm dividendAppTerm = (ApplicationTerm) dividend;
			final ApplicationTerm divisorAppTerm = (ApplicationTerm) divisor;
			Term dividendDividend;
			Term dividendDivisor = one;
			Term divisorDividend;
			Term divisorDivisor = one;
			if ("/".equals(dividendAppTerm.getFunction().getName())) {
				dividendDividend = dividendAppTerm.getParameters()[0];
				dividendDivisor = dividendAppTerm.getParameters()[1];
			} else {
				dividendDividend = dividendAppTerm;
			}
			if ("/".equals(divisorAppTerm.getFunction().getName())) {
				divisorDividend = divisorAppTerm.getParameters()[0];
				divisorDivisor = divisorAppTerm.getParameters()[1];
			} else {
				divisorDividend = divisorAppTerm;
			}
			if ("/".equals(divisorAppTerm.getFunction().getName())
					|| "/".equals(dividendAppTerm.getFunction().getName())) {
				final Term commonDividend = SmtUtils.mul(script.getScript(), "*", dividendDividend, divisorDivisor);
				final Term commonDivisor = SmtUtils.mul(script.getScript(), "*", dividendDivisor, divisorDividend);
				final Pair<Term, Term> resultReduced =
						QvasrAbstractor.reduceRealDivision(script, commonDividend, commonDivisor);
				result = SmtUtils.divReal(script.getScript(), resultReduced.getFirst(), resultReduced.getSecond());
			}

			if (!("/".equals(divisorAppTerm.getFunction().getName()))
					&& !("/".equals(dividendAppTerm.getFunction().getName()))) {
				final Pair<Term, Term> resultReduced = QvasrAbstractor.reduceRealDivision(script, dividend, divisor);
				result = SmtUtils.divReal(script.getScript(), resultReduced.getFirst(), resultReduced.getSecond());
			}
		}

		if (QvasrUtils.isApplicationTerm(dividend) && !(QvasrUtils.isApplicationTerm(divisor))) {
			final ApplicationTerm dividendAppTerm = (ApplicationTerm) dividend;
			Pair<Term, Term> resultReduced;
			if ("/".equals(dividendAppTerm.getFunction().getName())) {
				final Term dividendDividend = dividendAppTerm.getParameters()[0];
				final Term dividendDivisor = dividendAppTerm.getParameters()[1];
				final Term commonDivisor = SmtUtils.mul(script.getScript(), "*", dividendDivisor, divisor);
				resultReduced = QvasrAbstractor.reduceRealDivision(script, dividendDividend, commonDivisor);
				result = SmtUtils.divReal(script.getScript(), resultReduced.getFirst(), resultReduced.getSecond());
			} else {
				resultReduced = QvasrAbstractor.reduceRealDivision(script, dividend, divisor);
				result = SmtUtils.divReal(script.getScript(), resultReduced.getFirst(), resultReduced.getSecond());
			}
		}

		if (!(QvasrUtils.isApplicationTerm(dividend)) && QvasrUtils.isApplicationTerm(divisor)) {
			final ApplicationTerm divisorAppTerm = (ApplicationTerm) divisor;
			Pair<Term, Term> resultReduced;
			if ("/".equals(divisorAppTerm.getFunction().getName())) {
				final Term divisorDividend = divisorAppTerm.getParameters()[0];
				final Term divisorDivisor = divisorAppTerm.getParameters()[1];
				final Term commonDividend = SmtUtils.mul(script.getScript(), "*", dividend, divisorDivisor);
				resultReduced = QvasrAbstractor.reduceRealDivision(script, commonDividend, divisorDividend);
				result = SmtUtils.divReal(script.getScript(), resultReduced.getFirst(), resultReduced.getSecond());
			} else {
				resultReduced = QvasrAbstractor.reduceRealDivision(script, dividend, divisor);
				result = SmtUtils.divReal(script.getScript(), resultReduced.getFirst(), resultReduced.getSecond());
			}
		}

		if (!(QvasrUtils.isApplicationTerm(dividend)) && !(QvasrUtils.isApplicationTerm(divisor))) {
			final Pair<Term, Term> resultReduced = QvasrAbstractor.reduceRealDivision(script, dividend, divisor);
			result = SmtUtils.divReal(script.getScript(), resultReduced.getFirst(), resultReduced.getSecond());
		}
		return result;
	}

	/**
	 * Simplify a multiplication between two reals factorOne * factorTwo. Useful for divisions. For example x * 1/x -> 1
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 * @param factorOne
	 *            First factor of the multiplication.
	 * @param factorTwo
	 *            Second factor of the multiplication.
	 * @return A simplified real multiplication.
	 */
	public static Term simplifyRealMultiplication(final ManagedScript script, final Term factorOne,
			final Term factorTwo) {
		final Term zero = script.getScript().decimal("0");
		if (QvasrUtils.checkTermEquiv(script, factorOne, zero) || QvasrUtils.checkTermEquiv(script, factorTwo, zero)) {
			return zero;
		}
		final Term one = script.getScript().decimal("1");
		if (QvasrUtils.checkTermEquiv(script, factorOne, one)) {
			return factorTwo;
		}

		if (QvasrUtils.checkTermEquiv(script, factorTwo, one)) {
			return factorOne;
		}

		Term result = SmtUtils.mul(script.getScript(), "*", factorOne, factorTwo);
		if (QvasrUtils.isApplicationTerm(factorOne) && QvasrUtils.isApplicationTerm(factorTwo)) {
			final ApplicationTerm factorOneAppTerm = (ApplicationTerm) factorOne;
			final ApplicationTerm factorTwoAppTerm = (ApplicationTerm) factorTwo;
			if ("/".equals(factorOneAppTerm.getFunction().getName())
					&& "/".equals(factorTwoAppTerm.getFunction().getName())) {
				final Term commonDivisor = script.getScript().term("*", factorOneAppTerm.getParameters()[1],
						factorTwoAppTerm.getParameters()[1]);
				final Term commonDividend = script.getScript().term("*", factorOneAppTerm.getParameters()[0],
						factorTwoAppTerm.getParameters()[0]);
				result = QvasrAbstractor.simplifyRealDivision(script, commonDividend, commonDivisor);
			}
			if (!"/".equals(factorOneAppTerm.getFunction().getName())
					&& "/".equals(factorTwoAppTerm.getFunction().getName())) {
				final Term commonDividend =
						SmtUtils.mul(script.getScript(), "*", factorOneAppTerm, factorTwoAppTerm.getParameters()[0]);
				result = QvasrAbstractor.simplifyRealDivision(script, commonDividend,
						factorTwoAppTerm.getParameters()[1]);
			}
			if ("/".equals(factorOneAppTerm.getFunction().getName())
					&& !"/".equals(factorTwoAppTerm.getFunction().getName())) {
				final Term commonDividend =
						SmtUtils.mul(script.getScript(), "*", factorOneAppTerm.getParameters()[0], factorTwoAppTerm);
				result = QvasrAbstractor.simplifyRealDivision(script, commonDividend,
						factorOneAppTerm.getParameters()[1]);
			}
		}

		if (!(QvasrUtils.isApplicationTerm(factorOne)) && QvasrUtils.isApplicationTerm(factorTwo)) {
			final ApplicationTerm factorTwoAppTerm = (ApplicationTerm) factorTwo;
			if ("/".equals(factorTwoAppTerm.getFunction().getName())) {
				final Term commonDividend =
						SmtUtils.mul(script.getScript(), "*", factorOne, factorTwoAppTerm.getParameters()[0]);
				result = simplifyRealDivision(script, commonDividend, factorTwoAppTerm.getParameters()[1]);
			}
		}
		if (QvasrUtils.isApplicationTerm(factorOne) && !(QvasrUtils.isApplicationTerm(factorTwo))) {
			final ApplicationTerm factorOneAppTerm = (ApplicationTerm) factorOne;
			if ("/".equals(factorOneAppTerm.getFunction().getName())) {
				final Term commonDividend =
						SmtUtils.mul(script.getScript(), "*", factorTwo, factorOneAppTerm.getParameters()[0]);
				result = simplifyRealDivision(script, commonDividend, factorOneAppTerm.getParameters()[1]);
			}
		}
		return result;
	}

	/**
	 * Simplify differences where either the minuend or subtrahend is a division, or only one of them. For example 2/x -
	 * y/4 -> 8-xy/4x
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 *
	 * @param minuend
	 *            The minuend of the difference
	 * @param subtrahend
	 *            The subtrahend of the difference
	 * @return A simplified real difference
	 */
	public static Term simplifyRealSubtraction(final ManagedScript script, final Term minuend, final Term subtrahend) {
		Term result = SmtUtils.minus(script.getScript(), minuend, subtrahend);
		if (QvasrUtils.isApplicationTerm(subtrahend) && QvasrUtils.isApplicationTerm(minuend)) {
			final ApplicationTerm appTermSubrahend = (ApplicationTerm) subtrahend;
			final ApplicationTerm appTermMinuend = (ApplicationTerm) minuend;
			if ("/".equals(appTermSubrahend.getFunction().getName())) {
				Term simplifiedMinuend;
				final Term dividentSubtrahend = appTermSubrahend.getParameters()[0];
				final Term divisorSubtrahend = appTermSubrahend.getParameters()[1];
				if (!"/".equals(appTermMinuend.getFunction().getName())) {
					final List<Term> paramsMinuend = getApplicationTermMultiplicationParams(script, appTermMinuend);
					paramsMinuend.addAll(getApplicationTermMultiplicationParams(script, divisorSubtrahend));
					final List<Term> paramsDividentSubtrahend =
							getApplicationTermMultiplicationParams(script, dividentSubtrahend);
					final Term divSubMul = expandRealMultiplication(script, paramsMinuend);
					final Term minSubMul = expandRealMultiplication(script, paramsDividentSubtrahend);
					simplifiedMinuend = SmtUtils.minus(script.getScript(), divSubMul, minSubMul);
					result = QvasrAbstractor.simplifyRealDivision(script, simplifiedMinuend, divisorSubtrahend);
					result.toStringDirect();
				} else {
					final Term dividentMinuend = appTermMinuend.getParameters()[0];
					final Term divisorMinuend = appTermMinuend.getParameters()[1];
					if (QvasrUtils.checkTermEquiv(script, divisorSubtrahend, divisorMinuend)) {
						final Term subMinuendSubtrahend =
								SmtUtils.minus(script.getScript(), dividentMinuend, dividentSubtrahend);
						result = QvasrAbstractor.simplifyRealDivision(script, subMinuendSubtrahend, divisorMinuend);
					} else {
						final Term commonDenominator =
								QvasrAbstractor.expandRealMultiplication(script, divisorMinuend, divisorSubtrahend);
						final Term commonDenominatorDividentMinuend =
								QvasrAbstractor.expandRealMultiplication(script, dividentMinuend, divisorSubtrahend);
						final Term commonDenominatorDividentSubtrahend =
								QvasrAbstractor.expandRealMultiplication(script, dividentSubtrahend, divisorMinuend);
						final Term commonDenominatorSub = SmtUtils.minus(script.getScript(),
								commonDenominatorDividentMinuend, commonDenominatorDividentSubtrahend);
						result = QvasrAbstractor.simplifyRealDivision(script, commonDenominatorSub, commonDenominator);
					}
				}
			}
		}

		if (!(QvasrUtils.isApplicationTerm(subtrahend)) && QvasrUtils.isApplicationTerm(minuend)) {
			final ApplicationTerm appTermMinuend = (ApplicationTerm) minuend;
			if ("/".equals(appTermMinuend.getFunction().getName())) {
				final Term simplifiedMinuend;
				final Term dividendMinuend = appTermMinuend.getParameters()[0];
				final Term divisorMinuend = appTermMinuend.getParameters()[1];
				final Term commonDenominatorMinuend = expandRealMultiplication(script, subtrahend, divisorMinuend);
				final List<Term> paramsDividentSubtrahend =
						getApplicationTermMultiplicationParams(script, dividendMinuend);
				final Term commonDenominatorSubtrahend = expandRealMultiplication(script, paramsDividentSubtrahend);
				simplifiedMinuend =
						SmtUtils.minus(script.getScript(), commonDenominatorSubtrahend, commonDenominatorMinuend);
				result = QvasrAbstractor.simplifyRealDivision(script, simplifiedMinuend, divisorMinuend);
				result.toStringDirect();
			}
		}
		if (QvasrUtils.isApplicationTerm(subtrahend) && !(QvasrUtils.isApplicationTerm(minuend))) {
			final ApplicationTerm appTermSubrahend = (ApplicationTerm) subtrahend;
			if ("/".equals(appTermSubrahend.getFunction().getName())) {
				final Term simplifiedMinuend;
				final Term dividentSubtrahend = appTermSubrahend.getParameters()[0];
				final Term divisorSubtrahend = appTermSubrahend.getParameters()[1];
				final Term commonDenominatorMinuend = expandRealMultiplication(script, minuend, divisorSubtrahend);
				final List<Term> paramsDividentSubtrahend =
						getApplicationTermMultiplicationParams(script, dividentSubtrahend);
				final Term commonDenominatorSubtrahend = expandRealMultiplication(script, paramsDividentSubtrahend);
				simplifiedMinuend =
						SmtUtils.minus(script.getScript(), commonDenominatorMinuend, commonDenominatorSubtrahend);
				result = QvasrAbstractor.simplifyRealDivision(script, simplifiedMinuend, divisorSubtrahend);
			}
		}
		return result;
	}

	/**
	 * Simplifies differences of minuend - subtrahend by matching terms.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 * @param minuend
	 *            Minuend of the difference.
	 * @param subtrahend
	 *            Subtrahend of the difference.
	 * @return A simpliefied difference
	 */
	public static Term reduceNegativeRealSubtraction(final ManagedScript script, final Term minuend,
			final Term subtrahend) {
		if (QvasrUtils.isApplicationTerm(minuend) && QvasrUtils.isApplicationTerm(subtrahend)) {
			final ApplicationTerm minuendAppTerm = (ApplicationTerm) minuend;
			final ApplicationTerm subtrahendAppTerm = (ApplicationTerm) subtrahend;
			List<Term> minuendParams = Arrays.asList(minuendAppTerm.getParameters());
			List<Term> subtrahendParams = Arrays.asList(subtrahendAppTerm.getParameters());
			if ("+".equals(minuendAppTerm.getFunction().getName())
					&& "+".equals(subtrahendAppTerm.getFunction().getName())) {
				final Deque<Term> minuendQueue = new ArrayDeque<>();
				final Deque<Term> minuendTemp = new ArrayDeque<>();
				minuendQueue.addAll(minuendParams);
				minuendTemp.addAll(minuendParams);
				final Deque<Term> subtrahendQueue = new ArrayDeque<>();
				subtrahendQueue.addAll(subtrahendParams);
				while (!minuendQueue.isEmpty()) {
					final Term factor = minuendQueue.pop();
					for (final Term factorTwo : subtrahendQueue) {
						if (QvasrUtils.checkTermEquiv(script, factor, factorTwo)) {
							subtrahendQueue.remove(factorTwo);
							minuendTemp.remove(factor);
							break;
						}
					}
				}
				minuendParams = new ArrayList<>(minuendTemp);
				subtrahendParams = new ArrayList<>(subtrahendQueue);
			}
			if (!"+".equals(minuendAppTerm.getFunction().getName())
					&& "+".equals(subtrahendAppTerm.getFunction().getName())) {
				final Deque<Term> minuendQueue = new ArrayDeque<>();
				minuendQueue.add(minuendAppTerm);
				final Deque<Term> subtrahendQueue = new ArrayDeque<>();
				final Deque<Term> subtrahendTemp = new ArrayDeque<>();
				subtrahendQueue.addAll(subtrahendParams);
				subtrahendTemp.addAll(subtrahendParams);
				while (!subtrahendQueue.isEmpty()) {
					final Term factor = subtrahendQueue.pop();
					if (QvasrUtils.checkTermEquiv(script, factor, minuendAppTerm)) {
						minuendQueue.remove(minuendAppTerm);
						subtrahendTemp.remove(factor);
						break;
					}

				}
				minuendParams = new ArrayList<>(minuendQueue);
				subtrahendParams = new ArrayList<>(subtrahendTemp);
			}
			if ("+".equals(minuendAppTerm.getFunction().getName())
					&& !"+".equals(subtrahendAppTerm.getFunction().getName())) {
				final Deque<Term> minuendQueue = new ArrayDeque<>();
				final Deque<Term> minuendTemp = new ArrayDeque<>();
				minuendQueue.addAll(minuendParams);
				minuendTemp.addAll(minuendParams);
				final Deque<Term> subtrahendQueue = new ArrayDeque<>();
				subtrahendQueue.add(subtrahendAppTerm);
				while (!minuendQueue.isEmpty()) {
					final Term factor = minuendQueue.pop();
					if (QvasrUtils.checkTermEquiv(script, factor, subtrahendAppTerm)) {
						minuendQueue.remove(subtrahendAppTerm);
						minuendTemp.remove(factor);
						break;
					}
				}
				minuendParams = new ArrayList<>(minuendTemp);
				subtrahendParams = new ArrayList<>(subtrahendQueue);
			}
			Term minuendReduced = script.getScript().decimal("0");
			Term subtrahendReduced = script.getScript().decimal("0");
			final Term[] minuendParamsArr = minuendParams.toArray(new Term[minuendParams.size()]);
			final Term[] subtrahendParamsArr = subtrahendParams.toArray(new Term[subtrahendParams.size()]);
			if (minuendParams.size() > 1) {
				minuendReduced = SmtUtils.sum(script.getScript(), "+", minuendParamsArr);
			}
			if (minuendParams.size() == 1) {
				minuendReduced = minuendParamsArr[0];
			}

			if (subtrahendParams.size() > 1) {
				subtrahendReduced = SmtUtils.sum(script.getScript(), "+", subtrahendParamsArr);
			}
			if (subtrahendParams.size() == 1) {
				subtrahendReduced = subtrahendParamsArr[0];
			}
			return SmtUtils.minus(script.getScript(), minuendReduced, subtrahendReduced);
		}
		return SmtUtils.minus(script.getScript(), minuend, subtrahend);
	}

	/**
	 * Reduces a real division of dividend / divisor. For example x(x + 1)/yx -> (x + 1)/y
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 * @param dividend
	 *            dividend of the division.
	 * @param divisor
	 *            divisor of the division.
	 * @return A simplified division.
	 */
	public static Pair<Term, Term> reduceRealDivision(final ManagedScript script, final Term dividend,
			final Term divisor) {
		final Term one = script.getScript().decimal("1");
		Term simplifiedDividend = dividend;
		Term simplifiedDivisor = divisor;
		while (true) {
			final Term simplifiedDividendPre = simplifiedDividend;
			if (QvasrUtils.isApplicationTerm(simplifiedDividend) && QvasrUtils.isApplicationTerm(simplifiedDivisor)) {
				final ApplicationTerm dividendAppTerm = (ApplicationTerm) simplifiedDividend;
				final ApplicationTerm divisorAppTerm = (ApplicationTerm) simplifiedDivisor;
				if ("*".equals(dividendAppTerm.getFunction().getName())
						&& "*".equals(divisorAppTerm.getFunction().getName())) {
					final List<Term> paramsDividend = getApplicationTermMultiplicationParams(script, dividendAppTerm);
					final List<Term> paramsDivisor = getApplicationTermMultiplicationParams(script, divisorAppTerm);
					final List<Term> reducedParamsDividend = new ArrayList<>(paramsDividend);
					final List<Term> reducedParamsDivisor = new ArrayList<>(paramsDivisor);
					for (final Term dividendFactor : paramsDividend) {
						for (final Term divisorFactor : paramsDivisor) {
							if (QvasrUtils.checkTermEquiv(script, dividendFactor, divisorFactor)) {
								reducedParamsDividend.remove(dividendFactor);
								reducedParamsDivisor.remove(divisorFactor);
							}
						}
					}
					if (reducedParamsDividend.isEmpty()) {
						reducedParamsDividend.add(one);
					}
					if (reducedParamsDivisor.isEmpty()) {
						reducedParamsDivisor.add(one);
					}
					final Term[] dividendArray = reducedParamsDividend.toArray(new Term[reducedParamsDividend.size()]);
					final Term[] divisorArray = reducedParamsDivisor.toArray(new Term[reducedParamsDivisor.size()]);

					simplifiedDividend = SmtUtils.mul(script.getScript(), "*", dividendArray);
					simplifiedDivisor = SmtUtils.mul(script.getScript(), "*", divisorArray);
				}
				if ("*".equals(dividendAppTerm.getFunction().getName())
						&& !("*".equals(divisorAppTerm.getFunction().getName()))) {
					final List<Term> paramsDividend = getApplicationTermMultiplicationParams(script, dividendAppTerm);
					final List<Term> reducedParamsDividend = new ArrayList<>(paramsDividend);
					final List<Term> reducedParamsDivisor = new ArrayList<>();
					reducedParamsDivisor.add(divisorAppTerm);
					for (final Term dividendFactor : paramsDividend) {
						if (QvasrUtils.checkTermEquiv(script, dividendFactor, divisorAppTerm)) {
							reducedParamsDividend.remove(dividendFactor);
							reducedParamsDivisor.remove(divisorAppTerm);
						}
					}
					if (reducedParamsDividend.isEmpty()) {
						reducedParamsDividend.add(one);
					}
					if (reducedParamsDivisor.isEmpty()) {
						reducedParamsDivisor.add(one);
					}
					final Term[] dividendArray = reducedParamsDividend.toArray(new Term[reducedParamsDividend.size()]);
					final Term[] divisorArray = reducedParamsDivisor.toArray(new Term[reducedParamsDivisor.size()]);
					simplifiedDividend = SmtUtils.mul(script.getScript(), "*", dividendArray);
					simplifiedDivisor = SmtUtils.mul(script.getScript(), "*", divisorArray);
				}
				if (!("*".equals(dividendAppTerm.getFunction().getName()))
						&& "*".equals(divisorAppTerm.getFunction().getName())) {
					final List<Term> paramsDivisor = getApplicationTermMultiplicationParams(script, divisorAppTerm);
					final List<Term> reducedParamsDividend = new ArrayList<>();
					final List<Term> reducedParamsDivisor = new ArrayList<>(paramsDivisor);
					reducedParamsDividend.add(dividendAppTerm);
					for (final Term divisorFactor : paramsDivisor) {
						if (QvasrUtils.checkTermEquiv(script, divisorFactor, dividendAppTerm)) {
							reducedParamsDividend.remove(divisorFactor);
							reducedParamsDivisor.remove(dividendAppTerm);
						}
					}
					if (reducedParamsDividend.isEmpty()) {
						reducedParamsDividend.add(one);
					}
					if (reducedParamsDivisor.isEmpty()) {
						reducedParamsDivisor.add(one);
					}
					final Term[] dividendArray = reducedParamsDividend.toArray(new Term[reducedParamsDividend.size()]);
					final Term[] divisorArray = reducedParamsDivisor.toArray(new Term[reducedParamsDivisor.size()]);
					simplifiedDividend = SmtUtils.mul(script.getScript(), "*", dividendArray);
					simplifiedDivisor = SmtUtils.mul(script.getScript(), "*", divisorArray);
				}
			}
			if (QvasrUtils.isApplicationTerm(simplifiedDividend)
					&& !(QvasrUtils.isApplicationTerm(simplifiedDivisor))) {
				final ApplicationTerm dividendAppTerm = (ApplicationTerm) simplifiedDividend;
				if ("*".equals(dividendAppTerm.getFunction().getName())) {
					final Set<Term> simplifiedDividendParamSet =
							new HashSet<>(Arrays.asList(dividendAppTerm.getParameters()));
					for (final Term dividendFactor : dividendAppTerm.getParameters()) {
						if (QvasrUtils.checkTermEquiv(script, dividendFactor, simplifiedDivisor)) {
							simplifiedDividendParamSet.remove(dividendFactor);
							simplifiedDivisor = one;
						}
					}
					final Term[] dividendArray =
							simplifiedDividendParamSet.toArray(new Term[simplifiedDividendParamSet.size()]);
					simplifiedDividend = SmtUtils.mul(script.getScript(), "*", dividendArray);
				}
			}
			if (!(QvasrUtils.isApplicationTerm(simplifiedDividend))
					&& QvasrUtils.isApplicationTerm(simplifiedDivisor)) {
				final ApplicationTerm divisorAppTerm = (ApplicationTerm) simplifiedDivisor;
				if ("*".equals(divisorAppTerm.getFunction().getName())) {
					final Set<Term> simplifiedDivisorParamSet =
							new HashSet<>(Arrays.asList(divisorAppTerm.getParameters()));
					for (final Term divisorFactor : divisorAppTerm.getParameters()) {
						if (QvasrUtils.checkTermEquiv(script, divisorFactor, simplifiedDividend)) {
							simplifiedDividend = one;
							simplifiedDivisorParamSet.remove(divisorFactor);
						}
					}
					final Term[] divisorArray =
							simplifiedDivisorParamSet.toArray(new Term[simplifiedDivisorParamSet.size()]);
					simplifiedDivisor = SmtUtils.mul(script.getScript(), "*", divisorArray);
				}
			}
			if (QvasrUtils.checkTermEquiv(script, simplifiedDividendPre, simplifiedDividend)) {
				break;
			}
		}
		return new Pair<>(simplifiedDividend, simplifiedDivisor);
	}

	/**
	 * Get the parameters of an Application Term.
	 *
	 * @param script
	 *            A {@link ManagedScript}
	 * @param appTerm
	 *            An {@link ApplicationTerm} who's parameters are extracted
	 * @return A list of terms representing the parameters of the application term.
	 */
	public static List<Term> getApplicationTermMultiplicationParams(final ManagedScript script, final Term appTerm) {
		final List<Term> params = new ArrayList<>();
		if (QvasrUtils.isApplicationTerm(appTerm)) {
			if ("*".equals(((ApplicationTerm) appTerm).getFunction().getName())) {
				for (final Term param : ((ApplicationTerm) appTerm).getParameters()) {
					if (QvasrUtils.isApplicationTerm(param)
							&& ("*".equals(((ApplicationTerm) param).getFunction().getName()))) {
						params.addAll(getApplicationTermMultiplicationParams(script, param));
					} else {
						params.add(param);
					}
				}
			} else {
				params.add(appTerm);
			}
		} else {
			params.add(appTerm);
		}
		return params;
	}

	/**
	 * Get parameters of the special case of {@link ApplicationTerm}: The sum.
	 *
	 * @param appTerm
	 *            Application term with function symbol "+"
	 * @return A list of terms representing the parameters of the sum.
	 */
	public static List<Term> getApplicationTermSumParams(final ApplicationTerm appTerm) {
		final List<Term> params = new ArrayList<>();
		if ("+".equals((appTerm.getFunction().getName()))) {
			for (final Term param : appTerm.getParameters()) {
				if (QvasrUtils.isApplicationTerm(param)
						&& ("+".endsWith(((ApplicationTerm) param).getFunction().getName()))) {
					params.addAll(getApplicationTermSumParams((ApplicationTerm) param));
				} else {
					params.add(param);
				}
			}
		} else {
			params.add(appTerm);
		}
		return params;
	}

	/**
	 * Find a column to use as pivot in the gaussian elimination algorithm.
	 *
	 * @param matrix
	 *            A matrix representing the current state of the Gaussian Elimination
	 * @param col
	 *            A column
	 * @return An integer representing the new pivot row.
	 */
	private static int findPivot(final ManagedScript script, final Term[][] matrix, final int col) {
		int maxRow = -1;
		for (int row = col; row < matrix.length; row++) {
			if (!QvasrUtils.checkTermEquiv(script, matrix[row][col], script.getScript().decimal("0"))) {
				maxRow = row;
				break;
			}
		}
		return maxRow;
	}

	/**
	 * Swap two rows in a matrix.
	 *
	 * @param matrix
	 *            A matrix where two rows will be swapped.
	 * @param col
	 * @param row
	 * @return
	 */
	private static Term[][] swap(final Term[][] matrix, final int col, final int row) {
		Term temp;
		for (int i = col; i < matrix[col].length; i++) {
			temp = matrix[col][i];
			matrix[col][i] = matrix[row][i];
			matrix[row][i] = temp;
		}
		return matrix;
	}

	/**
	 * Find Updates to variables in the transition formula. Needed to construct a linear system of equations to compute
	 * bases of resets and increments for the Q-Vasr-abstraction.
	 *
	 * @param transitionTerm
	 * @param outVariables
	 * @return
	 */
	private static Map<TermVariable, Term> getUpdates(final IUltimateServiceProvider services,
			final ManagedScript script, final UnmodifiableTransFormula transitionFormula, final BaseType baseType) {
		final SimultaneousUpdate su;
		try {
			su = SimultaneousUpdate.fromTransFormula(services, transitionFormula, script);
		} catch (final Exception e) {
			throw new UnsupportedOperationException("Could not compute Simultaneous Update!");
		}
		/*
		 * Create a new real sort termvariable.
		 */
		final Map<Term, Term> realTvs = new HashMap<>();
		final Map<IProgramVar, Term> updates = su.getDeterministicAssignment();
		/*
		 * TODO: Look at havoced vars.
		 */
		for (final IProgramVar readOnlyVar : su.getReadonlyVars()) {
			updates.put(readOnlyVar, readOnlyVar.getTermVariable());
		}
		for (final IProgramVar pv : updates.keySet()) {
			final TermVariable inVar = script.constructFreshTermVariable(pv.getGloballyUniqueId() + "_real",
					SmtSortUtils.getRealSort(script));
			realTvs.put(pv.getTermVariable(), inVar);
		}
		/*
		 * Transform the updates to variables to real sort.
		 */
		final HashMap<IProgramVar, Term> realUpdates = new HashMap<>();
		for (final Entry<IProgramVar, Term> update : updates.entrySet()) {
			final Term intUpdate = update.getValue();
			final Term realUpdate = Substitution.apply(script, realTvs, intUpdate);
			realUpdates.put(update.getKey(), realUpdate);
		}
		final Map<TermVariable, Term> assignments = new LinkedHashMap<>();
		for (final Entry<IProgramVar, Term> varUpdate : realUpdates.entrySet()) {
			final IProgramVar progVar = varUpdate.getKey();
			final Term varUpdateTerm = varUpdate.getValue();
			final HashMap<Term, Term> subMappingTerm = new HashMap<>();
			Term realTerm;
			if (QvasrUtils.isApplicationTerm(varUpdateTerm)) {
				final ApplicationTerm varUpdateAppterm = (ApplicationTerm) varUpdateTerm;
				subMappingTerm.putAll(appTermToReal(script, varUpdateAppterm));
				realTerm = Substitution.apply(script, subMappingTerm, varUpdateAppterm);
			} else if (varUpdateTerm instanceof ConstantTerm) {
				final Rational value = SmtUtils.toRational((ConstantTerm) varUpdateTerm);
				realTerm = value.toTerm(SmtSortUtils.getRealSort(script));
			} else {
				realTerm = realTvs.get(progVar.getTermVariable());
			}
			if (baseType == BaseType.ADDITIONS) {
				final Term realVar = realTvs.get(progVar.getTermVariable());
				realTerm = SmtUtils.minus(script.getScript(), realTerm, realVar);
			}
			assignments.put((TermVariable) realTvs.get(progVar.getTermVariable()), realTerm);
		}

		return assignments;
	}

	/**
	 * Converts a give application term to real sort.
	 *
	 * @param appTerm
	 * @return
	 */
	private static Map<Term, Term> appTermToReal(final ManagedScript script, final ApplicationTerm appTerm) {
		final Map<Term, Term> subMap = new HashMap<>();
		for (final Term param : appTerm.getParameters()) {
			if (param.getSort() == SmtSortUtils.getRealSort(script)) {
			} else if (param instanceof ConstantTerm) {
				final ConstantTerm paramConst = (ConstantTerm) param;
				final Rational paramValue = (Rational) paramConst.getValue();
				subMap.put(param, paramValue.toTerm(SmtSortUtils.getRealSort(script)));
			} else if (param instanceof TermVariable) {
				subMap.put(param, script.constructFreshTermVariable(((TermVariable) param).getName(),
						SmtSortUtils.getRealSort(script)));
			} else {
				subMap.putAll(appTermToReal(script, (ApplicationTerm) param));
			}
		}
		return subMap;
	}

	/**
	 * Construct a matrix representing a set of linear equations that model updates to variables in a given transition
	 * formula. The matrix has 2^n columns with n being the number of outvars, because we have to set each variable to 0
	 * to be able to use Gaussian elimination. We want to have a matrix for the bases of resets Res: {[s_1, s_2, ...,
	 * s_n] [x_1', x_2', ...] = a} and additions Inc: {[s_1, s_2, ..., s_n] [x_1', x_2', ...] = [s_1, s_2, ..., s_n]
	 * [x_1, x_2, ..., x_n] + a}
	 *
	 * @param updates
	 * @param transitionFormula
	 * @param typeOfBase
	 * @return
	 */
	private static Term[][] constructBaseMatrix(final ManagedScript script, final Map<TermVariable, Term> updates,
			final UnmodifiableTransFormula transitionFormula) {
		final int columnDimension = transitionFormula.getOutVars().size();

		final Set<Set<Term>> setToZero = new HashSet<>();
		final Map<Term, Term> intToReal = new HashMap<>();
		for (final Term tv : updates.keySet()) {
			final Set<Term> inVar = new HashSet<>();
			inVar.add(tv);
			setToZero.add(inVar);
		}
		/*
		 * To get a linear set of equations, which we want to solve, we set the various variables to 0.
		 */
		Set<Set<Term>> powerset = new HashSet<>(setToZero);
		for (final Set<Term> inTv : setToZero) {
			powerset = QvasrUtils.joinSet(powerset, inTv);
		}
		final Term[][] baseMatrix = new Term[powerset.size() + 1][columnDimension + 1];

		for (int i = 0; i < powerset.size() + 1; i++) {
			for (int j = 0; j < columnDimension + 1; j++) {
				baseMatrix[i][j] = script.getScript().decimal("0");
			}
		}

		final Deque<Set<Term>> zeroStack = new HashDeque<>();
		zeroStack.addAll(powerset);
		final Term one = script.getScript().decimal("1");
		final Term zero = script.getScript().decimal("0");
		int j = 0;
		while (!zeroStack.isEmpty()) {
			int i = 0;
			/*
			 * Set the a column to one, not a.
			 */
			baseMatrix[j][columnDimension] = one;
			final Map<Term, Term> subMapping = new HashMap<>();
			if (j > 0) {
				final Set<Term> toBeSetZero = zeroStack.pop();
				for (final Term tv : toBeSetZero) {
					subMapping.put(tv, zero);
				}
			}
			for (final Entry<TermVariable, Term> update : updates.entrySet()) {
				final Term updateTerm = update.getValue();
				Term toBeUpdated;
				toBeUpdated = Substitution.apply(script, subMapping, updateTerm);
				final Term toBeUpdatedReal = Substitution.apply(script, intToReal, toBeUpdated);
				baseMatrix[j][i] = toBeUpdatedReal;
				i++;
			}
			j++;
		}
		return baseMatrix;
	}

	/**
	 * Construct a formula modeling updates to variables done in a transition formula in relation to a new termvariable
	 * s. (May not be needed, as we can skip this construction)
	 *
	 * @param updates
	 * @param transitionFormula
	 * @param typeOfBase
	 * @return
	 */
	private Term constructBaseFormula(final ManagedScript script, final Map<TermVariable, Set<Term>> updates,
			final UnmodifiableTransFormula transitionFormula, final BaseType baseType) {
		int sCount = 0;
		final Set<Term> newUpdates = new HashSet<>();
		for (final var variableUpdate : updates.entrySet()) {
			final TermVariable s = script.constructFreshTermVariable("s" + sCount, SmtSortUtils.getRealSort(script));
			for (final Term update : variableUpdate.getValue()) {
				final Term mult = SmtUtils.mul(script.getScript(), "*", s, update);
				newUpdates.add(mult);
			}
			sCount++;
		}
		Term addition = script.getScript().decimal("1");
		for (final Term update : newUpdates) {
			addition = SmtUtils.sum(script.getScript(), "+", addition, update);
		}
		addition = SmtUtils.equality(script.getScript(), addition,
				script.constructFreshTermVariable("a", SmtSortUtils.getRealSort(script)));
		return addition;
	}
}
