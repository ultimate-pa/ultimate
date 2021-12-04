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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermOperations;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) This class is used to compute a {@link QvasrAbstraction}
 *         for a given {@link Term} by solving various sets of linear equation systems.
 *
 *
 */
public class QvasrAbstractor {

	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final Term mZero;
	private final Term mOne;

	/**
	 *
	 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de) Define which kind of base matrix. Resets: Where the
	 *         outvars only depend on the invars and addition vector a. Additions: Where outvars depend on invars and
	 *         addition vector a.
	 *
	 */
	private enum BaseType {
		RESETS, ADDITIONS
	}

	/**
	 * Computes a Q-Vasr-abstraction (S, V), with linear simulation matrix S and Q-Vasr V. A transition formula can be
	 * overapproximated using a Q-Vasr-abstraction.
	 *
	 * @param script
	 * @param logger
	 */
	public QvasrAbstractor(final ManagedScript script, final ILogger logger, final IUltimateServiceProvider services) {
		mScript = script;
		mLogger = logger;
		mServices = services;
		mZero = mScript.getScript().decimal("0");
		mOne = mScript.getScript().decimal("1");
	}

	/**
	 * Compute a Q-Vasr-abstraction for a given transition formula.
	 *
	 * @param transitionTerm
	 * @param transitionFormula
	 * @return
	 */
	public QvasrAbstraction computeAbstraction(final Term transitionTerm,
			final UnmodifiableTransFormula transitionFormula) {

		final Map<Term, Term> updatesInFormulaAdditions = getUpdates(transitionFormula, BaseType.ADDITIONS);
		final Map<Term, Term> updatesInFormulaResets = getUpdates(transitionFormula, BaseType.RESETS);
		final Term[][] newUpdatesMatrixResets = constructBaseMatrix(updatesInFormulaResets, transitionFormula);
		final Term[][] newUpdatesMatrixAdditions = constructBaseMatrix(updatesInFormulaAdditions, transitionFormula);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Resets: ");
			printMatrix(newUpdatesMatrixResets);
			mLogger.debug("Additions: ");
			printMatrix(newUpdatesMatrixAdditions);
		}

		final Term[][] gaussedResets = gaussPartialPivot(newUpdatesMatrixResets);
		Term[][] gaussedResetsOnesPruned = removeZeroRows(gaussedResets);
		gaussedResetsOnesPruned = removeDuplicateRows(gaussedResetsOnesPruned);
		final Term[][] solutionsResetGaussJordan = gaussRowEchelonFormJordan(gaussedResetsOnesPruned);
		final Rational[][] out = new Rational[2][2];
		final Qvasr qvasr = null;
		return new QvasrAbstraction(out, qvasr);
	}

	/**
	 * Convert a matrix in upper triangular form into row echelon form -> only leading 1s using Standard Real Division.
	 *
	 * @param matrix
	 * @return
	 *
	 */
	private Term[][] gaussRowEchelonForm(final Term[][] matrix) {
		for (int i = 0; i < matrix.length; i++) {
			for (int j = 0; j < matrix[0].length; j++) {
				if (!checkTermEquiv(mScript, mZero, matrix[i][j])) {
					final Term divider = matrix[i][j];
					final Term dividerInverse = getDivisionInverse(mScript, matrix[i][j]);
					for (int k = j; k < matrix[0].length; k++) {
						final Term toBeDivided = matrix[i][k];
						final Term mult =
								QvasrAbstractor.simplifyRealMultiplication(mScript, toBeDivided, dividerInverse);
						final Term division = QvasrAbstractor.simplifyRealDivision(mScript, toBeDivided, divider);
						if (mLogger.isDebugEnabled()) {
							mLogger.debug("Matrix " + i + k + " =  " + division.toStringDirect());
						}
						matrix[i][k] = mult;
					}
					break;
				}
			}
		}
		return matrix;
	}

	/**
	 * Bring a given matrix into upper triangle form.
	 *
	 * @param matrix
	 * @return
	 */
	private Term[][] gaussPartialPivot(Term[][] matrix) {
		for (int k = 0; k < matrix.length - 1; k++) {
			int max = -1;
			if ((k + 1) < matrix.length && (k + 1) < matrix[0].length) {
				max = findPivot(matrix, k);
			}
			if (max == -1) {
				mLogger.warn("Gaussian Elimination Done.");
				return matrix;
			}
			if (max != 0) {
				matrix = swap(matrix, k, max);
			}
			final Term pivot = matrix[k][k];
			// i is the row
			for (int i = k + 1; i < matrix.length; i++) {
				final Term toBeEliminated = matrix[i][k];
				matrix[i][k] = mZero;
				final Term newDiv = QvasrAbstractor.simplifyRealDivision(mScript, toBeEliminated, pivot);

				// k is the column
				for (int j = k + 1; j < matrix[0].length; j++) {
					final Term currentColumn = matrix[k][j];
					final Term currentEntry = matrix[i][j];
					final Term newMul = QvasrAbstractor.simplifyRealMultiplication(mScript, newDiv, currentColumn);
					final Term newSub = QvasrAbstractor.simplifyRealSubtraction(mScript, currentEntry, newMul);
					matrix[i][j] = newSub;
				}
			}
		}
		return matrix;
	}

	/**
	 * Convert a matrix in upper triangular form into row echelon form -> only leading 1s using {@link PolynomialTerm}
	 *
	 * @param matrix
	 * @return
	 */
	private Term[][] gaussRowEchelonFormPolynomial(final Term[][] matrix) {
		for (int i = 0; i < matrix.length; i++) {
			for (int j = 0; j < matrix[0].length; j++) {
				if (!checkTermEquiv(mScript, matrix[i][j], mZero)) {
					final IPolynomialTerm divider = PolynomialTermOperations.convert(mScript.getScript(), matrix[i][j]);
					for (int k = j; k < matrix[0].length; k++) {
						final IPolynomialTerm[] polyArr = new IPolynomialTerm[2];
						final IPolynomialTerm toBeDivided =
								PolynomialTermOperations.convert(mScript.getScript(), matrix[i][k]);
						polyArr[0] = toBeDivided;
						polyArr[1] = divider;
						final IPolynomialTerm polyDiv;
						if (PolynomialTerm.divisionPossible(polyArr)) {
							polyDiv = AffineTerm.divide(polyArr, mScript.getScript());
						} else {
							polyDiv = PolynomialTermUtils.simplifyImpossibleDivision("/", polyArr, mScript.getScript());
						}
						matrix[i][k] = polyDiv.toTerm(mScript.getScript());
					}
					break;
				}
			}
		}
		return matrix;
	}

	/**
	 * Convert a matrix in upper triangular form into row echelon form -> only leading 1s using Standard Real Division.
	 *
	 * @param matrix
	 * @return
	 *
	 */
	private Term[][] gaussRowEchelonFormJordan(final Term[][] matrix) {
		for (int i = matrix.length - 1; 0 <= i; i--) {
			for (int j = 0; j < matrix[0].length; j++) {
				if (!checkTermEquiv(mScript, matrix[i][j], mZero)) {
					final Term dividerInverse = getDivisionInverse(mScript, matrix[i][j]);
					for (int k = j; k < matrix[0].length; k++) {
						final Term toBeDivided = matrix[i][k];
						final Term mult =
								QvasrAbstractor.simplifyRealMultiplication(mScript, toBeDivided, dividerInverse);
						matrix[i][k] = mult;
					}
					for (int l = i - 1; l >= 0; l--) {
						final Term toBeEliminatedMult = matrix[l][j];
						for (int m = j; m < matrix[0].length; m++) {
							final Term rowEntry = matrix[i][m];
							final Term rowEntryToBeEliminated = matrix[l][m];
							final Term multRow =
									QvasrAbstractor.simplifyRealMultiplication(mScript, toBeEliminatedMult, rowEntry);
							final Term subRow =
									QvasrAbstractor.simplifyRealSubtraction(mScript, rowEntryToBeEliminated, multRow);
							matrix[l][m] = subRow;
						}
					}
					break;
				}
			}
		}
		return matrix;
	}

	public static Term getDivisionInverse(final ManagedScript script, final Term term) {
		Term result;
		if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getFunction().getName().equals("/")) {
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
	 * Use back substitution to compute solutions for a matrix in row echelon form.
	 *
	 * @param matrix
	 * @return
	 */
	private Term[] backSub(final Term[][] matrix) {
		final Term[] solutions = new Term[matrix[0].length - 1];
		for (int k = 0; k < matrix[0].length - 1; k++) {
			solutions[k] = mZero;
		}
		final int columns = matrix[0].length - 1;
		int solCounter = matrix[0].length - 2;
		for (int i = matrix.length - 1; 0 <= i; i--) {
			solutions[solCounter] = matrix[i][columns];
			for (int j = solCounter + 1; j <= columns - 1; j++) {
				final Term mul = QvasrAbstractor.simplifyRealMultiplication(mScript, matrix[i][j], solutions[j]);
				final Term sub = QvasrAbstractor.simplifyRealSubtraction(mScript, solutions[solCounter], mul);
				solutions[solCounter] = sub;
			}
			solCounter--;
		}
		return solutions;
	}

	/**
	 * Remove rows with all 0s from a given matrix.
	 *
	 * @param matrix
	 * @return
	 */
	private Term[][] removeZeroRows(final Term[][] matrix) {
		final Set<Integer> toBeEliminated = new HashSet<>();
		for (int i = 0; i < matrix.length; i++) {
			for (int j = 0; j < matrix[0].length; j++) {
				if (!checkTermEquiv(mScript, matrix[i][j], mZero)) {
					break;
				}
				if (j == matrix[0].length - 1) {
					toBeEliminated.add(i);
				}
			}
		}
		final int prunedLength = matrix.length - toBeEliminated.size();
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
	}

	/**
	 * Remove rows from a matrix that are identical.
	 *
	 * @param matrix
	 * @return
	 */
	private Term[][] removeDuplicateRows(final Term[][] matrix) {
		final Set<Integer> toBeEliminated = new HashSet<>();
		for (int i = 0; i < matrix.length; i++) {
			final Set<Integer> possibleDuplicates = new HashSet<>();
			for (int j = i + 1; j < matrix.length; j++) {
				if (checkTermEquiv(mScript, matrix[i][0], matrix[j][0])) {
					possibleDuplicates.add(j);
				}
				final Set<Integer> trueDuplicates = new HashSet<>(possibleDuplicates);
				for (final Integer k : possibleDuplicates) {
					for (int l = 0; l < matrix[0].length; l++) {
						if (!checkTermEquiv(mScript, matrix[k][l], matrix[i][l])) {
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
		final Term[][] prunedMatrix = new Term[prunedLength][matrix[0].length];
		int cnt = 0;
		for (int k = 0; k < prunedLength; k++) {
			if (!toBeEliminated.contains(k)) {
				for (int l = 0; l < matrix[0].length; l++) {
					prunedMatrix[cnt][l] = matrix[k][l];
				}
				cnt++;
			}
		}
		return prunedMatrix;
	}

	/**
	 * Factors out coefficients from sums.
	 *
	 * @param script
	 * @param sum
	 * @return
	 */
	private static Term factorOutRealSum(final ManagedScript script, final Term sum) {
		if (sum instanceof ApplicationTerm) {
			final ApplicationTerm sumAppTerm = (ApplicationTerm) sum;
			final List<Term> summands = getApplicationTermSumParams(sumAppTerm);
			final List<Term> simplifiedSummands = new ArrayList<>();

			for (final Term summandOne : summands) {
				if (summandOne instanceof ApplicationTerm
						&& ((ApplicationTerm) summandOne).getFunction().getName().equals("*")) {
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
	 * Checks for equivalence of terms.
	 *
	 * @param script
	 * @param firstEntry
	 * @param secondEntry
	 * @return
	 */
	public static boolean checkTermEquiv(final ManagedScript script, final Term firstEntry, final Term secondEntry) {
		return SmtUtils.areFormulasEquivalent(firstEntry, secondEntry, script.getScript());
	}

	/**
	 * Simplify multiplications of two factors.
	 *
	 * @param factorOne
	 * @param factorTwo
	 * @return
	 */
	public static Term expandRealMultiplication(final ManagedScript script, final Term factorOne,
			final Term factorTwo) {
		final List<Term> factorOneVars = new ArrayList<>();
		final List<Term> factorTwoVars = new ArrayList<>();
		if (factorOne instanceof ApplicationTerm && factorTwo instanceof ApplicationTerm) {
			final ApplicationTerm factorOneAppTerm = (ApplicationTerm) factorOne;
			final ApplicationTerm factorTwoAppTerm = (ApplicationTerm) factorTwo;
			if (factorOneAppTerm.getFunction().getName().equals("+")) {
				for (final Term param : factorOneAppTerm.getParameters()) {
					if (param instanceof ApplicationTerm) {
						factorOneVars.addAll(getApplicationTermSumParams((ApplicationTerm) param));
					} else {
						factorOneVars.add(param);
					}
				}
			} else {
				factorOneVars.add(factorOneAppTerm);
			}
			if (factorTwoAppTerm.getFunction().getName().equals("+")) {
				for (final Term param : factorTwoAppTerm.getParameters()) {
					if (param instanceof ApplicationTerm) {
						factorTwoVars.addAll(getApplicationTermSumParams((ApplicationTerm) param));
					} else {
						factorTwoVars.add(param);
					}
				}
			} else {
				factorTwoVars.add(factorTwoAppTerm);
			}

		}

		if (!(factorOne instanceof ApplicationTerm) && factorTwo instanceof ApplicationTerm) {
			final ApplicationTerm factorTwoAppTerm = (ApplicationTerm) factorTwo;
			factorOneVars.add(factorOne);
			if (factorTwoAppTerm.getFunction().getName().equals("+")) {
				for (final Term param : factorTwoAppTerm.getParameters()) {
					if (param instanceof ApplicationTerm) {
						factorTwoVars.addAll(getApplicationTermSumParams((ApplicationTerm) param));
					} else {
						factorTwoVars.add(param);
					}
				}
			} else {
				factorTwoVars.add(factorTwoAppTerm);
			}
		}

		if (factorOne instanceof ApplicationTerm && !(factorTwo instanceof ApplicationTerm)) {
			final ApplicationTerm factorOneAppTerm = (ApplicationTerm) factorOne;
			factorTwoVars.add(factorTwo);
			if (factorOneAppTerm.getFunction().getName().equals("+")) {
				for (final Term param : factorOneAppTerm.getParameters()) {
					if (param instanceof ApplicationTerm) {
						factorOneVars.addAll(getApplicationTermSumParams((ApplicationTerm) param));
					} else {
						factorOneVars.add(param);
					}
				}
			} else {
				factorOneVars.add(factorOneAppTerm);
			}
		}

		if (!(factorOne instanceof ApplicationTerm) && !(factorTwo instanceof ApplicationTerm)) {
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
	 * Simplify multiplications of two factors.
	 *
	 * @param factorOne
	 * @param factorTwo
	 * @return
	 */
	public static Term expandRealMultiplication(final ManagedScript script, final List<Term> factors) {
		Term result = script.getScript().decimal("0");
		if (factors.size() < 2) {
			return factors.get(0);
		}
		final Deque<Term> factorStack = new ArrayDeque<>(factors);
		while (!factorStack.isEmpty()) {
			final Term factorOne = factorStack.pop();
			for (final Term factorTwo : factorStack) {
				if (factorOne instanceof ApplicationTerm) {
					final ApplicationTerm factorOneAppTerm = (ApplicationTerm) factorOne;
					if (factorTwo instanceof ApplicationTerm) {
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
				} else if (factorTwo instanceof ApplicationTerm) {
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
	 * Simplify a Division which is multiplied.
	 *
	 * @param dividend
	 * @param divisor
	 * @param mult
	 * @return
	 */
	public static Term simplifyRealDivision(final ManagedScript script, final Term dividend, final Term divisor) {
		final Term zero = script.getScript().decimal("0");
		final Term one = script.getScript().decimal("1");

		Term result = SmtUtils.divReal(script.getScript(), dividend, divisor);
		/*
		 * Can be represented by AffineTerm -> less expensive
		 */
		if (checkTermEquiv(script, divisor, zero)) {
			throw new UnsupportedOperationException("cannot divide by 0!");
		}
		if (checkTermEquiv(script, divisor, script.getScript().decimal("1"))) {
			return dividend;
		}
		if (checkTermEquiv(script, dividend, zero)) {
			return zero;
		}

		if (checkTermEquiv(script, dividend, divisor)) {
			return one;
		}

		if (dividend instanceof ApplicationTerm && divisor instanceof ApplicationTerm) {
			final ApplicationTerm dividendAppTerm = (ApplicationTerm) dividend;
			final ApplicationTerm divisorAppTerm = (ApplicationTerm) divisor;
			Term dividendDividend;
			Term dividendDivisor = one;
			Term divisorDividend;
			Term divisorDivisor = one;
			if (dividendAppTerm.getFunction().getName().equals("/")) {
				dividendDividend = dividendAppTerm.getParameters()[0];
				dividendDivisor = dividendAppTerm.getParameters()[1];
			} else {
				dividendDividend = dividendAppTerm;
			}
			if (divisorAppTerm.getFunction().getName().equals("/")) {
				divisorDividend = divisorAppTerm.getParameters()[0];
				divisorDivisor = divisorAppTerm.getParameters()[1];
			} else {
				divisorDividend = divisorAppTerm;
			}

			if (divisorAppTerm.getFunction().getName().equals("/")
					|| dividendAppTerm.getFunction().getName().equals("/")) {
				final Term commonDividend = SmtUtils.mul(script.getScript(), "*", dividendDividend, divisorDivisor);
				final Term commonDivisor = SmtUtils.mul(script.getScript(), "*", dividendDivisor, divisorDividend);
				final Pair<Term, Term> resultReduced =
						QvasrAbstractor.reduceRealDivision(script, commonDividend, commonDivisor);
				result = SmtUtils.divReal(script.getScript(), resultReduced.getFirst(), resultReduced.getSecond());
			}

			if (!(divisorAppTerm.getFunction().getName().equals("/"))
					&& !(dividendAppTerm.getFunction().getName().equals("/"))) {
				final Pair<Term, Term> resultReduced = QvasrAbstractor.reduceRealDivision(script, dividend, divisor);
				result = SmtUtils.divReal(script.getScript(), resultReduced.getFirst(), resultReduced.getSecond());
			}
		}

		if (dividend instanceof ApplicationTerm && !(divisor instanceof ApplicationTerm)) {
			final ApplicationTerm dividendAppTerm = (ApplicationTerm) dividend;
			Pair<Term, Term> resultReduced;
			if (dividendAppTerm.getFunction().getName().equals("/")) {
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

		if (!(dividend instanceof ApplicationTerm) && divisor instanceof ApplicationTerm) {
			final ApplicationTerm divisorAppTerm = (ApplicationTerm) divisor;
			Pair<Term, Term> resultReduced;
			if (divisorAppTerm.getFunction().getName().equals("/")) {
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

		if (!(dividend instanceof ApplicationTerm) && !(divisor instanceof ApplicationTerm)) {
			final Pair<Term, Term> resultReduced = QvasrAbstractor.reduceRealDivision(script, dividend, divisor);
			result = SmtUtils.divReal(script.getScript(), resultReduced.getFirst(), resultReduced.getSecond());
		}
		return result;
	}

	/**
	 * Simplify a multiplication between two reals.
	 *
	 * @param script
	 * @param factorOne
	 * @param factorTwo
	 * @return
	 */
	public static Term simplifyRealMultiplication(final ManagedScript script, final Term factorOne,
			final Term factorTwo) {
		Term result = SmtUtils.mul(script.getScript(), "*", factorOne, factorTwo);
		final Term zero = script.getScript().decimal("0");
		final Term one = script.getScript().decimal("1");

		if (checkTermEquiv(script, factorOne, zero) || checkTermEquiv(script, factorTwo, zero)) {
			return zero;
		}

		if (checkTermEquiv(script, factorOne, one)) {
			return factorTwo;
		}

		if (checkTermEquiv(script, factorTwo, one)) {
			return factorOne;
		}

		if (factorOne instanceof ApplicationTerm && factorTwo instanceof ApplicationTerm) {
			final ApplicationTerm factorOneAppTerm = (ApplicationTerm) factorOne;
			final ApplicationTerm factorTwoAppTerm = (ApplicationTerm) factorTwo;
			if (factorOneAppTerm.getFunction().getName().equals("/")
					&& factorTwoAppTerm.getFunction().getName().equals("/")) {
				final Term commonDivisor = script.getScript().term("*", factorOneAppTerm.getParameters()[1],
						factorTwoAppTerm.getParameters()[1]);
				final Term commonDividend = script.getScript().term("*", factorOneAppTerm.getParameters()[0],
						factorTwoAppTerm.getParameters()[0]);
				result = QvasrAbstractor.simplifyRealDivision(script, commonDividend, commonDivisor);
			}
			if (!factorOneAppTerm.getFunction().getName().equals("/")
					&& factorTwoAppTerm.getFunction().getName().equals("/")) {
				final Term commonDividend =
						SmtUtils.mul(script.getScript(), "*", factorOneAppTerm, factorTwoAppTerm.getParameters()[0]);
				result = QvasrAbstractor.simplifyRealDivision(script, commonDividend,
						factorTwoAppTerm.getParameters()[1]);
			}
			if (factorOneAppTerm.getFunction().getName().equals("/")
					&& !factorTwoAppTerm.getFunction().getName().equals("/")) {
				final Term commonDividend =
						SmtUtils.mul(script.getScript(), "*", factorOneAppTerm.getParameters()[0], factorTwoAppTerm);
				result = QvasrAbstractor.simplifyRealDivision(script, commonDividend,
						factorOneAppTerm.getParameters()[1]);
			}
		}

		if (!(factorOne instanceof ApplicationTerm) && factorTwo instanceof ApplicationTerm) {
			final ApplicationTerm factorTwoAppTerm = (ApplicationTerm) factorTwo;
			if (factorTwoAppTerm.getFunction().getName().equals("/")) {
				final Term commonDividend =
						SmtUtils.mul(script.getScript(), "*", factorOne, factorTwoAppTerm.getParameters()[0]);
				result = simplifyRealDivision(script, commonDividend, factorTwoAppTerm.getParameters()[1]);
			}
		}
		if (factorOne instanceof ApplicationTerm && !(factorTwo instanceof ApplicationTerm)) {
			final ApplicationTerm factorOneAppTerm = (ApplicationTerm) factorOne;
			if (factorOneAppTerm.getFunction().getName().equals("/")) {
				final Term commonDividend =
						SmtUtils.mul(script.getScript(), "*", factorTwo, factorOneAppTerm.getParameters()[0]);
				result = simplifyRealDivision(script, commonDividend, factorOneAppTerm.getParameters()[1]);
			}
		}
		return result;
	}

	/**
	 * Simplify differences where either the minuend or subtrahend is a division, or only one of them.
	 *
	 * @param minuend
	 * @param subtrahend
	 * @return
	 */
	public static Term simplifyRealSubtraction(final ManagedScript script, final Term minuend, final Term subtrahend) {
		Term result = SmtUtils.minus(script.getScript(), minuend, subtrahend);
		if (subtrahend instanceof ApplicationTerm && minuend instanceof ApplicationTerm) {
			final ApplicationTerm appTermSubrahend = (ApplicationTerm) subtrahend;
			final ApplicationTerm appTermMinuend = (ApplicationTerm) minuend;
			if (appTermSubrahend.getFunction().getName().equals("/")) {
				Term simplifiedMinuend;
				final Term dividentSubtrahend = appTermSubrahend.getParameters()[0];
				final Term divisorSubtrahend = appTermSubrahend.getParameters()[1];
				if (!appTermMinuend.getFunction().getName().equals("/")) {
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
					if (checkTermEquiv(script, divisorSubtrahend, divisorMinuend)) {
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

		if (!(subtrahend instanceof ApplicationTerm) && minuend instanceof ApplicationTerm) {
			final ApplicationTerm appTermMinuend = (ApplicationTerm) minuend;
			if (appTermMinuend.getFunction().getName().equals("/")) {
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
		if (subtrahend instanceof ApplicationTerm && !(minuend instanceof ApplicationTerm)) {
			final ApplicationTerm appTermSubrahend = (ApplicationTerm) subtrahend;
			if (appTermSubrahend.getFunction().getName().equals("/")) {
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
	 * Reduces subtractions of minuend - subtrahend by matching terms.
	 *
	 * @param script
	 * @param minuend
	 * @param subtrahend
	 * @return
	 */
	public static Term reduceNegativeRealSubtraction(final ManagedScript script, final Term minuend,
			final Term subtrahend) {
		if (minuend instanceof ApplicationTerm && subtrahend instanceof ApplicationTerm) {
			final ApplicationTerm minuendAppTerm = (ApplicationTerm) minuend;
			final ApplicationTerm subtrahendAppTerm = (ApplicationTerm) subtrahend;
			List<Term> minuendParams = Arrays.asList(minuendAppTerm.getParameters());
			List<Term> subtrahendParams = Arrays.asList(subtrahendAppTerm.getParameters());
			if (minuendAppTerm.getFunction().getName().equals("+")
					&& subtrahendAppTerm.getFunction().getName().equals("+")) {
				final Deque<Term> minuendQueue = new ArrayDeque<>();
				final Deque<Term> minuendTemp = new ArrayDeque<>();
				minuendQueue.addAll(minuendParams);
				minuendTemp.addAll(minuendParams);
				final Deque<Term> subtrahendQueue = new ArrayDeque<>();
				subtrahendQueue.addAll(subtrahendParams);
				while (!minuendQueue.isEmpty()) {
					final Term factor = minuendQueue.pop();
					for (final Term factorTwo : subtrahendQueue) {
						if (checkTermEquiv(script, factor, factorTwo)) {
							subtrahendQueue.remove(factorTwo);
							minuendTemp.remove(factor);
							break;
						}
					}
				}
				minuendParams = new ArrayList<>(minuendTemp);
				subtrahendParams = new ArrayList<>(subtrahendQueue);
			}
			if (!minuendAppTerm.getFunction().getName().equals("+")
					&& subtrahendAppTerm.getFunction().getName().equals("+")) {
				final Deque<Term> minuendQueue = new ArrayDeque<>();
				minuendQueue.add(minuendAppTerm);
				final Deque<Term> subtrahendQueue = new ArrayDeque<>();
				final Deque<Term> subtrahendTemp = new ArrayDeque<>();
				subtrahendQueue.addAll(subtrahendParams);
				subtrahendTemp.addAll(subtrahendParams);
				while (!subtrahendQueue.isEmpty()) {
					final Term factor = subtrahendQueue.pop();
					if (checkTermEquiv(script, factor, minuendAppTerm)) {
						minuendQueue.remove(minuendAppTerm);
						subtrahendTemp.remove(factor);
						break;
					}

				}
				minuendParams = new ArrayList<>(minuendQueue);
				subtrahendParams = new ArrayList<>(subtrahendTemp);
			}
			if (minuendAppTerm.getFunction().getName().equals("+")
					&& !subtrahendAppTerm.getFunction().getName().equals("+")) {
				final Deque<Term> minuendQueue = new ArrayDeque<>();
				final Deque<Term> minuendTemp = new ArrayDeque<>();
				minuendQueue.addAll(minuendParams);
				minuendTemp.addAll(minuendParams);
				final Deque<Term> subtrahendQueue = new ArrayDeque<>();
				subtrahendQueue.add(subtrahendAppTerm);
				while (!minuendQueue.isEmpty()) {
					final Term factor = minuendQueue.pop();
					if (checkTermEquiv(script, factor, subtrahendAppTerm)) {
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
	 * Reduces a division of dividend / divisor.
	 *
	 * @param script
	 * @param dividend
	 * @param divisor
	 * @return
	 */
	public static Pair<Term, Term> reduceRealDivision(final ManagedScript script, final Term dividend,
			final Term divisor) {
		final Term one = script.getScript().decimal("1");
		Term simplifiedDividend = dividend;
		Term simplifiedDivisor = divisor;
		while (true) {
			final Term simplifiedDividendPre = simplifiedDividend;
			if (simplifiedDividend instanceof ApplicationTerm && simplifiedDivisor instanceof ApplicationTerm) {
				final ApplicationTerm dividendAppTerm = (ApplicationTerm) simplifiedDividend;
				final ApplicationTerm divisorAppTerm = (ApplicationTerm) simplifiedDivisor;
				if (dividendAppTerm.getFunction().getName().equals("*")
						&& divisorAppTerm.getFunction().getName().equals("*")) {
					final List<Term> paramsDividend = getApplicationTermMultiplicationParams(script, dividendAppTerm);
					final List<Term> paramsDivisor = getApplicationTermMultiplicationParams(script, divisorAppTerm);
					final List<Term> reducedParamsDividend = new ArrayList<>(paramsDividend);
					final List<Term> reducedParamsDivisor = new ArrayList<>(paramsDivisor);
					for (final Term dividendFactor : paramsDividend) {
						for (final Term divisorFactor : paramsDivisor) {
							if (checkTermEquiv(script, dividendFactor, divisorFactor)) {
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
				if (dividendAppTerm.getFunction().getName().equals("*")
						&& !(divisorAppTerm.getFunction().getName().equals("*"))) {
					final List<Term> paramsDividend = getApplicationTermMultiplicationParams(script, dividendAppTerm);
					final List<Term> reducedParamsDividend = new ArrayList<>(paramsDividend);
					final List<Term> reducedParamsDivisor = new ArrayList<>();
					reducedParamsDivisor.add(divisorAppTerm);
					for (final Term dividendFactor : paramsDividend) {
						if (checkTermEquiv(script, dividendFactor, divisorAppTerm)) {
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
				if (!(dividendAppTerm.getFunction().getName().equals("*"))
						&& divisorAppTerm.getFunction().getName().equals("*")) {
					final List<Term> paramsDivisor = getApplicationTermMultiplicationParams(script, divisorAppTerm);
					final List<Term> reducedParamsDividend = new ArrayList<>();
					final List<Term> reducedParamsDivisor = new ArrayList<>(paramsDivisor);
					reducedParamsDividend.add(dividendAppTerm);
					for (final Term divisorFactor : paramsDivisor) {
						if (checkTermEquiv(script, divisorFactor, dividendAppTerm)) {
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
			if (simplifiedDividend instanceof ApplicationTerm && !(simplifiedDivisor instanceof ApplicationTerm)) {
				final ApplicationTerm dividendAppTerm = (ApplicationTerm) simplifiedDividend;
				if (dividendAppTerm.getFunction().getName().equals("*")) {
					final Set<Term> simplifiedDividendParamSet =
							new HashSet<>(Arrays.asList(dividendAppTerm.getParameters()));
					for (final Term dividendFactor : dividendAppTerm.getParameters()) {
						if (checkTermEquiv(script, dividendFactor, simplifiedDivisor)) {
							simplifiedDividendParamSet.remove(dividendFactor);
							simplifiedDivisor = one;
						}
					}
					final Term[] dividendArray =
							simplifiedDividendParamSet.toArray(new Term[simplifiedDividendParamSet.size()]);
					simplifiedDividend = SmtUtils.mul(script.getScript(), "*", dividendArray);
				}
			}
			if (!(simplifiedDividend instanceof ApplicationTerm) && simplifiedDivisor instanceof ApplicationTerm) {
				final ApplicationTerm divisorAppTerm = (ApplicationTerm) simplifiedDivisor;
				if (divisorAppTerm.getFunction().getName().equals("*")) {
					final Set<Term> simplifiedDivisorParamSet =
							new HashSet<>(Arrays.asList(divisorAppTerm.getParameters()));
					for (final Term divisorFactor : divisorAppTerm.getParameters()) {
						if (checkTermEquiv(script, divisorFactor, simplifiedDividend)) {
							simplifiedDividend = one;
							simplifiedDivisorParamSet.remove(divisorFactor);
						}
					}
					final Term[] divisorArray =
							simplifiedDivisorParamSet.toArray(new Term[simplifiedDivisorParamSet.size()]);
					simplifiedDivisor = SmtUtils.mul(script.getScript(), "*", divisorArray);

				}
			}
			if (checkTermEquiv(script, simplifiedDividendPre, simplifiedDividend)) {
				break;
			}
		}
		return new Pair<>(simplifiedDividend, simplifiedDivisor);
	}

	/**
	 * Get the paramters of an Application Term.
	 *
	 * @param script
	 * @param appTerm
	 * @return
	 */
	public static List<Term> getApplicationTermMultiplicationParams(final ManagedScript script, final Term appTerm) {
		final List<Term> params = new ArrayList<>();
		if (appTerm instanceof ApplicationTerm) {
			if (((ApplicationTerm) appTerm).getFunction().getName().equals("*")) {
				for (final Term param : ((ApplicationTerm) appTerm).getParameters()) {
					if (param instanceof ApplicationTerm
							&& ((ApplicationTerm) param).getFunction().getName().equals("*")) {
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
	 * Get parameters of the special case of Application term: The sum.
	 *
	 * @param appTerm
	 * @return
	 */
	public static List<Term> getApplicationTermSumParams(final ApplicationTerm appTerm) {
		final List<Term> params = new ArrayList<>();
		if (appTerm.getFunction().getName().equals("+")) {
			for (final Term param : appTerm.getParameters()) {
				if (param instanceof ApplicationTerm && ((ApplicationTerm) param).getFunction().getName().equals("+")) {
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
	 * @param col
	 * @return
	 */
	private int findPivot(final Term[][] matrix, final int col) {
		int maxRow = -1;
		for (int row = col; row < matrix.length; row++) {
			if (!checkTermEquiv(mScript, matrix[row][col], mZero)) {
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
	private Map<Term, Term> getUpdates(final UnmodifiableTransFormula transitionFormula, final BaseType baseType) {
		final Map<Term, Term> assignments = new HashMap<>();
		final Map<Term, Term> realTvs = new HashMap<>();
		final HashMap<IProgramVar, Term> realUpdates = new HashMap<>();
		final SimultaneousUpdate su;
		try {
			su = SimultaneousUpdate.fromTransFormula(transitionFormula, mScript);
		} catch (final Exception e) {
			throw new UnsupportedOperationException("Could not compute Simultaneous Update!");
		}
		/*
		 * Create a new real sort termvariable.
		 */
		final Map<IProgramVar, Term> updates = su.getDeterministicAssignment();
		for (final IProgramVar pv : updates.keySet()) {
			realTvs.put(pv.getTermVariable(), mScript.constructFreshTermVariable(pv.getGloballyUniqueId() + "_real",
					SmtSortUtils.getRealSort(mScript)));
		}
		/*
		 * Transform the updates to variables to real sort.
		 */
		final SubstitutionWithLocalSimplification subTv = new SubstitutionWithLocalSimplification(mScript, realTvs);
		for (final Entry<IProgramVar, Term> update : updates.entrySet()) {
			final Term intUpdate = update.getValue();
			final Term realUpdate = subTv.transform(intUpdate);
			realUpdates.put(update.getKey(), realUpdate);
		}
		for (final Entry<IProgramVar, Term> varUpdate : realUpdates.entrySet()) {
			final IProgramVar progVar = varUpdate.getKey();
			final Term varUpdateTerm = varUpdate.getValue();
			final HashMap<Term, Term> subMappingTerm = new HashMap<>();
			Term realTerm;
			if (varUpdateTerm instanceof ApplicationTerm) {
				final ApplicationTerm varUpdateAppterm = (ApplicationTerm) varUpdateTerm;
				subMappingTerm.putAll(appTermToReal(varUpdateAppterm));
				final SubstitutionWithLocalSimplification subTerm =
						new SubstitutionWithLocalSimplification(mScript, subMappingTerm);
				realTerm = subTerm.transform(varUpdateAppterm);
			} else if (varUpdateTerm instanceof ConstantTerm) {
				final Rational value = SmtUtils.toRational((ConstantTerm) varUpdateTerm);
				realTerm = value.toTerm(SmtSortUtils.getRealSort(mScript));
			} else {
				realTerm = realTvs.get(progVar.getTermVariable());
			}
			if (baseType == BaseType.ADDITIONS) {
				final Term realVar = realTvs.get(progVar.getTermVariable());
				realTerm = SmtUtils.minus(mScript.getScript(), realTerm, realVar);
			}
			assignments.put(realTvs.get(progVar.getTermVariable()), realTerm);
		}
		return assignments;
	}

	/**
	 * Converts a give application term to real sort.
	 *
	 * @param appTerm
	 * @return
	 */
	private Map<Term, Term> appTermToReal(final ApplicationTerm appTerm) {
		final Map<Term, Term> subMap = new HashMap<>();
		for (final Term param : appTerm.getParameters()) {
			if (param.getSort() == SmtSortUtils.getRealSort(mScript)) {
				continue;
			}
			if (param instanceof ConstantTerm) {
				final ConstantTerm paramConst = (ConstantTerm) param;
				final Rational paramValue = (Rational) paramConst.getValue();
				subMap.put(param, paramValue.toTerm(SmtSortUtils.getRealSort(mScript)));
			} else {
				subMap.putAll(appTermToReal((ApplicationTerm) param));
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
	private Term[][] constructBaseMatrix(final Map<Term, Term> updates,
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

		final Deque<Set<Term>> zeroStack = new HashDeque<>();
		zeroStack.addAll(powerset);
		int j = 0;
		final TermVariable a = mScript.constructFreshTermVariable("a", SmtSortUtils.getRealSort(mScript));
		while (!zeroStack.isEmpty()) {
			int i = 0;
			baseMatrix[j][columnDimension] = a;
			final Map<Term, Term> subMapping = new HashMap<>();
			if (j > 0) {
				final Set<Term> toBeSetZero = zeroStack.pop();
				for (final Term tv : toBeSetZero) {
					subMapping.put(tv, mZero);
				}
			}
			for (final Entry<Term, Term> update : updates.entrySet()) {
				final Term updateTerm = update.getValue();
				Term toBeUpdated;
				final SubstitutionWithLocalSimplification sub =
						new SubstitutionWithLocalSimplification(mScript, subMapping);
				toBeUpdated = sub.transform(updateTerm);
				final SubstitutionWithLocalSimplification subReal =
						new SubstitutionWithLocalSimplification(mScript, intToReal);
				final Term toBeUpdatedReal = subReal.transform(toBeUpdated);

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
	private Term constructBaseFormula(final Map<TermVariable, Set<Term>> updates,
			final UnmodifiableTransFormula transitionFormula, final BaseType baseType) {
		int sCount = 0;
		final Set<Term> newUpdates = new HashSet<>();
		for (final var variableUpdate : updates.entrySet()) {
			final TermVariable s = mScript.constructFreshTermVariable("s" + sCount, SmtSortUtils.getRealSort(mScript));
			for (final Term update : variableUpdate.getValue()) {
				final Term mult = SmtUtils.mul(mScript.getScript(), "*", s, update);
				newUpdates.add(mult);
			}
			sCount++;
		}
		Term addition = mScript.getScript().decimal("1");
		for (final Term update : newUpdates) {
			addition = SmtUtils.sum(mScript.getScript(), "+", addition, update);
		}
		addition = SmtUtils.equality(mScript.getScript(), addition,
				mScript.constructFreshTermVariable("a", SmtSortUtils.getRealSort(mScript)));
		return addition;
	}

	/**
	 * Print the given matrix in readable form.
	 *
	 * @param matrix
	 */
	private void printMatrix(final Term[][] matrix) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Matrix: ");
			for (int i = 0; i < matrix.length; i++) {
				mLogger.debug(Arrays.toString(matrix[i]));
			}
		}
	}

}
