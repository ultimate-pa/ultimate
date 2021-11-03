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

import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
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

		final Term[][] gaussedAdditions = gaussPartialPivot(newUpdatesMatrixAdditions);
		printMatrix(gaussedAdditions);
		final Term[][] gaussedAdditionsOnes = gaussRowEchelonForm(gaussedAdditions);
		printMatrix(gaussedAdditionsOnes);
		final Term[] solutions = backSub(gaussedAdditionsOnes);

		final Term[][] gaussedResets = gaussPartialPivot(newUpdatesMatrixResets);
		printMatrix(gaussedResets);
		final Term[][] gaussedResetsOnes = gaussRowEchelonForm(gaussedResets);
		printMatrix(gaussedResetsOnes);
		final Term[] solutionsResets = backSub(gaussedResetsOnes);

		final Rational[][] out = new Rational[2][2];
		final Qvasr qvasr = null;
		return new QvasrAbstraction(out, qvasr);
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
				if (!SmtUtils.areFormulasEquivalent(matrix[i][j], mScript.getScript().decimal("0"),
						mScript.getScript())) {

					final IPolynomialTerm divider = PolynomialTermOperations.convert(mScript.getScript(), matrix[i][j]);
					// matrix[i][j] = mScript.getScript().decimal("1");
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
	private Term[][] gaussRowEchelonForm(final Term[][] matrix) {
		for (int i = 0; i < matrix.length; i++) {
			for (int j = 0; j < matrix[0].length; j++) {
				if (!SmtUtils.areFormulasEquivalent(matrix[i][j], mScript.getScript().decimal("0"),
						mScript.getScript())) {
					final Term divider = matrix[i][j];
					// matrix[i][j] = mScript.getScript().decimal("1");
					for (int k = j; k < matrix[0].length; k++) {
						final Term toBeDivided = matrix[i][k];
						final Term division =
								simplifyRealDivision(toBeDivided, divider, mScript.getScript().decimal("1"));
						if (mLogger.isDebugEnabled()) {
							mLogger.debug("Matrix " + i + k + " =  " + division.toStringDirect());
						}
						// final Term division = SmtUtils.divReal(mScript.getScript(), toBeDivided, divider);
						matrix[i][k] = division;
					}
					break;
				}
			}
		}
		return matrix;
	}

	/**
	 * TODO
	 *
	 * @param matrix
	 * @return
	 */
	private Term[] backSub(final Term[][] matrix) {
		final Term[] solutions = new Term[matrix[0].length];
		for (int k = 0; k < matrix[0].length; k++) {
			solutions[k] = mScript.getScript().decimal("0");
		}
		final int columns = matrix[0].length - 1;
		final int solCounter = columns;
		for (int i = matrix.length - 1; 0 <= i; i--) {
			solutions[solCounter] = matrix[i][columns];
			for (int j = 0; j < columns - 1; j++) {
				final Term mul = SmtUtils.mul(mScript.getScript(), "*", matrix[i][j], solutions[j]);
				final Term sub = SmtUtils.minus(mScript.getScript(), solutions[solCounter], mul);
				solutions[solCounter] = sub;
			}
		}
		return solutions;
	}

	/**
	 * Bring a given matrix into upper triangle form.
	 *
	 * @param matrix
	 * @return
	 */
	private Term[][] gaussPartialPivot(Term[][] matrix) {
		for (int k = 0; k < matrix.length - 1; k++) {
			int max = 0;
			if ((k + 1) < matrix.length) {
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
				// matrix[i][k] = mScript.getScript().decimal("0");
				final Term newDiv = SmtUtils.divReal(mScript.getScript(), toBeEliminated, pivot);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Divide: " + matrix[i][k].toString() + " by " + matrix[k][k].toString() + "\n"
							+ newDiv.toStringDirect());
				}
				// k is the column
				for (int j = k; j < matrix[0].length; j++) {
					final Term currentColumn = matrix[k][j];
					final Term newMul = simplifyRealDivision(toBeEliminated, pivot, currentColumn);
					final Term newSub = SmtUtils.minus(mScript.getScript(), matrix[i][j], newMul);
					if (mLogger.isDebugEnabled()) {
						mLogger.debug(" ");
						mLogger.debug("Matrix: " + i + " " + j + "   " + matrix[i][j].toStringDirect());
						mLogger.debug("Division: " + newDiv.toStringDirect());
						mLogger.debug("Times: " + currentColumn.toStringDirect());
						mLogger.debug("Multiplication: " + newMul.toStringDirect());
						mLogger.debug("Result: " + newSub.toStringDirect());
						mLogger.debug(" ");
					}
					matrix[i][j] = newSub;
				}
			}
			mLogger.debug("Gauss done?");
		}
		return matrix;
	}

	private final Term simplifyRealDivision(final Term dividend, final Term divisor, final Term mult) {
		if (SmtUtils.areFormulasEquivalent(divisor, mScript.getScript().decimal("0"), mScript.getScript())) {
			throw new UnsupportedOperationException("cannot divide by 0!");
		}
		if (SmtUtils.areFormulasEquivalent(divisor, mScript.getScript().decimal("1"), mScript.getScript())) {
			return mScript.getScript().term("*", dividend, mult);
		}
		if (SmtUtils.areFormulasEquivalent(dividend, mScript.getScript().decimal("0"), mScript.getScript())) {
			return mScript.getScript().decimal("0");
		}
		if (SmtUtils.areFormulasEquivalent(dividend, divisor, mScript.getScript())) {
			return mScript.getScript().term("*", mScript.getScript().decimal("1"), mult);
		}
		if (SmtUtils.areFormulasEquivalent(mult, divisor, mScript.getScript())) {
			return dividend;
		}
		final Term div = SmtUtils.divReal(mScript.getScript(), dividend, divisor);
		return SmtUtils.mul(mScript.getScript(), "*", div, mult);
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
			if (!SmtUtils.areFormulasEquivalent(matrix[row][col], mScript.getScript().decimal("0"),
					mScript.getScript())) {
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
		final int rowDimension = (int) Math.pow(2, transitionFormula.getInVars().size());
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
		final Term[][] baseMatrix = new Term[powerset.size() + 2][columnDimension + 1];
		for (final Set<Term> inTv : setToZero) {
			powerset = QvasrUtils.joinSet(powerset, inTv);
		}
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
					subMapping.put(tv, mScript.getScript().decimal("0"));
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
		mLogger.debug("Matrix: ");
		for (int i = 0; i < matrix.length; i++) {
			mLogger.debug(Arrays.toString(matrix[i]));
		}
	}
}
