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

import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
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
	private final ILogger mLogger;

	private enum BaseType {
		RESETS, ADDITIONS
	};

	/**
	 * Computes a Q-Vasr-abstraction (S, V), with linear simulation matrix S and Q-Vasr V. A transition formula can be
	 * overapproximated using a Q-Vasr-abstraction.
	 *
	 * @param script
	 * @param logger
	 */
	public QvasrAbstractor(final ManagedScript script, final ILogger logger) {
		mScript = script;
		mLogger = logger;
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

		final Map<TermVariable, Set<Term>> updatesInFormulaAdditions =
				getUpdates(transitionTerm, transitionFormula, BaseType.ADDITIONS);
		final Map<TermVariable, Set<Term>> updatesInFormulaResets =
				getUpdates(transitionTerm, transitionFormula, BaseType.RESETS);

		final Term[][] newUpdatesMatrixResets =
				constructBaseMatrix(updatesInFormulaResets, transitionFormula, BaseType.RESETS);

		final Term[][] newUpdatesMatrixAdditions =
				constructBaseMatrix(updatesInFormulaAdditions, transitionFormula, BaseType.ADDITIONS);

		final Rational[][] out = new Rational[2][2];
		final Qvasr qvasr = null;
		return new QvasrAbstraction(out, qvasr);
	}

	/**
	 * Find Updates to variables in the transition formula. Needed to construct a linear system of equations to compute
	 * bases of resets and increments for the Q-Vasr-abstraction.
	 *
	 * @param transitionTerm
	 * @param outVariables
	 * @return
	 */
	private Map<TermVariable, Set<Term>> getUpdates(final Term transitionTerm,
			final UnmodifiableTransFormula transitionFormula, final BaseType baseType) {
		final Map<TermVariable, Set<Term>> assignments = new HashMap<>();
		final ApplicationTermFinder applicationTermFinder = new ApplicationTermFinder("=", false);
		for (final TermVariable outVar : transitionFormula.getOutVars().values()) {
			final Set<TermVariable> out = new HashSet<>();
			out.add(outVar);
			final Term filtered = SmtUtils.filterFormula(transitionTerm, out, mScript.getScript());
			final Set<ApplicationTerm> varAssignment = applicationTermFinder.findMatchingSubterms(filtered);
			final Set<Term> trueAssignment = new HashSet<>();
			for (final ApplicationTerm app : varAssignment) {
				for (Term param : app.getParameters()) {
					if (!(param instanceof TermVariable) || (param instanceof TermVariable && param != outVar)) {
						if (baseType == BaseType.ADDITIONS) {
							final IProgramVar programVar =
									(IProgramVar) TransFormulaUtils.getProgramVarForTerm(transitionFormula, outVar);
							if (transitionFormula.getInVars().containsKey(programVar)) {
								final TermVariable inVar = transitionFormula.getInVars().get(programVar);
								param = SmtUtils.sum(mScript.getScript(), "+", param,
										SmtUtils.neg(mScript.getScript(), inVar));
							} else {
								param = SmtUtils.sum(mScript.getScript(), "+", param,
										SmtUtils.neg(mScript.getScript(), outVar));
							}
						}
						trueAssignment.add(param);
					}
				}
			}
			assignments.put(outVar, trueAssignment);
		}
		return assignments;
	}

	/**
	 * Construct a matrix representing a set of linear equations that model updates to variables in a given transition
	 * formula. The matrix has 2^#outVariables columns because we have to set each variable to 0 to be able to use
	 * Gaussian elimination.
	 *
	 * @param updates
	 * @param transitionFormula
	 * @param typeOfBase
	 * @return
	 */
	private Term[][] constructBaseMatrix(final Map<TermVariable, Set<Term>> updates,
			final UnmodifiableTransFormula transitionFormula, final BaseType baseType) {
		final int rowDimension = (int) Math.pow(2, transitionFormula.getInVars().size());
		final int columnDimension = transitionFormula.getOutVars().size() + 1;
		final Term[][] baseMatrix = new Term[rowDimension][columnDimension];

		final Set<Set<TermVariable>> setToZero = new HashSet<>();
		for (final TermVariable tv : transitionFormula.getInVars().values()) {
			final Set<TermVariable> inVar = new HashSet<>();
			inVar.add(tv);
			setToZero.add(inVar);
		}
		Set<Set<TermVariable>> powerset = new HashSet<>(setToZero);
		for (final Set<TermVariable> inTv : setToZero) {
			powerset = QvasrUtils.joinSet(powerset, inTv);
		}
		final Deque<Set<TermVariable>> zeroStack = new HashDeque<>();
		zeroStack.addAll(powerset);
		int j = 0;
		final TermVariable a = mScript.constructFreshTermVariable("a", SmtSortUtils.getRealSort(mScript));
		while (!zeroStack.isEmpty()) {
			int i = 0;
			baseMatrix[j][columnDimension - 1] = a;
			final Map<Term, Term> subMapping = new HashMap<>();
			if (j > 0) {
				final Set<TermVariable> toBeSetZero = zeroStack.pop();
				for (final TermVariable tv : toBeSetZero) {
					subMapping.put(tv, mScript.getScript().numeral("0"));
				}
			}
			for (final Set<Term> update : updates.values()) {
				for (final Term updateTerm : update) {
					Term toBeUpdated;
					final Substitution sub = new Substitution(mScript, subMapping);
					toBeUpdated = sub.transform(updateTerm);
					baseMatrix[j][i] = toBeUpdated;
				}
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
	private Set<Term> constructBaseFormula(final Map<TermVariable, Set<Term>> updates,
			final UnmodifiableTransFormula transitionFormula, final BaseType baseType) {
		int sCount = 0;
		final Set<Term> newUpdates = new HashSet<>();
		for (final var variableUpdate : updates.entrySet()) {
			// TODO: Don't we need a float/rational here instead of intSort?
			final TermVariable s = mScript.constructFreshTermVariable("s" + sCount, SmtSortUtils.getIntSort(mScript));
			for (final Term update : variableUpdate.getValue()) {
				final Term mult = SmtUtils.mul(mScript.getScript(), "*", s, update);
				newUpdates.add(mult);
			}
			sCount++;
		}
		return newUpdates;
	}
}
