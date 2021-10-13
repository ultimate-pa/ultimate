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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

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

		final Map<TermVariable, Set<Term>> updatesInFormula = getUpdates(transitionTerm, transitionFormula);
		final Set<Term> newUpdates = constructBaseFormula(updatesInFormula, transitionTerm, transitionFormula, "");
		final Term[][] newUpdatesMatrix = constructBaseMatrix(updatesInFormula, transitionTerm, transitionFormula, "");

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
			final UnmodifiableTransFormula transitionFormula) {
		final Map<TermVariable, Set<Term>> assignments = new HashMap<>();
		final ApplicationTermFinder applicationTermFinder = new ApplicationTermFinder("=", false);
		for (final TermVariable outVar : transitionFormula.getOutVars().values()) {
			final Set<TermVariable> out = new HashSet<>();
			out.add(outVar);
			final Term filtered = SmtUtils.filterFormula(transitionTerm, out, mScript.getScript());
			final Set<ApplicationTerm> varAssignment = applicationTermFinder.findMatchingSubterms(filtered);
			final Set<Term> trueAssignment = new HashSet<>();
			for (final ApplicationTerm app : varAssignment) {
				for (final Term param : app.getParameters()) {
					if (!(param instanceof TermVariable) || (param instanceof TermVariable && param != outVar)) {
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
	 * @param transitionTerm
	 * @param transitionFormula
	 * @param typeOfBase
	 * @return
	 */
	private Term[][] constructBaseMatrix(final Map<TermVariable, Set<Term>> updates, final Term transitionTerm,
			final UnmodifiableTransFormula transitionFormula, final String typeOfBase) {
		final int rowDimension = (int) Math.pow(2, transitionFormula.getOutVars().size());
		final int columnDimension = transitionFormula.getOutVars().size();
		final Term[][] baseMatrix = new Term[rowDimension][columnDimension];

		for (int j = 0; j < rowDimension; j++) {
			int i = 0;
			for (final Set<Term> update : updates.values()) {
				for (final Term updateTerm : update) {
					baseMatrix[j][i] = updateTerm;
					// TODO!
					/*
					 * for (final Term updateTerm : update) { for (final TermVariable inVar :
					 * transitionFormula.getInVars().values()) { final Set<TermVariable> tv = new HashSet<>();
					 * tv.add(inVar); final Map<TermVariable, Term> replaceTermVars = new HashMap<>();
					 * replaceTermVars.put(inVar, mScript.getScript().numeral("0")); final Substitution sub = new
					 * Substitution(mScript, replaceTermVars); final Term newUpdate = sub.transform(updateTerm);
					 * mLogger.debug(""); }
					 *
					 * for (int i = 0; i < rowDimension; i++) { baseMatrix[i][j] = updateTerm; }
					 */
				}
				i++;
			}
		}
		return baseMatrix;
	}

	/**
	 * Construct a formula modeling updates to variables done in a transition formula in relation to a new termvariable
	 * s. (May not be needed, as we can skip this construction)
	 *
	 * @param updates
	 * @param transitionTerm
	 * @param transitionFormula
	 * @param typeOfBase
	 * @return
	 */
	private Set<Term> constructBaseFormula(final Map<TermVariable, Set<Term>> updates, final Term transitionTerm,
			final UnmodifiableTransFormula transitionFormula, final String typeOfBase) {
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
