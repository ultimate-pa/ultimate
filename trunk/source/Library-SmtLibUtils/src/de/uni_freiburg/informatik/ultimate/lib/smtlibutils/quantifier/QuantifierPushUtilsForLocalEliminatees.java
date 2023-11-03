/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.FormulaClassification;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils.IQuantifierEliminator;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Provides static methods that are utilized by the
 * {@link QuantifierPushTermWalker}. Methods in this class are focused on "local
 * eliminatees". We call an eliminatee "local for a dualFiniteJunction" if it
 * occurs only in a single dualFiniteJunct.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierPushUtilsForLocalEliminatees {

	/**
	 * We call an eliminatee "local for a dualFiniteJunction" if it occurs only in a
	 * single dualFiniteJunct. This method takes a dualFiniteJunction and
	 * iteratively pushes sets of local eliminatees over dualFiniteJuncts that are
	 * correspondingFiniteJunctions.
	 */
	public static Term pushLocalEliminateesOverCorrespondingFiniteJunction(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask et,
			final IQuantifierEliminator qe) {
		Term[] currentDualFiniteJuncts = QuantifierUtils.getDualFiniteJuncts(et.getQuantifier(), et.getTerm());
		if (currentDualFiniteJuncts.length <= 1) {
			throw new AssertionError(QuantifierPushUtils.NOT_DUAL_FINITE_CONNECTIVE);
		}
		Pair<Term, Set<TermVariable>> qualifiedDualJunct2LocalEliminatees = findSomePushableLocalEliminateeSet(et);
		EliminationTask currentEt = et;
		int iterations = 0;
		while (qualifiedDualJunct2LocalEliminatees != null) {
			final Set<TermVariable> localEliminatees = qualifiedDualJunct2LocalEliminatees.getSecond();
			final Set<TermVariable> otherEliminatess = new LinkedHashSet<>(currentEt.getEliminatees());
			otherEliminatess.removeAll(localEliminatees);
			final Context context = currentEt.getContext().constructChildContextForQuantifiedFormula(
					mgdScript.getScript(), new ArrayList<>(otherEliminatess));
			final Term tmp = pushLocalEliminateeSetToDualJunct(services, mgdScript, applyDistributivity, pqeTechniques,
					simplificationTechnique, currentEt.getQuantifier(), currentEt.getTerm(),
					qualifiedDualJunct2LocalEliminatees, context, qe);
			otherEliminatess.retainAll(Arrays.asList(tmp.getFreeVars()));
			if (otherEliminatess.isEmpty()) {
				return tmp;
			}
			// 20200407 Matthias: Maybe we should simplify the whole dualJunction here,
			// however in a experiment simplification here was not helpful.
			currentEt = new EliminationTask(currentEt.getQuantifier(), otherEliminatess, tmp, currentEt.getContext());
			currentDualFiniteJuncts = QuantifierUtils.getDualFiniteJuncts(currentEt.getQuantifier(), tmp);
			if (currentDualFiniteJuncts.length <= 1) {
				return currentEt.toTerm(mgdScript.getScript());
			}
			qualifiedDualJunct2LocalEliminatees = findSomePushableLocalEliminateeSet(currentEt);
			iterations++;
		}
		if (iterations == 0) {
			// no push possible
			return null;
		} else {
			return currentEt.toTerm(mgdScript.getScript());
		}
	}

	/**
	 * We call an eliminatee "local for a dualFiniteJunction" if it occurs only in a
	 * single dualFiniteJunct. This method takes a dualFiniteJunction and one
	 * dualFinitJunct that is a correspondingFiniteJunction together with a set of
	 * local eliminatees and pushes the local eliminatees over the
	 * correspondingFiniteJunct.
	 */
	private static Term pushLocalEliminateeSetToDualJunct(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final int quantifier, final Term dualFiniteJunction,
			final Pair<Term, Set<TermVariable>> dualJunctEliminateesPair, final Context context,
			final IQuantifierEliminator qe) {
		final Term[] dualFiniteJuncts = QuantifierUtils.getDualFiniteJuncts(quantifier, dualFiniteJunction);
		if (dualFiniteJuncts.length <= 1) {
			throw new AssertionError(QuantifierPushUtils.NOT_DUAL_FINITE_CONNECTIVE);
		}
		final int i = Arrays.asList(dualFiniteJuncts).indexOf(dualJunctEliminateesPair.getFirst());
		final Term ithTermQuantified = SmtUtils.quantifier(mgdScript.getScript(), quantifier,
				dualJunctEliminateesPair.getSecond(), dualJunctEliminateesPair.getFirst());
		final Context childContextForIthTerm = context.constructChildContextForConDis(services, mgdScript,
				((ApplicationTerm) dualFiniteJunction).getFunction(), Arrays.asList(dualFiniteJuncts), i);
		final Term ithTermPushed = qe.eliminate(services, mgdScript, applyDistributivity, pqeTechniques,
				simplificationTechnique, childContextForIthTerm, ithTermQuantified);
		final List<Term> resultDualJuncts = new ArrayList<>(Arrays.asList(dualFiniteJuncts));
		resultDualJuncts.set(i, ithTermPushed);
		return QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(), quantifier, resultDualJuncts);
	}

	/**
	 * We call an eliminatee "local for a dualFiniteJunction" if it occurs only in a
	 * single dualFiniteJunct. This method takes an {@link EliminationTask} over a
	 * dualFiniteJunction and returns some dualFiniteJunct that is a
	 * correspondingFiniteJunction and all its local eliminatees. The method returns
	 * null if no dualFiniteJunct has local eliminatees.
	 */
	static Pair<Term, Set<TermVariable>> findSomePushableLocalEliminateeSet(final EliminationTask et) {
		final Term[] dualFiniteJuncts = QuantifierUtils.getDualFiniteJuncts(et.getQuantifier(), et.getTerm());
		assert dualFiniteJuncts.length > 1 : QuantifierPushUtils.NOT_DUAL_FINITE_CONNECTIVE;
		final HashRelation<TermVariable, Term> eliminatee2DualJuncts = new HashRelation<>();
		for (final Term dualJunct : dualFiniteJuncts) {
			final Set<TermVariable> freeVars = new HashSet<>(Arrays.asList(dualJunct.getFreeVars()));
			for (final TermVariable eliminatee : et.getEliminatees()) {
				if (freeVars.contains(eliminatee)) {
					eliminatee2DualJuncts.addPair(eliminatee, dualJunct);
				}
			}
		}
		final HashRelation<Term, TermVariable> dualJunct2LocalEliminatees = new HashRelation<>();
		// do not iterate over the HashRelation because the order is not deterministic
		for (final TermVariable eliminatee : et.getEliminatees()) {
			final Set<Term> dualJunctsOfEliminatee = eliminatee2DualJuncts.getImage(eliminatee);
			assert !dualJunctsOfEliminatee.isEmpty();
			if (dualJunctsOfEliminatee.size() == 1) {
				final Term dualJunct = dualJunctsOfEliminatee.iterator().next();
				final FormulaClassification classification = QuantifierPusher.classify(et.getQuantifier(), dualJunct);
				switch (classification) {
				case ATOM:
					// do nothing, atoms could have been already handled by the elimination
					// techniques that were applied to the dual finite junction
					break;
				case CORRESPONDING_FINITE_CONNECTIVE:
					// would allow us to push the quantifier(s) further more
					dualJunct2LocalEliminatees.addPair(dualJunct, eliminatee);
					break;
				case DUAL_FINITE_CONNECTIVE:
					throw new AssertionError("Dual finite connective not flattened");
				case DUAL_QUANTIFIER:
					// do nothing, no chance to push
					break;
				case NOT_QUANTIFIED:
					throw new AssertionError("Illegal for the call above");
				case SAME_QUANTIFIER:
					throw new AssertionError("Quantifier not flattened");
				default:
					throw new AssertionError("Unknown value: " + classification);
				}
			}
		}
		if (dualJunct2LocalEliminatees.isEmpty()) {
			return null;
		} else {
			// get some element but
			// do not iterate over the HashRelation because the order is not deterministic
			for (final Term dualFiniteJunct : dualFiniteJuncts) {
				final Set<TermVariable> eliminatees = dualJunct2LocalEliminatees.getImage(dualFiniteJunct);
				if (!eliminatees.isEmpty()) {
					return new Pair<>(dualFiniteJunct, eliminatees);
				}
			}
		}
		throw new AssertionError("HashRelation must contain at least one element.");
	}
}
