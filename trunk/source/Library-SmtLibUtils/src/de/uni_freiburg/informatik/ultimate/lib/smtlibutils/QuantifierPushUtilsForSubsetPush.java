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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierUtils.IQuantifierEliminator;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.EliminationTask;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.ParameterPartition;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Provides static methods that are utilized by the
 * {@link QuantifierPushTermWalker}. Methods in this class are focused the
 * elimination for dualFiniteJunctions. If an elimination is costly, we
 * sometimes what to apply the elimination only to a subset of the
 * dualFiniteJuncts.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierPushUtilsForSubsetPush {

	/**
	 * Auxiliary method for quantifier elimination. <br />
	 * <ul>
	 * <li>Motivation: One single application of distributivity doubles the size of
	 * the current formula. If we can apply distributivity only to a subformula this
	 * blow-up will be smaller.
	 * <li>Idea: Select one eliminatee and all dualJuncts in which the eliminatee
	 * occurs. (Omit eliminatees that occur in all dualJuncts) Apply the algorithm
	 * recursively to this dualJunction. Continue until one of the following
	 * applies.
	 * <ul>
	 * <li>(1) The root symbol of the whole formula is not a dual junction any more,
	 * e.g., due to simplifications that became possible. (Considered a successful
	 * elimination)
	 * <li>(2) We can now partition the dualJuncts according such that no two
	 * equivalence classes share a common eliminatee. (Considered a successful
	 * elimination)
	 * <li>(3) The elimination failed for all eliminatees that does not occur in all
	 * dualjuncts. (Considered a failed elimination) </ ul><li> Optimization1: Do
	 * not apply the recursive elimination only to the selected eliminatee but also
	 * to its "minion" eliminatees. We call an eliminatee a "minion" of the selected
	 * eliminatee if it occurs only in dualJuncts in which the eliminatee also
	 * occurs.
	 * <li>Optimization2: Do not apply the general quantifier elimination recursively
	 * but only the method that immediately applies the distributivity.
	 * <li>Comment1: This method is useless if we do not apply distributivity.
	 * <li>Problem1: If the recursive call just replaces that names of the
	 * quantified variables we run into an infinite loop. Maybe there a similar more
	 * sophisticated nontermination problems. </ ul>
	 * TODO: What about eliminatee that occur in a single dualjunct?
	 * Have been checked before. But track new ones. Flatten after push
	 *
	 */
	public static Term sequentialSubsetPush(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask et,
			final IQuantifierEliminator qe) {
		List<Term> currentDualFiniteJuncts = Arrays
				.asList(QuantifierUtils.getDualFiniteJunction(et.getQuantifier(), et.getTerm()));
		if (currentDualFiniteJuncts.size() <= 1) {
			throw new AssertionError("No dual finite junction");
		}
		{
			final Pair<Term, Set<TermVariable>> pair = QuantifierPushUtilsForLocalEliminatees
					.findSomePushableLocalEliminateeSet(et);
			if (pair != null) {
				throw new AssertionError("Contains local eliminatees");
			}
		}
		if (!QuantifierPushUtils.isFlattened(et.getQuantifier(), currentDualFiniteJuncts)) {
			throw new AssertionError("Not flattened");
		}
		{
			final ParameterPartition pp = new ParameterPartition(mgdScript.getScript(), et);
			if (!pp.isIsPartitionTrivial()) {
				throw new AssertionError("Is partitionable!");
			}
		}
		List<TermVariable> todoEliminatees = new ArrayList<>(et.getEliminatees());
		List<TermVariable> failedEliminatees = new ArrayList<>();
		// In fact these eliminatees occur also in at least one dualFiniteJunct
		// otherwise the input would not be legal.
		List<TermVariable> todoEliminateesThatDoNotOccurInAllParams = remaningEliminateeThatDoNotOccurInAllParams(
				todoEliminatees, currentDualFiniteJuncts);
		int i = 0;
		while (!todoEliminateesThatDoNotOccurInAllParams.isEmpty()) {
			if (i > 20) {
				currentDualFiniteJuncts.toString();
				throw new AssertionError("Maybe an infinite loop");
			}
			final TermVariable eliminatee = QuantifierPusher.selectBestEliminatee(mgdScript.getScript(),
					et.getQuantifier(), todoEliminateesThatDoNotOccurInAllParams, currentDualFiniteJuncts);
			final PartitionByEliminateeOccurrence parti = new PartitionByEliminateeOccurrence(currentDualFiniteJuncts,
					eliminatee);
			final List<TermVariable> minionEliminatees = QuantifierPusher.determineMinionEliminatees(todoEliminatees,
					parti.getFiniteDualJunctsWithoutEliminatee());
			if (!minionEliminatees.contains(eliminatee)) {
				throw new AssertionError("Missing minion " + eliminatee);
			}
			Term pushed = pushMinionEliminatees(services, mgdScript, applyDistributivity, pqeTechniques,
					simplificationTechnique, et, qe, minionEliminatees, parti, todoEliminatees, failedEliminatees);
			// special case if pushed formula is similar?
			// eliminatee failed, all minions failed?
			if (pushed instanceof QuantifiedFormula) {
				final QuantifiedFormula qf = (QuantifiedFormula) pushed;
				for (final TermVariable var : Arrays.asList(qf.getVariables())) {
					if (minionEliminatees.contains(var)) {
						failedEliminatees.add(var);
					} else {
						todoEliminatees.add(var);
					}
				}
				pushed = qf.getSubformula();
			}
			todoEliminatees.removeAll(minionEliminatees);
			Term currentDualFiniteJunction;
			{
				currentDualFiniteJuncts = new ArrayList<>(parti.getFiniteDualJunctsWithoutEliminatee());
				currentDualFiniteJuncts.add(pushed);
				// building the dualFiniteJunction may simplify the formula
				currentDualFiniteJunction = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(),
						et.getQuantifier(), currentDualFiniteJuncts);
			}
			{
				// simplification may have removed other eliminatees
				final List<TermVariable> freeVars = Arrays.asList(currentDualFiniteJunction.getFreeVars());
				todoEliminatees.retainAll(freeVars);
				failedEliminatees.retainAll(freeVars);
			}
			if (todoEliminatees.isEmpty()) {
				return SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(), failedEliminatees,
						currentDualFiniteJunction);
			}
			currentDualFiniteJuncts = Arrays
					.asList(QuantifierUtils.getDualFiniteJunction(et.getQuantifier(), currentDualFiniteJunction));
			if (!QuantifierPushUtils.isFlattened(et.getQuantifier(), currentDualFiniteJuncts)) {
				// can happen if due to simplification a quantified formula moves towards the
				// root
				// 20220420 TODO: Implement flattening
				throw new UnsupportedOperationException("Unplanned introduction of non-flat quantified formula");
			}
			if (currentDualFiniteJuncts.size() == 1) {
				// in fact not a real dualFiniteJunction any more (possibly dualQuantifier,
				// correspondingConnective, or atom)
				final List<TermVariable> currentEliminatees = new ArrayList<>(todoEliminatees);
				currentEliminatees.addAll(failedEliminatees);
				return SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(), currentEliminatees,
						currentDualFiniteJunction);
			}
			// We deliberately leave out the ParameterPartition since elimination of locals
			// also works also well for partitionable elimination tasks
			final Term localsEliminated;
			{
				final List<TermVariable> currentEliminatees = new ArrayList<>(todoEliminatees);
				currentEliminatees.addAll(failedEliminatees);
				final EliminationTask etForLocalPush = new EliminationTask(et.getQuantifier(),
						new HashSet<>(currentEliminatees), currentDualFiniteJunction, et.getContext());
				localsEliminated = QuantifierPushUtilsForLocalEliminatees
						.pushLocalEliminateesOverCorrespondingFiniteJunction(services, mgdScript, applyDistributivity,
								pqeTechniques, simplificationTechnique, etForLocalPush, qe);

			}
			if (localsEliminated != null) {
				if (localsEliminated instanceof QuantifiedFormula) {
					final QuantifiedFormula qf = (QuantifiedFormula) localsEliminated;
					if (qf.getQuantifier() != et.getQuantifier()) {
						// We eliminated successful, coincidentally the result is also a quantified
						// formula with a different quantifier.
						return localsEliminated;
					}
					final List<TermVariable> oldFailedEliminatees = failedEliminatees;
					todoEliminatees = new ArrayList<>();
					failedEliminatees = new ArrayList<>();
					for (final TermVariable v : qf.getVariables()) {
						if (oldFailedEliminatees.contains(v)) {
							failedEliminatees.add(v);
						} else {
							todoEliminatees.add(v);
						}
					}
					currentDualFiniteJunction = qf.getSubformula();
				} else {
					currentDualFiniteJunction = localsEliminated;
				}
				currentDualFiniteJuncts = Arrays
						.asList(QuantifierUtils.getDualFiniteJunction(et.getQuantifier(), currentDualFiniteJunction));
				if (!QuantifierPushUtils.isFlattened(et.getQuantifier(), currentDualFiniteJuncts)) {
					// can happen if due to simplification a quantified formula moves towards the
					// root
					// 20220420 TODO: Implement flattening
					throw new UnsupportedOperationException("Unplanned introduction of non-flat quantified formula");
				}
				if (currentDualFiniteJuncts.size() == 1) {
					// in fact not a real dualFiniteJunction any more (possibly dualQuantifier,
					// correspondingConnective, or atom)
					final List<TermVariable> currentEliminatees = new ArrayList<>(todoEliminatees);
					currentEliminatees.addAll(failedEliminatees);
					return SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(), currentEliminatees,
							currentDualFiniteJunction);
				}
			}
			{
				final List<TermVariable> currentEliminatees = new ArrayList<>(todoEliminatees);
				currentEliminatees.addAll(failedEliminatees);
				final EliminationTask etForParameterPartitionCheck = new EliminationTask(et.getQuantifier(),
						new HashSet<>(currentEliminatees), currentDualFiniteJunction, et.getContext());
				final ParameterPartition pp = new ParameterPartition(mgdScript.getScript(),
						etForParameterPartitionCheck);
				if (!pp.isIsPartitionTrivial()) {
					return SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(), failedEliminatees,
							pp.getTermWithPushedQuantifier());
				}
			}
			todoEliminateesThatDoNotOccurInAllParams = remaningEliminateeThatDoNotOccurInAllParams(todoEliminatees,
					currentDualFiniteJuncts);
			i++;
		}
		if (i == 0) {
			return null;
		} else {
			final List<TermVariable> currentEliminatees = new ArrayList<>(todoEliminatees);
			currentEliminatees.addAll(failedEliminatees);
			return SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(), currentEliminatees, QuantifierUtils
					.applyDualFiniteConnective(mgdScript.getScript(), et.getQuantifier(), currentDualFiniteJuncts));
		}
	}

	private static Term pushMinionEliminatees(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask et,
			final IQuantifierEliminator qe, final List<TermVariable> minionEliminatees,
			final PartitionByEliminateeOccurrence parti, final List<TermVariable> todoEliminatees,
			final List<TermVariable> failedEliminatees) {
		final Term dualFiniteJunction = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(),
				et.getQuantifier(), parti.getFiniteDualJunctsWithEliminatee());
		final Term quantified = SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(),
				new HashSet<>(minionEliminatees), dualFiniteJunction);
//		if (parti.getFiniteDualJunctsWithEliminatee().size() == 1) {
//			// TODO: Omit this check after we push minions if there is at least one corresponding connective
//			return quantified;
//		}
		final List<TermVariable> nonMinionEliminatees = new ArrayList<>(todoEliminatees);
		nonMinionEliminatees.removeAll(new HashSet<>(minionEliminatees));
		nonMinionEliminatees.addAll(failedEliminatees);
		final Context parentContext = et.getContext();
		Context context = parentContext.constructChildContextForQuantifiedFormula(mgdScript.getScript(),
						nonMinionEliminatees);
		context = context.constructChildContextForConDis(services, mgdScript,
					((ApplicationTerm) et.getTerm()).getFunction(), parti.getFiniteDualJunctsWithoutEliminatee());
//		final EliminationTask currentEt = new EliminationTask((QuantifiedFormula) quantified, context);
//		final Term res = QuantifierPusher.applyDistributivityAndPush(services, mgdScript, pqeTechniques, simplificationTechnique,
//				currentEt, qe, DER_BASED_DISTRIBUTION_PARAMETER_PRESELECTION, EVALUATE_SUCCESS_OF_DISTRIBUTIVITY_APPLICATION);
//		if (res == null) {
//			return quantified;
//		} else {
//			return res;
//		}
		return qe.eliminate(services, mgdScript, applyDistributivity, pqeTechniques, simplificationTechnique,
					context, quantified);
	}

	private static List<TermVariable> remaningEliminateeThatDoNotOccurInAllParams(
			final List<TermVariable> todoEliminatees, final List<Term> currentDualFiniteParams) {
		return todoEliminatees.stream()
				.filter(eliminatee -> currentDualFiniteParams.stream()
						.anyMatch(param -> !Arrays.asList(param.getFreeVars()).contains(eliminatee)))
				.collect(Collectors.toList());
	}

	/**
	 * Class that partitions a list of terms into two lists. One list where a given
	 * TermVariable occurs as a free variable and one list where the given
	 * TermVariable does not occur as a free variable. Terminology and assertions
	 * are fitted to the method {@link QuantifierPushUtilsForSubsetPush#sequentialSubsetPush} in
	 * which this class is used.
	 */
	private static class PartitionByEliminateeOccurrence {

		private final List<Term> mFiniteDualJunctsWithEliminatee;
		private final List<Term> mFiniteDualJunctsWithoutEliminatee;

		public PartitionByEliminateeOccurrence(final List<Term> finiteDualJuncts, final TermVariable eliminatee) {
			final List<Term> finiteDualJunctsWithEliminatee = new ArrayList<>();
			final List<Term> finiteDualJunctsWithoutEliminatee = new ArrayList<>();
			for (final Term dualFiniteJunct : finiteDualJuncts) {
				if (Arrays.asList(dualFiniteJunct.getFreeVars()).contains(eliminatee)) {
					finiteDualJunctsWithEliminatee.add(dualFiniteJunct);
				} else {
					finiteDualJunctsWithoutEliminatee.add(dualFiniteJunct);
				}
			}
			if (finiteDualJunctsWithEliminatee.isEmpty()) {
				throw new AssertionError("Eliminatee must occur in at least one dualfiniteJunct");
			}
			if (finiteDualJunctsWithoutEliminatee.isEmpty()) {
				throw new AssertionError("Eliminatee must not occur all dualfiniteJuncts");
			}

			mFiniteDualJunctsWithEliminatee = finiteDualJunctsWithEliminatee;
			mFiniteDualJunctsWithoutEliminatee = finiteDualJunctsWithoutEliminatee;
		}

		public List<Term> getFiniteDualJunctsWithEliminatee() {
			return mFiniteDualJunctsWithEliminatee;
		}

		public List<Term> getFiniteDualJunctsWithoutEliminatee() {
			return mFiniteDualJunctsWithoutEliminatee;
		}

	}

}
