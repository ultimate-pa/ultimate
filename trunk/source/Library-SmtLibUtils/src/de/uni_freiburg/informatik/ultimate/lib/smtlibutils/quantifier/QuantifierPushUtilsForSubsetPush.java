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
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;


import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.FormulaClassification;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils.IQuantifierEliminator;
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
	 * TODO: Revise documentation Auxiliary method for quantifier elimination.
	 * <br />
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
	 * <li>Optimization2: Do not apply the general quantifier elimination
	 * recursively but only the method that immediately applies the distributivity.
	 * <li>Comment1: This method is useless if we do not apply distributivity.
	 * <li>Problem1: If the recursive call just replaces that names of the
	 * quantified variables we run into an infinite loop. Maybe there a similar more
	 * sophisticated nontermination problems. </ ul>
	 *
	 * TODO: What about eliminatee that occur in a single dualjunct? Have been
	 * checked before. But track new ones. Flatten after push
	 *
	 * FIXME: Combination of partitioning and flattening may produce an infinite
	 * loop.
	 *
	 */
	public static Term sequentialSubsetPush(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask et,
			final IQuantifierEliminator qe) {
		List<Term> currentDualFiniteJuncts = Arrays
				.asList(QuantifierUtils.getDualFiniteJuncts(et.getQuantifier(), et.getTerm()));
		// TODO Reduce the following checks
		if (currentDualFiniteJuncts.size() <= 1) {
			throw new AssertionError("No dual finite junction");
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
		List<TermVariable> currentEliminatees = new ArrayList<>(et.getEliminatees());
		final List<TermVariable> failedEliminatees = new ArrayList<>();
		// In fact these eliminatees occur also in at least one dualFiniteJunct
		// otherwise the input would not be legal.
		List<TermVariable> currentSuitableEliminatees = findSuitableEliminatees(currentEliminatees, failedEliminatees,
				currentDualFiniteJuncts, et.getQuantifier());
		int iterations = 0;
		int iterationsWithProgress = 0;
		while (!currentSuitableEliminatees.isEmpty()) {
			if (iterations > 20 + et.getEliminatees().size()) {
				final ILogger logger = services.getLoggingService().getLogger(QuantifierPushUtilsForSubsetPush.class);
				logger.info(String.format(
						"Initially %s eliminatees, after %s iterations we have %s eliminatees. Is this in finite loop?",
						et.getEliminatees().size(), iterations, currentEliminatees.size()));
			}
			final TermVariable eliminatee = XnfScout.selectBestEliminatee(mgdScript.getScript(),
					et.getQuantifier(), currentSuitableEliminatees, currentDualFiniteJuncts);
			final PartitionByEliminateeOccurrence parti = new PartitionByEliminateeOccurrence(currentDualFiniteJuncts,
					eliminatee);
			// Note 1: minionEliminatees may include failedEliminatees
			// Note 2: in subsequent calls the selected eliminatee may occur in all params
			// hence we have to recurse on proper minions even if they have a smaller
			// expected chance for getting eliminated #overtakingMinionProblem
			final List<TermVariable> minionEliminatees = QuantifierPusher.determineMinionEliminatees(currentEliminatees,
					parti.getFiniteDualJunctsWithoutEliminatee());
			if (!minionEliminatees.contains(eliminatee)) {
				throw new AssertionError("Missing minion " + eliminatee);
			}
			final Term pushSubformula;
			{
				final Term pushed = pushMinionEliminatees(services, mgdScript, applyDistributivity, pqeTechniques,
						simplificationTechnique, et, qe, minionEliminatees, parti, currentEliminatees);
				iterations++;
				if (pushed == null) {
					// not pushable, mark eliminatee as failed an continue with the same dual juncts
					failedEliminatees.add(eliminatee);
					currentSuitableEliminatees = findSuitableEliminatees(currentEliminatees, failedEliminatees,
							currentDualFiniteJuncts, et.getQuantifier());
					continue;
				}
				final Set<TermVariable> eliminatedMinions;
				final List<TermVariable> newEliminatees = new LinkedList<>();
				if (pushed instanceof QuantifiedFormula) {
					final QuantifiedFormula qf = (QuantifiedFormula) pushed;
					eliminatedMinions = new HashSet<>(minionEliminatees);
					for (final TermVariable tv : Arrays.asList(qf.getVariables())) {
						if (minionEliminatees.contains(tv)) {
							eliminatedMinions.remove(tv);
							if (tv == eliminatee) {
								failedEliminatees.add(eliminatee);
							}
						} else {
							newEliminatees.add(tv);
						}
					}
					pushSubformula = qf.getSubformula();
				} else {
					eliminatedMinions = new HashSet<>(minionEliminatees);
					pushSubformula = pushed;
				}
				// TODO: When is a push considered a success? (1) When the push changed the
				// formula, e.g., existential quantification could be removed in one disjunct.
				// (2) If at least one eliminatee is removed completely.
				// I prefer (1) but QuantifierEliminationBenchmarks#fridgeDivCapture (with
				// distributivity evaluation switched off) only successful if we use (2)
				if (!eliminatedMinions.isEmpty()) {
					iterationsWithProgress++;
				}
				currentEliminatees.removeAll(eliminatedMinions);
				currentEliminatees.addAll(newEliminatees);
			}

			final Term currentDualFiniteJunction;
			{
				currentDualFiniteJuncts = new ArrayList<>(parti.getFiniteDualJunctsWithoutEliminatee());
				currentDualFiniteJuncts.add(pushSubformula);
				// building the dualFiniteJunction may simplify the formula
				currentDualFiniteJunction = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(),
						et.getQuantifier(), currentDualFiniteJuncts);
			}
			{
				final EliminationTask etForPreprocessing = new EliminationTask(et.getQuantifier(),
						new HashSet<>(currentEliminatees), currentDualFiniteJunction, et.getContext());
				final boolean pushLocalEliminatees = false;
				final boolean pushDualQuantifiersInParams = true;
				final Pair<Boolean, Term> pair = QuantifierPushUtils.preprocessDualFiniteJunction(services, mgdScript,
						applyDistributivity, pqeTechniques, simplificationTechnique, etForPreprocessing, qe,
						pushLocalEliminatees, pushDualQuantifiersInParams);
				if (!pair.getFirst()) {
					return pair.getSecond();
				}
				final QuantifiedFormula qf = (QuantifiedFormula) pair.getSecond();
				currentEliminatees = new ArrayList<>(Arrays.asList(qf.getVariables()));
				failedEliminatees.retainAll(currentEliminatees);
				currentDualFiniteJuncts = Arrays
						.asList(QuantifierUtils.getDualFiniteJuncts(et.getQuantifier(), qf.getSubformula()));
			}

			currentSuitableEliminatees = findSuitableEliminatees(currentEliminatees, failedEliminatees,
					currentDualFiniteJuncts, et.getQuantifier());
		}
		if (iterationsWithProgress == 0) {
			return null;
		} else {
			return SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(), currentEliminatees, QuantifierUtils
					.applyDualFiniteConnective(mgdScript.getScript(), et.getQuantifier(), currentDualFiniteJuncts));
		}
	}

	/**
	 * Try to push minion eliminatees. Construct appropriate context (mind
	 * non-minions and other dual juncts) for the push. Return null if push was not
	 * considered successful. We say that the push is not successful if (1) the
	 * result of the push is similar to the input or (2) the flattened result is
	 * similar to the input.
	 *
	 */
	private static Term pushMinionEliminatees(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask et,
			final IQuantifierEliminator qe, final List<TermVariable> minionEliminatees,
			final PartitionByEliminateeOccurrence parti, final List<TermVariable> currentEliminatees) {
		final Term dualFiniteJunction = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(),
				et.getQuantifier(), parti.getFiniteDualJunctsWithEliminatee());
		final Term quantified = SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(),
				new HashSet<>(minionEliminatees), dualFiniteJunction);
		final List<TermVariable> nonMinionEliminatees = new ArrayList<>(currentEliminatees);
		nonMinionEliminatees.removeAll(new HashSet<>(minionEliminatees));
		final Context parentContext = et.getContext();
		Context context = parentContext.constructChildContextForQuantifiedFormula(mgdScript.getScript(),
				nonMinionEliminatees);
		context = context.constructChildContextForConDis(services, mgdScript,
				((ApplicationTerm) et.getTerm()).getFunction(), parti.getFiniteDualJunctsWithoutEliminatee());
		// Evaluate success: return null if there was not progress.
		final Term pushed = qe.eliminate(services, mgdScript, applyDistributivity, pqeTechniques,
				simplificationTechnique, context, quantified);
		final Term result;
		if (pushed == quantified) {
			// no elimination success
			result = null;
		} else {
			final Term flattened = QuantifierPushUtils.flattenQuantifiedFormulas(mgdScript, et.getQuantifier(), pushed);
			if (flattened == null) {
				// elimination result was already flat
				result = pushed;
			} else {
				if (flattened == quantified) {
					// no elimination success either
					result = null;
				} else {
					result = flattened;
				}
			}
		}
		return result;
	}

	/**
	 * A currentEliminatee is suitable if
	 * <ul>
	 * <li>it is not in the set of `bannedEliminatees`,
	 * <li>occurs in at least two dualFiniteJuncts (not enforced here but ensured by
	 * the input),
	 * <li>does not occur in all dualFiniteJuncts, and
	 * <li>occurs in at least on dualFiniteJunct that is a corresponding
	 * finiteJunction (i.e., applying distributivity to a subset makes sense).
	 * </ul>
	 * Note: If we would allow eliminatees that occur in all subformulas we can run
	 * into an infinite loop (of subset pushes). If we however allow eliminatees to
	 * be not suitable for that reason a selected eliminatee with good score (wrt.
	 * expected eliminatability) may be be replaced by one of its minion with lower
	 * score in subsequent calls. #overtakingMinionProblem
	 *
	 */
	private static List<TermVariable> findSuitableEliminatees(final List<TermVariable> currentEliminatees,
			final List<TermVariable> bannedEliminatees, final List<Term> currentDualFiniteParams,
			final int quantifier) {
		return currentEliminatees.stream().filter(eliminatee -> !bannedEliminatees.contains(eliminatee)
				&& currentDualFiniteParams.stream()
						.anyMatch(param -> !Arrays.asList(param.getFreeVars()).contains(eliminatee))
				&& currentDualFiniteParams.stream()
						.anyMatch(param -> (Arrays.asList(param.getFreeVars()).contains(eliminatee) && QuantifierPusher
								.classify(quantifier, param) == FormulaClassification.CORRESPONDING_FINITE_CONNECTIVE)))
				.collect(Collectors.toList());
	}

	/**
	 * Class that partitions a list of terms into two lists. One list where a given
	 * TermVariable occurs as a free variable and one list where the given
	 * TermVariable does not occur as a free variable. Terminology and assertions
	 * are fitted to the method
	 * {@link QuantifierPushUtilsForSubsetPush#sequentialSubsetPush} in which this
	 * class is used.
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
