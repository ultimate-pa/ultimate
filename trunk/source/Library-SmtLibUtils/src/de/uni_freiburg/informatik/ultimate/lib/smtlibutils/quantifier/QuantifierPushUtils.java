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
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.FormulaClassification;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils.IQuantifierEliminator;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Provides static methods that are utilized by the {@link QuantifierPushTermWalker}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierPushUtils {

	/**
	 * If set to true we check after applying distributivity if we were able to eliminate some quantified variables. If
	 * elimination failed for all variables then we return the original term without applying distributivity.
	 *
	 */
	public static final boolean OPTION_EVALUATE_SUCCESS_OF_DISTRIBUTIVITY_APPLICATION = false;
	public static final boolean OPTION_ELIMINATEE_SEQUENTIALIZATION = true;
	public static final boolean OPTION_SCOUT_BASED_DISTRIBUTIVITY_RECOMMENDATION = true;

	public static final String NOT_DUAL_FINITE_CONNECTIVE = "not dual finite connective";

	public static boolean isQuantifiedDualFiniteJunction(final int quantifier, final Term term) {
		final boolean result;
		if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula) term;
			if (qf.getQuantifier() == quantifier) {
				result = QuantifierPusher.classify(qf.getSubformula()) == FormulaClassification.DUAL_FINITE_CONNECTIVE;
			} else {
				result = false;
			}
		} else {
			result = false;
		}
		return result;
	}

	/**
	 * If we have a dualFiniteJunction (i.e., existentially quantified conjunction
	 * or universally quantified disjunction) we can in general not push the
	 * quantifier and have to apply elimination techniques, like e.g., DER, TIR. In
	 * order to maximize the applicability of these elimination techniques we
	 * exhaustively apply a number of preprocessing steps.
	 *
	 * @param pushDualQuantifiersInParams Apply also a preprocessing step in which
	 *                                    we apply the elimination to
	 *                                    dualFiniteJuncts that are quantified by
	 *                                    the dual quantifier. Unlike the other
	 *                                    preprocessing steps this can be costly
	 *                                    even if this preprocessing step is unable
	 *                                    to change the formula.
	 *
	 * @return A pair (b, 𝜑) such that b==true iff 𝜑 is a quantified
	 *         dualFiniteJunction.
	 */
	public static Pair<Boolean, Term> preprocessDualFiniteJunction(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask et,
			final IQuantifierEliminator qe, final boolean pushLocalEliminatees,
			final boolean pushDualQuantifiersInParams) {
		EliminationTask currentEt = et;
		int i = 0;
		// Each preprocessing step may change the structure of the formula completely
		// and enable further preprocessing steps.
		// The sequence of preprocessing steps is applied iteratively in the following
		// loop. Whenever a preprocessing step was successful we apply the sequence of
		// preprocessing steps anew. If no preprocessing is applicable any more (i.e.,
		// we reached the end of the loop body) we return the result.
		// If however the result of a preprocessing step is not a dualFiniteJunction any
		// more, we return the result immediately.
		while (true) {
			i++;
			if (i >= 20) {
				throw new AssertionError("Probably an infinite loop!");
			}
			// Step 0: Check if elimination task has still eliminatees and return it not
			if (currentEt.getEliminatees().isEmpty()) {
				return new Pair<>(false, currentEt.getTerm());
			}

			// Step 1: Check if subformula is a dual finite junction and return if not
			final List<Term> currentDualFiniteJuncts = Arrays
					.asList(QuantifierUtils.getDualFiniteJuncts(currentEt.getQuantifier(), currentEt.getTerm()));
			if (currentDualFiniteJuncts.size() <= 1) {
				return new Pair<>(false, SmtUtils.quantifier(mgdScript.getScript(), currentEt.getQuantifier(),
						currentEt.getEliminatees(), currentDualFiniteJuncts.get(0)));
			}

			// Step 2: Flatten quantifiers if possible
			if (!isFlattened(et.getQuantifier(), currentDualFiniteJuncts)) {
				final Term flattened = flattenQuantifiedFormulas(mgdScript, et.getQuantifier(),
						currentEt.toTerm(mgdScript.getScript()));
				// some quantifiers could be removed for trivial reasons
				if (flattened instanceof QuantifiedFormula) {
					final QuantifiedFormula qf = (QuantifiedFormula) flattened;
					if (qf.getQuantifier() != currentEt.getQuantifier()) {
						// some inner quantifier moved to root node due to simplifications
						return new Pair<>(false, flattened);
					} else {
						// update EliminationTask, restart
						currentEt = new EliminationTask(qf, currentEt.getContext());
						continue;
					}
				} else {
					// return because not quantified any more
					return new Pair<>(false, flattened);
				}
			}

			// Step 3: Partition dualFiniteJuncts according to eliminatees and try to push
			{
				final ParameterPartition pp = new ParameterPartition(mgdScript.getScript(), currentEt);
				if (!pp.isIsPartitionTrivial()) {
					final Term tmp = pp.getTermWithPushedQuantifier();
					if (tmp instanceof QuantifiedFormula) {
						// very unlikely case that due to simplifications the result is again a
						// quantified formula
						final QuantifiedFormula qf = (QuantifiedFormula) tmp;
						if (qf.getQuantifier() != currentEt.getQuantifier()) {
							// some inner quantifier moved to root node due to simplifications
							return new Pair<>(false, tmp);
						} else {
							currentEt = new EliminationTask(qf, currentEt.getContext());
							continue;
						}
						// unreachable line
					} else {
						// partition result not quantified, we return
						return new Pair<>(false, tmp);
					}
				}
			}

			// Step 4: Push local eliminatees over corresponding connective if applicable
			// See #innerAlternatingFirst
			if (pushLocalEliminatees) {
				final Term localsEliminated = QuantifierPushUtilsForLocalEliminatees
						.pushLocalEliminateesOverCorrespondingFiniteJunction(services, mgdScript, applyDistributivity,
								pqeTechniques, simplificationTechnique, currentEt, qe);
				if (localsEliminated != null) {
					if (localsEliminated instanceof QuantifiedFormula) {
						final QuantifiedFormula qf = (QuantifiedFormula) localsEliminated;
						if (qf.getQuantifier() != currentEt.getQuantifier()) {
							// some inner quantifier moved to root node due to simplifications
							return new Pair<>(false, localsEliminated);
						} else {
							// update EliminationTask, restart
							currentEt = new EliminationTask(qf, currentEt.getContext());
							continue;
						}
					} else {
						// return because not quantified any more
						return new Pair<>(false, localsEliminated);
					}
				}
			}

			// Step 5 (optional) Push dual quantifiers of dualFiniteJuncts
			if (pushDualQuantifiersInParams) {
				final Term tmp = pushDualQuantifiersInParams(services, mgdScript, applyDistributivity, pqeTechniques,
						simplificationTechnique, currentEt, qe);
				// WARNING 1: We expect that we get null if the push was not successful. If we
				// always get a non-null result we will run into an infinite loop.
				// WARNING 2: Even if we do not run into an infinite loop this step can be
				// costly if the preprocessing runs several times because if there is a
				// non-eliminatable quantifier we try to eliminate the quantifier in each call.
				if (tmp != null) {
					if (tmp instanceof QuantifiedFormula) {
						final QuantifiedFormula qf = (QuantifiedFormula) tmp;
						if (qf.getQuantifier() != currentEt.getQuantifier()) {
							// some inner quantifier moved to root node due to simplifications
							return new Pair<>(false, tmp);
						} else {
							// update EliminationTask, restart
							currentEt = new EliminationTask(qf, currentEt.getContext());
							continue;
						}
					} else {
						// return because not quantified any more
						return new Pair<>(false, tmp);
					}
				}
			}

			// Finally, none of the preprocessing steps above was applicable any more
			// return dual finite junction in the desired form
			return new Pair<>(true, currentEt.toTerm(mgdScript.getScript()));
		}
	}

	/**
	 * We call a dualFiniteJunction flattened if no dualJunct has the same
	 * quantifier as the overall formula. E.g. `∃x. (∀y. 𝜑1[y]) ∧ 𝜑2[x] ∧
	 * (∃z.𝜑3[z])` is not flattened since the third conjunct is also existentially
	 * quantified but `∃x,y. (∀y. 𝜑1[y]) ∧ 𝜑2[x] ∧ 𝜑3[z]` is flattened.
	 */
	static boolean isFlattened(final int quantifier, final List<Term> dualFiniteJuncts) {
		final Predicate<? super Term> notSameQuantifier = (x -> (QuantifierPusher.classify(quantifier,
				x) != FormulaClassification.SAME_QUANTIFIER));
		return dualFiniteJuncts.stream().allMatch(notSameQuantifier);
	}


	/**
	 * TODO: Review and possibly revise.
	 * TODO: return null if not changed, update callers of method
	 */
	public static Term flattenQuantifiedFormulas(final ManagedScript mgdScript, final int quantifier,
			final Term term) {
		final Set<String> freeVarNames =
				Arrays.stream(term.getFreeVars()).map(x -> x.getName()).collect(Collectors.toSet());
		final Term inputDualJunction;
		final LinkedHashMap<String, TermVariable> quantifiedVariables = new LinkedHashMap<>();
		if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) term;
			if (quantifiedFormula.getQuantifier() != quantifier) {
				// different quantifier, do not handle
				return null;
			}
			inputDualJunction = quantifiedFormula.getSubformula();
			Arrays.stream(quantifiedFormula.getVariables()).forEach(x -> quantifiedVariables.put(x.getName(), x));
		} else {
			inputDualJunction = term;
		}
		final Term[] dualJuncts = QuantifierUtils.getDualFiniteJuncts(quantifier, inputDualJunction);
		final ArrayList<Term> resultDualJuncts = new ArrayList<>();
		for (final Term dualJunct : dualJuncts) {
			if (dualJunct instanceof QuantifiedFormula) {
				final QuantifiedFormula innerQuantifiedFormula = (QuantifiedFormula) dualJunct;
				if (innerQuantifiedFormula.getQuantifier() != quantifier) {
					resultDualJuncts.add(dualJunct);
				} else {
					final Map<Term, Term> substitutionMapping = new HashMap<>();
					for (final TermVariable innerVar : innerQuantifiedFormula.getVariables()) {
						TermVariable resultVar;
						if (quantifiedVariables.containsKey(innerVar.getName())
								|| freeVarNames.contains(innerVar.getName())) {
							resultVar = mgdScript.constructFreshCopy(innerVar);
							substitutionMapping.put(innerVar, resultVar);
						} else {
							resultVar = innerVar;
						}
						quantifiedVariables.put(resultVar.getName(), resultVar);
					}
					Term resultSubformula;
					if (substitutionMapping.isEmpty()) {
						resultSubformula = innerQuantifiedFormula.getSubformula();
					} else {
						resultSubformula = Substitution.apply(mgdScript, substitutionMapping,
								innerQuantifiedFormula.getSubformula());
					}
					resultDualJuncts.add(resultSubformula);
				}
			} else {
				resultDualJuncts.add(dualJunct);
			}
		}
		final Term resultDualJunction =
				QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(), quantifier, resultDualJuncts);
		final Term result = SmtUtils.quantifier(mgdScript.getScript(), quantifier,
				quantifiedVariables.entrySet().stream().map(Entry::getValue).collect(Collectors.toSet()),
				resultDualJunction);
		return result;
	}


	public static Term pushDualQuantifiersInParams(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask et,
			final IQuantifierEliminator qe) {
		final Term[] dualFiniteParams = QuantifierUtils.getDualFiniteJuncts(et.getQuantifier(), et.getTerm());
		assert dualFiniteParams.length > 1 : NOT_DUAL_FINITE_CONNECTIVE;
		final List<Term> resultDualFiniteParams = new ArrayList<>();
		boolean atLeastOneParameterModified = false;
		for (int i = 0; i < dualFiniteParams.length; i++) {
			if (dualFiniteParams[i] instanceof QuantifiedFormula) {
				final Context childContext = et.getContext().constructChildContextForConDis(services, mgdScript,
						((ApplicationTerm) et.getTerm()).getFunction(), Arrays.asList(dualFiniteParams), i);
				final Term resultDualFiniteParamI = qe.eliminate(services, mgdScript, applyDistributivity,
						pqeTechniques, simplificationTechnique, childContext, dualFiniteParams[i]);
				if (resultDualFiniteParamI != dualFiniteParams[i]) {
					atLeastOneParameterModified = true;
				}
				resultDualFiniteParams.add(resultDualFiniteParamI);
			} else {
				resultDualFiniteParams.add(dualFiniteParams[i]);
			}
		}
		final Term result;
		if (atLeastOneParameterModified) {
			final Term dualFiniteJunction = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(),
					et.getQuantifier(), resultDualFiniteParams);
			result = SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(), et.getEliminatees(),
					dualFiniteJunction);
		} else {
			result = null;
		}
		return result;
	}


}
