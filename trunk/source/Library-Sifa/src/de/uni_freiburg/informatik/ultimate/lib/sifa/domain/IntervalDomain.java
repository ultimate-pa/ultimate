/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.WeakHashMap;
import java.util.function.BiFunction;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation.AssumptionForSolvability;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

// TODO consider splitting dedicated abstract states into classes IntervalDnf and IntervalConjunction
public class IntervalDomain implements IDomain {

	private final ILogger mLogger;
	private final SymbolicTools mTools;
	private final int mMaxDisjuncts;
	private final Supplier<IProgressAwareTimer> mTermToIntervalTimeout;

	private final WeakHashMap<IPredicate, Collection<Map<TermVariable, Interval>>> mPredToIntervalCache =
			new WeakHashMap<>();

	public IntervalDomain(final ILogger logger, final SymbolicTools tools, final int maxDisjuncts,
			final Supplier<IProgressAwareTimer> termToIntervalTimeout) {
		mTools = tools;
		mLogger = logger;
		mMaxDisjuncts = maxDisjuncts;
		mTermToIntervalTimeout = termToIntervalTimeout;
	}

	@Override
	public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
		// TODO using return mTools.or(lhs, rhs) is still an option.
		//      Should we use it sometimes (for instance when inputs are not already cached as intervalDnfs)?
		Collection<Map<TermVariable, Interval>> joinedIntervalDnf = new ArrayList<>();
		joinedIntervalDnf.addAll(toIntervals(lhs));
		joinedIntervalDnf.addAll(toIntervals(rhs));
		if (joinedIntervalDnf.size() > mMaxDisjuncts) {
			joinedIntervalDnf = Collections.singleton(joinToSingleConjunction(joinedIntervalDnf));
		}
		return toPredicate(joinedIntervalDnf);
	}

	private Map<TermVariable, Interval> join(
			final Map<TermVariable, Interval> lhs, final Map<TermVariable, Interval> rhs) {
		return merge(Interval::union, lhs, rhs);
	}

	private Map<TermVariable, Interval> joinToSingleConjunction(
			final Collection<Map<TermVariable, Interval>> intervalDnf) {
		return intervalDnf.stream().reduce(this::join).orElse(Collections.emptyMap());
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		// TODO widen cartesian product instead of joining everything into one state
		//      as long as cartesian product doesn't exceed limit for parallel states
		final Map<TermVariable, Interval> oldItvlConjunction = joinToSingleConjunction(toIntervals(old));
		final Map<TermVariable, Interval> widenWithItvlConjunction = joinToSingleConjunction(toIntervals(widenWith));
		return toPredicate(widen(oldItvlConjunction, widenWithItvlConjunction));
	}

	private static Map<TermVariable, Interval> widen(
			final Map<TermVariable, Interval> old, final Map<TermVariable, Interval> widenWith) {
		return merge(Interval::widen, old, widenWith);
	}

	@Override
	public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
		return RelationCheckUtil.isEqBottom_SolverAlphaSolver(mTools, this, pred);
	}

	@Override
	public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
		return RelationCheckUtil.isSubsetEq_SolverAlphaSolver(mTools, this, subset, superset);
	}

	@Override
	public IPredicate alpha(final IPredicate pred) {
		final Collection<Map<TermVariable, Interval>> intervalDnf = toIntervals(pred);
		return toPredicate(intervalDnf);
	}

	private static Map<TermVariable, Interval> merge(final BiFunction<Interval, Interval, Interval> mergeOperation,
			final Map<TermVariable, Interval> lhs, final Map<TermVariable, Interval> rhs) {
		final Collection<TermVariable> allVars = new HashSet<>();
		allVars.addAll(lhs.keySet());
		allVars.addAll(rhs.keySet());
		final Map<TermVariable, Interval> join = new HashMap<>();
		for (final TermVariable var : allVars) {
			final Interval joinedValue = mergeOperation
					.apply(lhs.getOrDefault(var, Interval.TOP), rhs.getOrDefault(var, Interval.TOP));
			if (!joinedValue.isTop()) {
				join.put(var, joinedValue);
			}
		}
		return join;
	}

	private IPredicate toPredicate(final Map<TermVariable, Interval> intervalConjunction) {
		return mTools.predicate(intervalsToTerm(intervalConjunction));
	}
	private IPredicate toPredicate(final Collection<Map<TermVariable, Interval>> intervalDnf) {
		return mTools.orT(intervalDnf.stream().map(this::intervalsToTerm).collect(Collectors.toList()));
	}

	private Collection<Map<TermVariable, Interval>> toIntervals(final IPredicate pred) {
		final Collection<Map<TermVariable, Interval>> itvlDnf = mPredToIntervalCache
				.computeIfAbsent(pred, this::toIntervalsInternal);
		mLogger.debug("Interval abstraction of %s is %s", pred, itvlDnf);
		return itvlDnf;
	}

	/**
	 * Over-approximate a predicate by intervals.
	 * @param pred Predicate to be converted
	 * @return Interval over-approximation of the given predicate in DNF.
	 *         The outer collection represents a disjunction.
	 *         Each map represents a conjunction of the form (key1 ∊ value1) ∧ (key2 ∊ value2) ∧ ….
	 *         Variables without mappings are unbound and can assume any value.
	 */
	private Collection<Map<TermVariable, Interval>> toIntervalsInternal(final IPredicate pred) {
		final IProgressAwareTimer timer = mTermToIntervalTimeout.get();
		final Term[] dnfDisjunctsAsTerms = mTools.dnfDisjuncts(pred);
		final List<Map<TermVariable, Interval>> dnfDisjunctsAsIntervals = new ArrayList<>(dnfDisjunctsAsTerms.length);
		for (final Term dnfDisjunct : dnfDisjunctsAsTerms) {
			if (!timer.continueProcessing()) {
				mLogger.warn("Interval domain alpha timed out before all disjuncts were processed. "
						+ "Continuing with top.");
				// empty conjunction (the inner map) is true
				return Collections.singleton(Collections.emptyMap());
			}
			dnfDisjunctToIntervals(dnfDisjunct, timer).ifPresent(dnfDisjunctsAsIntervals::add);
		}
		// TODO join disjuncts if there are too many of them
		return Collections.unmodifiableCollection(dnfDisjunctsAsIntervals);
	}

	private Optional<Map<TermVariable, Interval>> dnfDisjunctToIntervals(
			final Term dnfDisjunct, final IProgressAwareTimer timer) {
		// TODO improve check to also find trivial cases like "(and true false)" instead of just "false"
		if (SmtUtils.isFalseLiteral(dnfDisjunct)) {
			return Optional.empty();
		}
		final List<SolvedBinaryRelation> solvedRelations = dnfDisjunctToSolvedRelations(dnfDisjunct);
		Collections.sort(solvedRelations, new CompareNumberOfFreeVariablesInRhs(solvedRelations));

		final Map<TermVariable, Interval> varToInterval = new HashMap<>();
		boolean updated = true;
		while (updated) {
			if (!timer.continueProcessing()) {
				mLogger.warn("Term to interval evaluator loop timed out before fixpoint was reached. "
						+ "Continuing with non-optimal over-approximation.");
				// further iterations will make the abstract state only more precise
				// current state is a legit over-approximation
				break;
			}
			updated = false;
			for (final SolvedBinaryRelation rel : solvedRelations) {
				final Optional<Interval> updatedLhsInterval = updatedLhsInterval(varToInterval, rel);
				if (!updatedLhsInterval.isPresent()) {
					continue;
				} else if (updatedLhsInterval.get().isBottom()) {
					return Optional.empty();
				}
				updated = true;
			}
		}
		return Optional.of(Collections.unmodifiableMap(varToInterval));
	}

	private List<SolvedBinaryRelation> dnfDisjunctToSolvedRelations(final Term dnfDisjunct) {
		final List<SolvedBinaryRelation> solvedRelations = new ArrayList<>();
		for (final Term conjunct : SmtUtils.getConjuncts(dnfDisjunct)) {
			solvedRelations.addAll(solveForAllSubjects(conjunct));
		}
		return solvedRelations;
	}

	private Collection<SolvedBinaryRelation> solveForAllSubjects(final Term term) {
		final AffineRelation affineRel = AffineRelation.convert(mTools.getScript(), term);
		if (affineRel == null) {
			return Collections.emptyList();
		}
		final Collection<SolvedBinaryRelation> result = new ArrayList<>();
		for (final TermVariable subject : term.getFreeVars()) {
			final SolvedBinaryRelation solved = affineRel.solveForSubject(mTools.getScript(), subject);
			if (solved != null) {
				result.add(solved);
			}
		}
		return result;
	}

	public static class CompareNumberOfFreeVariablesInRhs implements Comparator<SolvedBinaryRelation> {

		private final Map<SolvedBinaryRelation, Integer> mNumberOfFreeVarsInRhs;

		public CompareNumberOfFreeVariablesInRhs(final Collection<SolvedBinaryRelation> relations) {
			// pre-compute values since each .getFreeVars() would traverse the whole term again
			mNumberOfFreeVarsInRhs = relations.stream()
					.collect(Collectors.toMap(key -> key, key -> key.getRightHandSide().getFreeVars().length));
		}
		@Override
		public int compare(final SolvedBinaryRelation left, final SolvedBinaryRelation right) {
			return mNumberOfFreeVarsInRhs.get(left).compareTo(mNumberOfFreeVarsInRhs.get(right));
		}
	}

	/**
	 * Evaluates a relation and updates the lhs's interval value in the scope if the value changed
	 * compared to the old value.
	 * @return New value of the lhs (already in updated in the scope) or nothing if the value didn't change
	 */
	private Optional<Interval> updatedLhsInterval(
			final Map<TermVariable, Interval> scope, final SolvedBinaryRelation relation) {
		final Map<AssumptionForSolvability, Term> assumptions = relation.getAssumptionsMap();
		if (assumptions.entrySet().stream().anyMatch(assumption -> !isAssumptionValid(assumption, scope))) {
			// cannot use solved relation because of invalid assumption
			return Optional.empty();
		}
		assert relation.getLeftHandSide() instanceof TermVariable;
		final TermVariable subject = (TermVariable) relation.getLeftHandSide();
		final Interval oldValue = scope.getOrDefault(subject, Interval.TOP);
		final Interval newValue = updatedLhsForRelation(
				oldValue, relation.getRelationSymbol(), TermToInterval.evaluate(relation.getRightHandSide(), scope));
		if (oldValue.equals(newValue)) {
			return Optional.empty();
		}
		scope.put(subject, newValue);
		return Optional.of(newValue);
	}

	private Interval updatedLhsForRelation(final Interval lhs, final RelationSymbol relSym, final Interval rhs) {
		switch (relSym) {
		case DISTINCT:
			return lhs.satisfyDistinct(rhs).getLhs();
		case EQ:
			return lhs.satisfyEqual(rhs).getLhs();
		case GEQ:
		case GREATER:
			return lhs.satisfyGreaterOrEqual(rhs).getLhs();
		case LEQ:
		case LESS:
			return lhs.satisfyLessOrEqual(rhs).getLhs();
		default:
			throw new AssertionError("Missing case for " + relSym);
		}
	}

	private boolean isAssumptionValid(final Entry<AssumptionForSolvability, Term> assumption,
			final Map<TermVariable, Interval> scope) {
		switch (assumption.getKey()) {
		case INTEGER_DIVISIBLE_BY_CONSTANT:
			return isIntDivisibleByConst(assumption.getValue(), scope);
		case REAL_DIVISOR_NOT_ZERO:
			return isRealDivisorNotZero(assumption.getValue(), scope);
		default:
			throw new AssertionError("Missing case for " + assumption.getKey());
		}
	}

	private boolean isIntDivisibleByConst(final Term assumption, final Map<TermVariable, Interval> scope) {
		// TODO assumptions are a work in progress in for SolvedBinaryRelation.
		// In the future we have to check for things like (= (% x 7) 0).
		// For now we use the safe over-approximation:
		return false;
	}

	private boolean isRealDivisorNotZero(final Term assumption, final Map<TermVariable, Interval> scope) {
		// TODO assumptions are a work in progress in for SolvedBinaryRelation.
		// In the future we have to check for things like (distinct x 0).
		// For now we use the safe over-approximation:
		return false;
		// Correct check would be something like:
		// return !scope.getOrDefault((TermVariable) divisor, Interval.TOP).containsZero();
	}

	private Term intervalsToTerm(final Map<TermVariable, Interval> mapVarsToVals) {
		final Script script = mTools.getScript();
		final Collection<Term> conjunction = new ArrayList<>(2 * mapVarsToVals.size());
		for (final Entry<TermVariable, Interval> varAndVal : mapVarsToVals.entrySet()) {
			final TermVariable var = varAndVal.getKey();
			final Interval val = varAndVal.getValue();
			if (val.hasLower()) {
				conjunction.add(SmtUtils.geq(script, var, boundFor(var, val.getLower())));
			}
			if (val.hasUpper()) {
				conjunction.add(SmtUtils.leq(script, var, boundFor(var, val.getUpper())));
			}
		}
		return SmtUtils.and(script, conjunction);
	}

	private Term boundFor(final TermVariable variable, final Rational bound) {
		return SmtUtils.rational2Term(mTools.getScript(), bound, variable.getSort());
	}


}











