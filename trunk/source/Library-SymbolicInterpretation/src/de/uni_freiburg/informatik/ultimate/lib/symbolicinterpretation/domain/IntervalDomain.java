/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
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
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class IntervalDomain implements IDomain {

	private final ILogger mLogger;
	private final SymbolicTools mTools;
	private final Supplier<IProgressAwareTimer> mTermToIntervalTimeout;

	public IntervalDomain(final ILogger logger, final SymbolicTools tools,
			final Supplier<IProgressAwareTimer> termToIntervalTimeout) {
		mTools = tools;
		mLogger = logger;
		mTermToIntervalTimeout = termToIntervalTimeout;
	}
	@Override
	public IPredicate join(final IPredicate first, final IPredicate second) {
		// TODO Auto-generated method stub
		return mTools.or(first, second);
	}

	@Override
	public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
		// TODO Auto-generated method stub
		return mTools.top();
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
		final IProgressAwareTimer timer = mTermToIntervalTimeout.get();
		final Term[] dnfDisjunctsAsTerms = mTools.dnfDisjuncts(pred);
		final List<Map<TermVariable, Interval>> dnfDisjunctsAsIntervals = new ArrayList<>(dnfDisjunctsAsTerms.length);
		for (final Term dnfDisjunct : dnfDisjunctsAsTerms) {
			if (!timer.continueProcessing()) {
				mLogger.warn("Interval domain alpha timed out before all disjuncts were processed. "
						+ "Continuing with top.");
				// the empty disjunction is true
				dnfDisjunctsAsIntervals.clear();
			}
			dnfDisjunctsAsIntervals.add(dnfDisjunctToIntervals(dnfDisjunct, timer));
		}
		mLogger.debug("Interval abstraction is %s", dnfDisjunctsAsIntervals);
		// TODO join disjuncts if there are too many of them
		return mTools.or(dnfDisjunctsAsIntervals.stream().map(this::intervalsToTerm).collect(Collectors.toList()));
	}

	private Map<TermVariable, Interval> dnfDisjunctToIntervals(final Term dnfDisjunct, final IProgressAwareTimer timer) {

		final List<SolvedBinaryRelation> solvedRelations = dnfDisjunctToSolvedRelations(dnfDisjunct);
		Collections.sort(solvedRelations, new CompareNumberOfFreeVariablesInRhs(solvedRelations));

		final Map<TermVariable, Interval> varToInterval = new HashMap<>();
		boolean updated = true;
		while (updated) {
			if (!timer.continueProcessing()) {
				mLogger.warn("Term to interval evaluator loop timed out before fixpoint was reached. "
						+ "Continuing with non-optimal over-approximation.");
				// further iterations will make the abstract state more precise
				// current state is a legit over-approximation
				return varToInterval;
			}
			updated = false;
			for (final SolvedBinaryRelation rel : solvedRelations) {
				updated |= updateInterval(varToInterval, rel);
			}
		}
		return varToInterval;
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

	private boolean updateInterval(final Map<TermVariable, Interval> scope, final SolvedBinaryRelation relation) {
		final Map<AssumptionForSolvability, Term> assumptions = relation.getAssumptionsMap();
		if (assumptions.entrySet().stream().anyMatch(assumption -> !isAssumptionValid(assumption, scope))) {
			// cannot use solved relation because of invalid assumption
			return false;
		}
		assert relation.getLeftHandSide() instanceof TermVariable;
		final TermVariable subject = (TermVariable) relation.getLeftHandSide();
		final Interval oldValue = scope.getOrDefault(subject, Interval.TOP);
		final Interval newValue = updatedLhsForRelation(
				oldValue, relation.getRelationSymbol(), TermToInterval.evaluate(relation.getRightHandSide(), scope));
		if (oldValue.equals(newValue)) {
			return false;
		}
		scope.put(subject, newValue);
		return true;
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











