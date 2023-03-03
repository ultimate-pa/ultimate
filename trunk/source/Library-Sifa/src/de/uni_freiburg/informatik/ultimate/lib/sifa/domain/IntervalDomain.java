/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2023 Frank Schüssele (schuessf@tf.uni-freiburg.de)
 * Copyright (C) 2019-2023 University of Freiburg
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
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialRelation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class IntervalDomain extends AbstractStateBasedDomain<IntervalState> {

	public IntervalDomain(final ILogger logger, final SymbolicTools tools, final int maxDisjuncts,
			final Supplier<IProgressAwareTimer> timeout) {
		super(logger, tools, maxDisjuncts, timeout);
	}

	@Override
	public IntervalState toState(final Term[] conjuncts) {
		final List<SolvedBinaryRelation> solvedRelations = solveForAllSubjects(conjuncts);
		final Map<Term, Interval> varToInterval = new HashMap<>();
		boolean updated = true;
		final long maxIterations =
				1 + solvedRelations.stream().map(SolvedBinaryRelation::getLeftHandSide).distinct().count();
		for (int iteration = 1; updated && iteration <= maxIterations; ++iteration) {
			// TODO: Should we pass a timer for this?
			// if (!timer.continueProcessing()) {
			// mLogger.warn("Term to interval evaluator loop timed out before fixpoint was reached. "
			// + "Continuing with non-optimal over-approximation.");
			// // further iterations will make the abstract state only more precise
			// // current state is a legit over-approximation
			// break;
			// }
			updated = false;
			for (final SolvedBinaryRelation rel : solvedRelations) {
				final Optional<Interval> updatedLhsInterval = updatedLhsInterval(varToInterval, rel);
				if (!updatedLhsInterval.isPresent()) {
					continue;
				} else if (updatedLhsInterval.get().isBottom()) {
					return null;
				}
				updated = true;
			}
		}
		if (updated) {
			// maxIter limit reached
			// TODO research whether this only happens if dnfDisjunct is unsat.
			// If so, then return bottom
			mLogger.warn("Interval conversion did not stabilize in %d iterations. "
					+ "Over-approximation may be very coarse.", maxIterations);
			mLogger.debug("Relations used to update are %s.", solvedRelations);
			mLogger.debug("Interval values after last iteration are %s.", varToInterval);
		}
		return new IntervalState(varToInterval);
	}

	@Override
	public IntervalState getTopState() {
		return new IntervalState();
	}

	@Override
	protected Term transformTerm(final Term term) {
		// TODO consider removing boolean sub-terms before computing DNF as we don't use the boolean terms anyways
		return term;
	}

	private List<SolvedBinaryRelation> solveForAllSubjects(final Term[] conjuncts) {
		final List<SolvedBinaryRelation> result = new ArrayList<>();
		for (final Term term : conjuncts) {
			final PolynomialRelation polyRel = PolynomialRelation.of(mTools.getScript(), term);
			if (polyRel == null) {
				continue;
			}
			for (final TermVariable subject : term.getFreeVars()) {
				final SolvedBinaryRelation solved = polyRel.solveForSubject(mTools.getScript(), subject);
				if (solved != null) {
					result.add(solved);
				}
			}
		}
		Collections.sort(result, new CompareNumberOfFreeVariablesInRhs(result));
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
	 * Evaluates a relation and updates the lhs's interval value in the scope if the value changed compared to the old
	 * value.
	 *
	 * @return New value of the lhs (already in updated in the scope) or nothing if the value didn't change
	 */
	private static Optional<Interval> updatedLhsInterval(final Map<Term, Interval> scope,
			final SolvedBinaryRelation relation) {
		assert relation.getLeftHandSide() instanceof TermVariable;
		final TermVariable subject = (TermVariable) relation.getLeftHandSide();
		final Interval oldValue = scope.getOrDefault(subject, Interval.TOP);
		final Interval newValue = updatedLhsForRelation(oldValue, relation.getRelationSymbol(),
				TermToInterval.evaluate(relation.getRightHandSide(), scope));
		if (oldValue.equals(newValue)) {
			return Optional.empty();
		}
		scope.put(subject, newValue);
		return Optional.of(newValue);
	}

	private static Interval updatedLhsForRelation(final Interval lhs, final RelationSymbol relSym, final Interval rhs) {
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

}
