/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions;

import java.util.Set;
import java.util.function.Predicate;

/**
 * Provides IPredicates for filtering of transitions where the filtering is based on a given set of states. The
 * predicates evaluate to true iff each state that occurs in the transition is contained in the given set of states.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class StateBasedTransitionFilterPredicateProvider<LETTER, STATE> {
	protected final Set<STATE> mStates;
	private final Predicate<IncomingInternalTransition<LETTER, STATE>> mInternalPredecessorsPredicate;
	private final Predicate<IncomingCallTransition<LETTER, STATE>> mCallPredecessorPredicate;
	private final Predicate<OutgoingInternalTransition<LETTER, STATE>> mInternalSuccessorPredicate;
	private final Predicate<OutgoingCallTransition<LETTER, STATE>> mCallSuccessorPredicate;
	private final Predicate<IncomingReturnTransition<LETTER, STATE>> mReturnPredecessorPredicate;
	private final Predicate<OutgoingReturnTransition<LETTER, STATE>> mReturnSuccessorPredicate;
	private final Predicate<SummaryReturnTransition<LETTER, STATE>> mReturnSummaryPredicate;

	/**
	 * Constructor.
	 *
	 * @param states
	 *            states for filtering
	 */
	public StateBasedTransitionFilterPredicateProvider(final Set<STATE> states) {
		mStates = states;

		mInternalPredecessorsPredicate = trans -> mStates.contains(trans.getPred());

		mCallPredecessorPredicate = trans -> mStates.contains(trans.getPred());

		mInternalSuccessorPredicate = trans -> mStates.contains(trans.getSucc());

		mCallSuccessorPredicate = trans -> mStates.contains(trans.getSucc());

		mReturnPredecessorPredicate =
				trans -> mStates.contains(trans.getLinPred()) && mStates.contains(trans.getHierPred());

		mReturnSuccessorPredicate = trans -> mStates.contains(trans.getHierPred()) && mStates.contains(trans.getSucc());

		mReturnSummaryPredicate = trans -> mStates.contains(trans.getSucc()) && mStates.contains(trans.getLinPred());
	}

	public Predicate<IncomingInternalTransition<LETTER, STATE>> getInternalPredecessorsPredicate() {
		return mInternalPredecessorsPredicate;
	}

	public Predicate<IncomingCallTransition<LETTER, STATE>> getCallPredecessorPredicate() {
		return mCallPredecessorPredicate;
	}

	public Predicate<OutgoingInternalTransition<LETTER, STATE>> getInternalSuccessorPredicate() {
		return mInternalSuccessorPredicate;
	}

	public Predicate<OutgoingCallTransition<LETTER, STATE>> getCallSuccessorPredicate() {
		return mCallSuccessorPredicate;
	}

	public Predicate<IncomingReturnTransition<LETTER, STATE>> getReturnPredecessorPredicate() {
		return mReturnPredecessorPredicate;
	}

	public Predicate<OutgoingReturnTransition<LETTER, STATE>> getReturnSuccessorPredicate() {
		return mReturnSuccessorPredicate;
	}

	public Predicate<SummaryReturnTransition<LETTER, STATE>> getReturnSummaryPredicate() {
		return mReturnSummaryPredicate;
	}
}
