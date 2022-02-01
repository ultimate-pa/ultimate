/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Interface for the state factory used by sleep set reduction of a finite automaton.
 *
 * @author Marcel Ebbinghaus
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of states in the original automaton
 * @param <R>
 *            The type of states in the reduced automaton, created from an original state and a sleep set
 */
public interface ISleepSetStateFactory<L, S, R> extends IEmptyStackStateFactory<R> {
	/**
	 * Method to create the sleep set state according to a given state and sleep set.
	 *
	 * Implementations must ensure that states which should be considered equal are indeed equal according to their
	 * {{@link #equals(Object)} method. In other words, the caller does not cache results of calls to this method.
	 *
	 * @param state
	 *            The given state
	 * @param sleepset
	 *            The given sleep set
	 * @return The corresponding sleep set state
	 */
	R createSleepSetState(S state, ImmutableSet<L> sleepset);

	/**
	 * Retrieves the original state from which a given sleep set state was constructed.
	 *
	 * @param sleepState
	 *            The sleep set state
	 * @return The first argument passed to the call of {@link #createSleepSetState(Object, ImmutableSet)} that returned
	 *         the given sleep set state
	 */
	S getOriginalState(R sleepState);

	/**
	 * Retrieves the sleep set for a sleep set state.
	 *
	 * @param sleepState
	 *            The sleep set state
	 * @return The second argument passed to the call of {@link #createSleepSetState(Object, ImmutableSet)} that
	 *         returned the given sleep set state
	 */
	ImmutableSet<L> getSleepSet(R sleepState);

	/**
	 * Simple implementation of the interface, which disregards the sleep set and simply returns the automaton state.
	 *
	 * As a result, the reduced automaton will be a sub-automaton of the input automaton, with some transitions removed.
	 * No unrolling of loops or unfolding of branches is performed. While guaranteeing a small automaton size in terms
	 * of states, this yields possibly non-minimal reductions (in terms of the language).
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters
	 * @param <S>
	 *            The type of states in the original (and in the reduced) automaton.
	 */
	class NoUnrolling<L, S> implements ISleepSetStateFactory<L, S, S> {
		@Override
		public S createEmptyStackState() {
			throw new UnsupportedOperationException();
		}

		@Override
		public S createSleepSetState(final S state, final ImmutableSet<L> sleepset) {
			return state;
		}

		@Override
		public S getOriginalState(final S sleepState) {
			return sleepState;
		}

		@Override
		public ImmutableSet<L> getSleepSet(final S sleepState) {
			throw new UnsupportedOperationException("state factory cannot recover sleep set");
		}
	}

	/**
	 * Simple implementation of the interface, which represents the sleep set state as a pair.
	 *
	 * Hence the reduced automaton unrolls loops and unfolds branches in the original automaton as far as necessary to
	 * achieve a minimal reduction (in terms of the language). Of course, this can lead to larger automata in terms of
	 * states; in the worst case exponentially (in the size of the alphabet) more states.
	 *
	 * @author Marcel Ebbinghaus
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters
	 * @param <S>
	 *            The type of states in the original automaton
	 */
	class MinimalReduction<L, S> implements ISleepSetStateFactory<L, S, Pair<S, ImmutableSet<L>>> {
		@Override
		public Pair<S, ImmutableSet<L>> createEmptyStackState() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Pair<S, ImmutableSet<L>> createSleepSetState(final S state, final ImmutableSet<L> sleepset) {
			return new Pair<>(state, sleepset);
		}

		@Override
		public S getOriginalState(final Pair<S, ImmutableSet<L>> sleepState) {
			return sleepState.getFirst();
		}

		@Override
		public ImmutableSet<L> getSleepSet(final Pair<S, ImmutableSet<L>> sleepState) {
			return sleepState.getSecond();
		}
	}
}
