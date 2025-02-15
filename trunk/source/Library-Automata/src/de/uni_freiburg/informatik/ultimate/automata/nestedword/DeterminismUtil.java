/*
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

/**
 * Utility class for the safe implementation of, or operation on deterministic automata.
 */
public final class DeterminismUtil {
	private DeterminismUtil() {
		// utility class cannot be instantiated
	}

	/**
	 * Indicates that an automaton that was expected to be deterministic (i.e., have at most one initial state and at
	 * most one transition for each latter in the alphabet at each state) is indeed not deterministic.
	 */
	public static final class NondeterminismException extends RuntimeException {
		private static final long serialVersionUID = 1227455756844529361L;

		public NondeterminismException(final String message) {
			super(message);
		}
	}

	/**
	 * Indicates that an automaton that was expected to be total (i.e., have at least one initial state and at least one
	 * transition for each letter in the alphabet at each state) is indeed not total.
	 */
	public static final class NonTotalityException extends RuntimeException {
		private static final long serialVersionUID = 450393240055623620L;

		public NonTotalityException(final String message) {
			super(message);
		}
	}

	/**
	 * Retrieves the unique initial state of a total deterministic automaton.
	 *
	 * @param <S>
	 *            the type of states in the automaton
	 * @param automaton
	 *            the automaton
	 * @return the given automaton's initial state
	 * @throws NonTotalityException
	 *             if the automaton does not have any initial state
	 * @throws NondeterminismException
	 *             if the automaton has multiple initial states
	 */
	public static <S> S getInitialState(final INwaOutgoingLetterAndTransitionProvider<?, S> automaton) {
		final var iterator = automaton.getInitialStates().iterator();
		if (!iterator.hasNext()) {
			throw new NonTotalityException("Automaton does not have any initial state");
		}

		final S initialState = iterator.next();
		if (iterator.hasNext()) {
			throw new NondeterminismException("Automaton has multiple initial states");
		}
		return initialState;
	}

	/**
	 * Retrieves the unique outgoing transition of some state in a total deterministic automaton, for a given letter.
	 *
	 * @param <L>
	 *            the type of letters read by the automaton
	 * @param <S>
	 *            the type of states in the automaton
	 * @param automaton
	 *            the automaton
	 * @param state
	 *            the state of the automaton whose transitions are examined
	 * @param letter
	 *            a letter in the automaton's internal alphabet for which the transition should be retrieved
	 * @return the outgoing transition for the given state and letter
	 * @throws NonTotalityException
	 *             if the given state does not have a transition for the given letter
	 * @throws NondeterminismException
	 *             if the given state has multiple transitions for the given letter
	 */
	public static <L, S> OutgoingInternalTransition<L, S> getTotalDeterministicInternalTransition(
			final INwaOutgoingLetterAndTransitionProvider<L, S> automaton, final S state, final L letter) {
		assert automaton.getVpAlphabet().getInternalAlphabet().contains(letter) : "Letter is not in alphabet";

		final var iterator = automaton.internalSuccessors(state, letter).iterator();
		if (!iterator.hasNext()) {
			throw new NonTotalityException(
					"Automaton does not have a transition for letter " + letter + " at state " + state);
		}

		final OutgoingInternalTransition<L, S> transition = iterator.next();
		if (iterator.hasNext()) {
			throw new NondeterminismException(
					"Automaton has multiple transitions for letter " + letter + " at state " + state);
		}
		return transition;
	}

	/**
	 * Retrieves the unique successor of some state in a total deterministic automaton, for a given letter.
	 *
	 * @param <L>
	 *            the type of letters read by the automaton
	 * @param <S>
	 *            the type of states in the automaton
	 * @param automaton
	 *            the automaton
	 * @param state
	 *            the state of the automaton whose transitions are examined
	 * @param letter
	 *            a letter in the automaton's internal alphabet for which the successor should be retrieved
	 * @return the successor state reached by reading the given letter in the given state
	 * @throws NonTotalityException
	 *             if the given state does not have a successor for the given letter
	 * @throws NondeterminismException
	 *             if the given state has multiple successors for the given letter
	 */
	public static <L, S> S getTotalDeterministicInternalSuccessor(
			final INwaOutgoingLetterAndTransitionProvider<L, S> automaton, final S state, final L letter) {
		return getTotalDeterministicInternalTransition(automaton, state, letter).getSucc();
	}
}
