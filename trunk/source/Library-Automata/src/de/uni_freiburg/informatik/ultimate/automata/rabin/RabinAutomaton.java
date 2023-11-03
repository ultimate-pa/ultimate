/*
 * Copyright (C) 2023 Philipp Müller (pm251@venus.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TransformIterator;

/**
 * A class for explicitly declaring a Rabin automaton by declaring the relevant sets
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class RabinAutomaton<LETTER, STATE> implements IRabinAutomaton<LETTER, STATE> {
	private final Set<LETTER> mAlphabet;
	private final Set<STATE> mStates;
	private final Set<STATE> mInitialStates;
	private final Set<STATE> mAcceptingStates;
	private final Set<STATE> mFiniteStates;
	private final NestedMap2<STATE, LETTER, Set<STATE>> mTransitions;

	/**
	 * A Rabin Automaton explicitly defined by the parameters
	 *
	 * @param alphabet
	 *            The valid input characters for this automaton (should be a superset of the characters in transitions)
	 * @param states
	 *            The valid states of the automaton (should be a superset of the states in initialStates,
	 *            acceptingStates, finiteStates and transitions)
	 * @param initialStates
	 *            The states that are active when no letter/word has been read
	 * @param acceptingStates
	 *            States that when infinitely often visited lead to the acceptance of the input
	 * @param finiteStates
	 *            States that can only be visited a finite amount of times, iff the automaton accepts
	 * @param transitions
	 *            The transitions from one state to another for a one letter input
	 */
	public RabinAutomaton(final Set<LETTER> alphabet, final Set<STATE> states, final Set<STATE> initialStates,
			final Set<STATE> acceptingStates, final Set<STATE> finiteStates,
			final NestedMap2<STATE, LETTER, Set<STATE>> transitions) {
		mAlphabet = alphabet;
		mStates = states;
		mInitialStates = initialStates;
		mAcceptingStates = acceptingStates;
		mFiniteStates = finiteStates;
		mTransitions = transitions;
	}

	public Set<STATE> getStates() {
		return mStates;
	}

	public Set<STATE> getAcceptingStates() {
		return mAcceptingStates;
	}

	public Set<STATE> getFiniteStates() {
		return mFiniteStates;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public int size() {
		return mStates.size();
	}

	@Override
	public String sizeInformation() {
		return "Number of states: " + size() + ", number of transitions: "
				+ mTransitions.values().mapToInt(Set::size).sum();
	}

	@Override
	public Set<STATE> getInitialStates() {
		return mInitialStates;
	}

	@Override
	public boolean isAccepting(final STATE state) {
		return mAcceptingStates.contains(state);
	}

	@Override
	public boolean isFinite(final STATE state) {
		return mFiniteStates.contains(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state) {
		final Map<LETTER, Set<STATE>> successorMap = mTransitions.get(state);
		if (successorMap == null) {
			return () -> Collections.emptyIterator();
		}
		return () -> successorMap.entrySet().stream().flatMap(
				entry -> entry.getValue().stream().map(succ -> new OutgoingInternalTransition<>(entry.getKey(), succ)))
				.iterator();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {
		final Set<STATE> successors = mTransitions.get(state, letter);
		if (successors == null) {
			return () -> Collections.emptyIterator();
		}
		return () -> new TransformIterator<>(successors.iterator(), x -> new OutgoingInternalTransition<>(letter, x));
	}

	public NestedMap2<STATE, LETTER, Set<STATE>> getTransitions() {
		return mTransitions;
	}
}
