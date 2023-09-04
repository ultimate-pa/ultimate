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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * A class that lazyly constructs the intersection production with the method from: An Automata-Theoretic Approach to
 * Linear Temporal Logic by Moshe Y. Vardi The construction is found on page 242f in Banff Higher Order Workshop 1995.
 * All product-states that have at least one finite state as a parent are finite in Rabin automata. You can imagine
 * removing all finite parents at one point, this results in removing their children at the same point and extending
 * this method to work on Rabin automata.
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letter
 * @param <STATE>
 *            type of state
 */
public class RabinIntersectionWorstCaseOptimal<LETTER, STATE> implements IRabinAutomaton<LETTER, STATE> {
	private final IRabinAutomaton<LETTER, STATE> mFirstAutomaton;
	private final IRabinAutomaton<LETTER, STATE> mSecondAutomaton;
	private final IBuchiIntersectStateFactory<STATE> mFactory;

	private Set<STATE> mInitialStates;
	private final HashMap<STATE, Triple<STATE, STATE, Boolean>> mAutomatonMap = new HashMap<>();

	/**
	 * implementation that lazyly constructs the intersection of two Rabin automata
	 *
	 * @param firstAutomaton
	 *            first Rabin automaton to intersect
	 * @param secondAutomaton
	 *            second Rabin automaton to intersect
	 * @param factory
	 *            some factory
	 */
	public RabinIntersectionWorstCaseOptimal(final IRabinAutomaton<LETTER, STATE> firstAutomaton,
			final IRabinAutomaton<LETTER, STATE> secondAutomaton, final IBuchiIntersectStateFactory<STATE> factory) {
		mFirstAutomaton = firstAutomaton;
		mSecondAutomaton = secondAutomaton;
		mFactory = factory;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		assert mFirstAutomaton.getAlphabet().equals(mSecondAutomaton.getAlphabet());
		return mFirstAutomaton.getAlphabet();
	}

	@Override
	public int size() {
		return (mFirstAutomaton.size() * mSecondAutomaton.size()) * 2;
	}

	@Override
	public String sizeInformation() {
		return "Number of states: " + size() + "\n"
				+ "The number of lazyly constructed reachable states may be smaller";
	}

	private Set<STATE> constructInitialStates() {
		final Set<STATE> result = new HashSet<>();
		for (final STATE firstInitial : mFirstAutomaton.getInitialStates()) {
			for (final STATE secondInitial : mSecondAutomaton.getInitialStates()) {
				result.add(getProducedState(firstInitial, secondInitial, false));
			}
		}
		return result;
	}

	@Override
	public Set<STATE> getInitialStates() {
		if (mInitialStates == null) {
			mInitialStates = constructInitialStates();
		}
		return mInitialStates;
	}

	@Override
	public boolean isAccepting(final STATE state) {
		final Triple<STATE, STATE, Boolean> originalStateInformation = mAutomatonMap.get(state);
		return (!originalStateInformation.getThird()
				&& mFirstAutomaton.isAccepting(originalStateInformation.getFirst()));
	}

	@Override
	public boolean isFinite(final STATE state) {
		final Triple<STATE, STATE, Boolean> originalStateInformation = mAutomatonMap.get(state);
		return (mFirstAutomaton.isFinite(originalStateInformation.getFirst())
				|| mSecondAutomaton.isFinite(originalStateInformation.getSecond()));
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state) {
		final Triple<STATE, STATE, Boolean> originalStateInformation = mAutomatonMap.get(state);
		return getComponentalSuccessors(mFirstAutomaton.getSuccessors(originalStateInformation.getFirst()),
				originalStateInformation);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {
		final Triple<STATE, STATE, Boolean> originalStateInformation = mAutomatonMap.get(state);
		return getComponentalSuccessors(mFirstAutomaton.getSuccessors(originalStateInformation.getFirst(), letter),
				originalStateInformation);
	}

	/**
	 * Constructs product states for different subautomata used in this product construction
	 *
	 * @param first
	 *            state from mFirstAutomaton
	 * @param second
	 *            state from mSecondAutomaton
	 * @param acceptedOnlyFirst
	 *            referencing the subautomaton, if true then the first automaton has accepted before reaching this
	 *            state, but we await acceptance of the second automaton
	 * @return a state which uniquely incorporates all parameters
	 */
	private STATE getProducedState(final STATE first, final STATE second, final boolean acceptedOnlyFirst) {
		final STATE result = mFactory.intersectBuchi(first, second, acceptedOnlyFirst ? 1 : 2);
		mAutomatonMap.computeIfAbsent(result, x -> new Triple<>(first, second, acceptedOnlyFirst));
		return result;
	}

	/**
	 * a indirect helper function for getSuccessors, this contains the logic for the product subautomaton construction
	 *
	 * @param firstTransitionList
	 *            a subset of valid transitions for one (active) state in the first automaton
	 * @param secondState
	 *            a active state in the second automaton
	 * @param acceptedOnlyFirst
	 *            referencing the subautomaton in which the successors will be
	 * @return a list of corresponding transitions in the intersection automaton
	 */
	private ArrayList<OutgoingInternalTransition<LETTER, STATE>> getRelatedSuccessors(
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> firstTransitionList, final STATE secondState,
			final boolean acceptedOnlyFirst) {
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final OutgoingInternalTransition<LETTER, STATE> transitionFirst : firstTransitionList) {
			final LETTER letter = transitionFirst.getLetter();
			for (final OutgoingInternalTransition<LETTER, STATE> transitionSecond : mSecondAutomaton
					.getSuccessors(secondState, letter)) {
				result.add(new OutgoingInternalTransition<>(letter,
						getProducedState(transitionFirst.getSucc(), transitionSecond.getSucc(), acceptedOnlyFirst)));
			}
		}
		return result;
	}

	/**
	 * a helper method for getSuccessors, this contains the logic on the connections in and between components
	 *
	 * @param transitionsFromFirst
	 *            a list with transitions that are valid for one (active) state in the first automaton
	 * @param originalStateInformation
	 *            the content of mAutomatonMap for the origin
	 * @return a list of corresponding transitions in the intersection automaton
	 */
	private ArrayList<OutgoingInternalTransition<LETTER, STATE>> getComponentalSuccessors(
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> transitionsFromFirst,
			final Triple<STATE, STATE, Boolean> originalStateInformation) {
		boolean hasAcceptedFirst = originalStateInformation.getThird();
		if (hasAcceptedFirst) {
			if (mSecondAutomaton.isAccepting(originalStateInformation.getSecond())) {
				hasAcceptedFirst = false;
			}
		} else if (mFirstAutomaton.isAccepting(originalStateInformation.getFirst())
				&& !mSecondAutomaton.isAccepting(originalStateInformation.getSecond())) {
			hasAcceptedFirst = true;
		}
		return getRelatedSuccessors(transitionsFromFirst, originalStateInformation.getSecond(), hasAcceptedFirst);
	}
}
