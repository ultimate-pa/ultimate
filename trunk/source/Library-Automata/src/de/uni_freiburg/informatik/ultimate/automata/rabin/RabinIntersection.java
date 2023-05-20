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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * A class that lazyly constructs the intersection production from Udi Boker: “Why these automata types?,” in LPAR-22.
 * 22nd International Conference on Logic for Programming, Artificial Intelligence and Reasoning, Awassa, Ethiopia,
 * 16-21 November 2018 (G. Barthe, G. Sutcliffe, and M. Veanes, eds.), vol. 57 of EPiC Series in Computing, pp. 143–163,
 * EasyChair, 2018. The construction is found page 7, Theorem 1!
 *
 * This class reduces the reachable state size by enforcing the acceptance of the first automaton before transitioning
 * to another component. Runtime can be different for switching the automata parameters.
 *
 * This construction has less states than the 2 component one, if the first automaton has only few accepting states and
 * relatively many finite states in at least one automaton.
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letter
 * @param <STATE>
 *            type of state
 * @param <FACTORY>
 *            type of factory
 */
public class RabinIntersection<LETTER, STATE, FACTORY extends IBuchiIntersectStateFactory<STATE>>
		implements IRabinAutomaton<LETTER, STATE> {
	private static final int NUMBER_OF_COMPONENTS = 3;

	private final IRabinAutomaton<LETTER, STATE> mFirstAutomaton;
	private final IRabinAutomaton<LETTER, STATE> mSecondAutomaton;
	private final FACTORY mFactory;

	private Set<STATE> mInitialStates;
	private final HashMap<STATE, Triple<STATE, STATE, Integer>> mAutomatonMap = new HashMap<>();

	/**
	 * implementation that lazyly constructs the intersection of two Rabin automata
	 *
	 * @param firstAutomaton
	 *            first Rabin automaton to intersect
	 * @param secondAutomaton
	 *            second Rabin automaton to intersect
	 * @param factory
	 *            some {@link IRainbowStateFactory} & {@link IIntersectionStateFactory} for STATE
	 */
	public RabinIntersection(final IRabinAutomaton<LETTER, STATE> firstAutomaton,
			final IRabinAutomaton<LETTER, STATE> secondAutomaton, final FACTORY factory) {
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
		return (mFirstAutomaton.size() * mSecondAutomaton.size()) * NUMBER_OF_COMPONENTS;
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
				result.add(getProducedState(firstInitial, secondInitial, 0));
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
		return (mAutomatonMap.get(state).getThird() == 1);
	}

	@Override
	public boolean isFinite(final STATE state) {
		final Triple<STATE, STATE, Integer> originalStateInformation = mAutomatonMap.get(state);
		return (originalStateInformation.getThird() == 0
				&& (mFirstAutomaton.isFinite(originalStateInformation.getFirst())
						|| mSecondAutomaton.isFinite(originalStateInformation.getSecond())));
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state) {
		final Triple<STATE, STATE, Integer> originalStateInformation = mAutomatonMap.get(state);
		return getComponentalSuccessors(mFirstAutomaton.getSuccessors(originalStateInformation.getFirst()),
				originalStateInformation.getSecond(), originalStateInformation.getThird());
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {
		final Triple<STATE, STATE, Integer> originalStateInformation = mAutomatonMap.get(state);
		return getComponentalSuccessors(mFirstAutomaton.getSuccessors(originalStateInformation.getFirst(), letter),
				originalStateInformation.getSecond(), originalStateInformation.getThird());
	}

	/**
	 * Constructs product states for different subautomata used in this product construction
	 *
	 * @param first
	 *            state from mFirstAutomaton
	 * @param second
	 *            state from mSecondAutomaton
	 * @param component
	 *            a component referencing the subautomaton
	 * @return a state which uniquely incorporates all parameters
	 */
	private STATE getProducedState(final STATE first, final STATE second, final int component) {
		final STATE result;
		// acceptance of the second automaton is a necessary condition for all transitions from 2->0 using transitions
		// instead of states for this evidence reduces the automaton by the size of component 3
		if (component == NUMBER_OF_COMPONENTS) {
			if (!mSecondAutomaton.isAccepting(second) || mFirstAutomaton.isFinite(first)
					|| mSecondAutomaton.isFinite(second)) {
				return null;
			}
			result = mFactory.intersectBuchi(first, second, 0);
			mAutomatonMap.computeIfAbsent(result, x -> new Triple<>(first, second, 0));
			return result;
		}
		result = mFactory.intersectBuchi(first, second, component);
		// since we already need this map we can use it as a cache
		if (!mAutomatonMap.containsKey(result)) {
			// This checks for B', these are all states derived from finite states
			// only component 0 retains finite states, this should reduce the state set without changing the accepted
			// language!
			if (mFirstAutomaton.isFinite(first) || mSecondAutomaton.isFinite(second)) {
				if (component != 0) {
					return null;
				}
			} else
			// This checks for B" instead of making states finite we can delete them to reduce the state size
			// it also makes all remaining states in component 1 accepting
			if (component == 1 && !mFirstAutomaton.isAccepting(first)) {
				return null;
			}
			mAutomatonMap.put(result, new Triple<>(first, second, component));
		}
		return result;

	}

	/**
	 * a indirect helper function for getSuccessors, this contains the logic for the product subautomaton construction
	 *
	 * @param firstTransitionList
	 *            a subset of valid transitions for one (active) state in the first automaton
	 * @param secondState
	 *            a active state in the second automaton
	 * @param successorComponent
	 *            the component in the intersection which should be reached by the computed transitions
	 * @return a list of corresponding transitions in the intersection automaton
	 */
	private ArrayList<OutgoingInternalTransition<LETTER, STATE>> getRelatedSuccessors(
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> firstTransitionList, final STATE secondState,
			final int successorComponent) {
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();

		for (final OutgoingInternalTransition<LETTER, STATE> transitionFirst : firstTransitionList) {
			final LETTER letter = transitionFirst.getLetter();
			for (final OutgoingInternalTransition<LETTER, STATE> transitionSecond : mSecondAutomaton
					.getSuccessors(secondState, letter)) {
				final STATE producedState =
						getProducedState(transitionFirst.getSucc(), transitionSecond.getSucc(), successorComponent);
				if (producedState != null) {
					result.add(new OutgoingInternalTransition<>(letter, producedState));
				}
			}
		}
		return result;
	}

	/**
	 * a helper method for getSuccessors, this contains the logic on the connections in and between components
	 *
	 * @param transitionsFromFirst
	 *            a list with transitions that are valid for one (active) state in the first automaton
	 * @param originalSecondState
	 *            a state in the second automaton which is active
	 * @param originalComponent
	 *            the component from which transitions start
	 * @return a list of corresponding transitions in the intersection automaton
	 */
	private ArrayList<OutgoingInternalTransition<LETTER, STATE>> getComponentalSuccessors(
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> transitionsFromFirst,
			final STATE originalSecondState, final int originalComponent) {
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result =
				getRelatedSuccessors(transitionsFromFirst, originalSecondState, originalComponent + 1);
		if (originalComponent != 1) {
			result.addAll(getRelatedSuccessors(transitionsFromFirst, originalSecondState, originalComponent));
		}
		return result;
	}
}
