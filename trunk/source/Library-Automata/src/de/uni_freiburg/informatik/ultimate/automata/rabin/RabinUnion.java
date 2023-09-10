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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBlackWhiteStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TransformIterator;

/**
 * class to lazyly construct the union of two Rabin automata
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            type of letter
 * @param <STATE>
 *            type of state
 */
public class RabinUnion<LETTER, STATE> implements IRabinAutomaton<LETTER, STATE> {
	private final IRabinAutomaton<LETTER, STATE> mFirstAutomaton;
	private final IRabinAutomaton<LETTER, STATE> mSecondAutomaton;
	private final IBlackWhiteStateFactory<STATE> mFactory;
	private Set<STATE> mInitialStates;
	// 1 ~ firstAutomaton ~ Black, 0 ~ secondAutomaton ~ White
	HashMap<STATE, Pair<Boolean, STATE>> mAutomatonMap = new HashMap<>();

	/**
	 * implementation that lazyly constructs the union of two Rabin automata
	 *
	 * @param firstAutomaton
	 *            first Rabin automaton to unite
	 * @param secondAutomaton
	 *            second Rabin automaton to unite
	 * @param factory
	 *            some BlackWhiteStateFactory for STATE
	 */
	public RabinUnion(final IRabinAutomaton<LETTER, STATE> firstAutomaton,
			final IRabinAutomaton<LETTER, STATE> secondAutomaton, final IBlackWhiteStateFactory<STATE> factory) {
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
		return mFirstAutomaton.size() + mSecondAutomaton.size();
	}

	@Override
	public String sizeInformation() {
		return "Number of states: " + size() + "\n" + "of these there are: " + mFirstAutomaton.size()
				+ " from firstAutomaton and: " + mSecondAutomaton.size() + " from secondAutomaton";
	}

	private Set<STATE> constructInitialStates() {
		final Set<STATE> result = new HashSet<>();
		for (final STATE state : mFirstAutomaton.getInitialStates()) {
			result.add(getUnionState(state, true));
		}
		for (final STATE state : mSecondAutomaton.getInitialStates()) {
			result.add(getUnionState(state, false));
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
		final Pair<Boolean, STATE> originalStateInformation = mAutomatonMap.get(state);
		return getSubautomaton(originalStateInformation.getFirst()).isAccepting(originalStateInformation.getSecond());
	}

	@Override
	public boolean isFinite(final STATE state) {
		final Pair<Boolean, STATE> originalStateInformation = mAutomatonMap.get(state);
		return getSubautomaton(originalStateInformation.getFirst()).isFinite(originalStateInformation.getSecond());
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state) {
		final Pair<Boolean, STATE> originalStateInformation = mAutomatonMap.get(state);
		final boolean isFirst = originalStateInformation.getFirst();

		return constructSuccessors(getSubautomaton(isFirst).getSuccessors(originalStateInformation.getSecond()),
				isFirst);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {
		final Pair<Boolean, STATE> originalStateInformation = mAutomatonMap.get(state);
		final boolean isFirst = originalStateInformation.getFirst();

		return constructSuccessors(getSubautomaton(isFirst).getSuccessors(originalStateInformation.getSecond(), letter),
				isFirst);
	}

	/**
	 * a helper function for getSucessors
	 */
	private Iterable<OutgoingInternalTransition<LETTER, STATE>> constructSuccessors(
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> subautomatonTransitions, final boolean isFirst) {
		return () -> new TransformIterator<>(subautomatonTransitions.iterator(),
				x -> new OutgoingInternalTransition<>(x.getLetter(), getUnionState(x.getSucc(), isFirst)));
	}

	/**
	 * this method creates different states, even if states in mFirstAutomaton and mSecondAutomaton have the same name,
	 * if a UnionState was already created this method returns its value without further computation
	 *
	 * @param originalState
	 *            a state from either of mFirstAutomaton or mSecondAutomaton
	 * @param isFirst
	 *            a boolean that declares explicitly if this state is from mFirstAutomaton or mSecondAutomaton
	 * @return
	 */
	private STATE getUnionState(final STATE originalState, final boolean isFirst) {
		final STATE newState;
		if (isFirst) {
			newState = mFactory.getBlackContent(originalState);
		} else {
			newState = mFactory.getWhiteContent(originalState);
		}
		if (mAutomatonMap.containsKey(newState)) {
			return newState;
		}
		mAutomatonMap.put(newState, new Pair<>(isFirst, originalState));
		return newState;
	}

	/**
	 * a mapping function from a boolean to both subautomata
	 *
	 * @param isFirst
	 *            a key, true maps to the mFirstAutomaton, second to mSecondAutomaton
	 * @return the corresponding subautomaton
	 */
	private IRabinAutomaton<LETTER, STATE> getSubautomaton(final boolean isFirst) {
		if (isFirst) {
			return mFirstAutomaton;
		}
		return mSecondAutomaton;
	}
}
