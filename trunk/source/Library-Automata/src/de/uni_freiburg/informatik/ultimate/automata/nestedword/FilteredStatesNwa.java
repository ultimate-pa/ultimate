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

import java.util.List;
import java.util.Objects;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.FilteredIterable;

/**
 * Given a nested-word automaton, represents a modified automaton where certain states (and all transitions leading to
 * or from these states) have been removed.
 *
 * This class provides similar functionality to {@link NestedWordAutomatonFilteredStates}, but allows the given
 * underlying automaton to be constructed on-demand. In technical terms, the automaton need only implement
 * {@link INwaOutgoingLetterAndTransitionProvider}, not {@link INestedWordAutomaton}.
 *
 * The implementation is fully on-demand, no caching of states or transitions is performed (though the underlying
 * automaton may cache states and transitions).
 *
 * @param <LETTER>
 *            the type of letters read by the automaton
 * @param <STATE>
 *            the type of states in the (given resp. resulting) automaton
 */
public class FilteredStatesNwa<LETTER, STATE> implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mUnderlying;
	private final Predicate<STATE> mIsPrunedState;

	/**
	 * Creates a new automaton where certain states have been removed from the given automaton.
	 *
	 * @param underlying
	 *            The given automaton on which the new automaton is based.
	 * @param isPrunedState
	 *            A predicate returning {@code true} for all states that should be removed from the underlying automaton
	 */
	public FilteredStatesNwa(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> underlying,
			final Predicate<STATE> isPrunedState) {
		mUnderlying = Objects.requireNonNull(underlying);
		mIsPrunedState = Objects.requireNonNull(isPrunedState);
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mUnderlying.getVpAlphabet();
	}

	@Override
	public STATE getEmptyStackState() {
		return mUnderlying.getEmptyStackState();
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		return new FilteredIterable<>(mUnderlying.getInitialStates(), Predicate.not(mIsPrunedState));
	}

	@Override
	public boolean isInitial(final STATE state) {
		return !mIsPrunedState.test(state) && mUnderlying.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return !mIsPrunedState.test(state) && mUnderlying.isFinal(state);
	}

	@Override
	public int size() {
		// Somewhat imprecise, but good enough for now. Could be refined later.
		return mUnderlying.size();
	}

	@Override
	public String sizeInformation() {
		// Somewhat imprecise, but good enough for now. Could be refined later.
		return mUnderlying.sizeInformation();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		if (mIsPrunedState.test(state)) {
			return List.of();
		}
		return new FilteredIterable<>(mUnderlying.internalSuccessors(state, letter),
				transition -> !mIsPrunedState.test(transition.getSucc()));
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		if (mIsPrunedState.test(state)) {
			return List.of();
		}
		return new FilteredIterable<>(mUnderlying.callSuccessors(state, letter),
				transition -> !mIsPrunedState.test(transition.getSucc()));
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		if (mIsPrunedState.test(state) || mIsPrunedState.test(hier)) {
			return List.of();
		}
		return new FilteredIterable<>(mUnderlying.returnSuccessors(state, hier, letter),
				transition -> !mIsPrunedState.test(transition.getSucc()));
	}
}
