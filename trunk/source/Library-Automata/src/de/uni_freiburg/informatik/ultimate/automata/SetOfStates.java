/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * Represents a set of states of an automaton. States can be initial and/or accepting. This class stores initial and
 * accepting states explicitly which allows iteration and modification over these sets.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <STATE>
 *            type of states
 */
public class SetOfStates<STATE> {
	private static final String NOT_A_STATE = "Not a state: ";

	private final Set<STATE> mStates = new HashSet<>();
	private final Set<STATE> mInitialStates = new HashSet<>();
	private final Set<STATE> mAcceptingStates = new HashSet<>();
	/**
	 * Auxiliary state that we use to mark the empty stack.
	 * If we use strings to represent states, we usually use the Euro symbol €
	 * as emtpy stack symbol.
	 */
	private final STATE mEmptyStackState;

	public SetOfStates(final STATE emptyStackState) {
		super();
		mEmptyStackState = emptyStackState;
	}

	/**
	 * Adds a state.
	 *
	 * @param isInitial
	 *            {@code true} iff the state is initial
	 * @param isAccepting
	 *            {@code true} iff the state is accepting
	 * @param state
	 *            state
	 */
	@SuppressWarnings("squid:S2301")
	public void addState(final boolean isInitial, final boolean isAccepting, final STATE state) {
		if (state == null) {
			throw new IllegalArgumentException("state must not be null");
		}
		if (mStates.contains(state)) {
			throw new IllegalArgumentException("state already exists: " + state);
		}
		mStates.add(state);
		if (isInitial) {
			mInitialStates.add(state);
		}
		if (isAccepting) {
			mAcceptingStates.add(state);
		}
	}

	/**
	 * Removes a state.
	 *
	 * @param state
	 *            state
	 */
	public void removeState(final STATE state) {
		final boolean modified = mStates.remove(state);
		if (!modified) {
			throw new IllegalArgumentException(NOT_A_STATE + state);
		}
		mInitialStates.remove(state);
		mAcceptingStates.remove(state);
	}

	/**
	 * Makes an initial state non-initial.
	 *
	 * @deprecated
	 * 			Do not modify existing automata, construct new automata instead.
	 */
	@Deprecated
	public void makeStateNonInitial(final STATE state) {
		if (!mStates.contains(state)) {
			throw new IllegalArgumentException(NOT_A_STATE + state);
		}
		final boolean modified = mInitialStates.remove(state);
		if (!modified) {
			throw new IllegalArgumentException("Can only make initial states non-initial");
		}
	}

	public Set<STATE> getStates() {
		return Collections.unmodifiableSet(mStates);
	}

	public Set<STATE> getInitialStates() {
		return Collections.unmodifiableSet(mInitialStates);
	}

	public Set<STATE> getAcceptingStates() {
		return Collections.unmodifiableSet(mAcceptingStates);
	}

	public STATE getEmptyStackState() {
		return mEmptyStackState;
	}

	/**
	 * @param state
	 *            State.
	 * @return {@code true} iff the state is initial
	 */
	public boolean isInitial(final STATE state) {
		if (!mStates.contains(state)) {
			throw new IllegalArgumentException(NOT_A_STATE + state);
		}
		return mInitialStates.contains(state);
	}

	/**
	 * @param state
	 *            State.
	 * @return {@code true} iff the state is accepting
	 */
	public boolean isAccepting(final STATE state) {
		if (!mStates.contains(state)) {
			throw new IllegalArgumentException(NOT_A_STATE + state);
		}
		return mAcceptingStates.contains(state);
	}

}
