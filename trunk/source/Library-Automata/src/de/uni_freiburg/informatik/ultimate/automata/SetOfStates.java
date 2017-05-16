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
 * Represents a set of states of an automaton. States can be initial or
 * accepting.
 * This class stores initial and accepting states explicitly which allows
 * one to iterate over these sets.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class SetOfStates<STATE> {

	private final Set<STATE> mStates = new HashSet<STATE>();
	private final Set<STATE> mInitialStates = new HashSet<STATE>();
	private final Set<STATE> mAcceptingStates = new HashSet<STATE>();


	public void addState(final boolean isInitial, final boolean isAccepting, final STATE state) {
		if (state == null) {
			throw new NullPointerException("state must not be null");
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
	
	public void removeState(final STATE state) {
		final boolean modified = mStates.remove(state);
		if (!modified) {
			throw new IllegalArgumentException("Not a state: " + state);
		}
		mInitialStates.remove(state);
		mAcceptingStates.remove(state);
	}
	
	public void makeStateNonInitial(final STATE state) {
		if (!mStates.contains(state)) {
			throw new IllegalArgumentException("Not a state: " + state);
		}
		final boolean modified = mInitialStates.remove(state);
		if (!modified) {
			throw new IllegalArgumentException("Can only make initial state non-Initial");
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

	public boolean isInitial(final STATE state) {
		if (mStates.contains(state)) {
			return mInitialStates.contains(state);
		} else {
			throw new IllegalArgumentException("Not a state: " + state);
		}
	}

	public boolean isAccepting(final STATE state) {
		if (mStates.contains(state)) {
			return mAcceptingStates.contains(state);
		} else {
			throw new IllegalArgumentException("Not a state: " + state);
		}
	}

}
