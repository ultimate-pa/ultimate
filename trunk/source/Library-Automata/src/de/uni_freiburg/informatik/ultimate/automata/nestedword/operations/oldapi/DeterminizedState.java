/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;

/**
 * Determinized state in the classical determinization algorithm for NWAs.
 * While determinizing a nondeterministic finite automaton NFA using the
 * powerset construction a state in the determinized automaton corresponds to a
 * subset of the states of A.
 * For NWAs there exists a similar construction. Let A be a nondeterministic
 * NWA. A state in the determinized NWA corresponds to a set of ordered pairs
 * of A's states. In such a pair, the first state (present) represents a
 * state "in which A can be at the moment", the second state (caller)
 * represents the state "before the last call statement", i.e. the second state
 * represents "the top of the stack".
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Symbol
 * @param <STATE>
 *            Content
 */
public class DeterminizedState<LETTER, STATE> implements IDeterminizedState<LETTER, STATE> {
	/**
	 * Set of ordered pairs. The pair (present,caller) is in this set iff
	 * present is contained in the image of caller.
	 */
	private final Map<STATE, Set<STATE>> mCaller2presents;
	private boolean mContainsFinal;
	private STATE mCachedResultingState;

	private boolean mConstructionFinished;
	private int mHashCode;

	/**
	 * Constructor.
	 * <p>
	 * TODO Christian 2016-09-10: The parameter is not used - a bug?
	 * 
	 * @param nwa
	 *            nested word automaton
	 */
	public DeterminizedState(final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		mCaller2presents = new HashMap<>();
	}

	@Override
	public Set<STATE> getDownStates() {
		return mCaller2presents.keySet();
	}

	@Override
	public Set<STATE> getUpStates(final STATE caller) {
		return mCaller2presents.get(caller);
	}

	/**
	 * @return true iff for some pair in the set, the first entry is an
	 *         accepting state.
	 */
	public boolean containsFinal() {
		return mContainsFinal;
	}

	/**
	 * @param nwa
	 *            A nested word automaton.
	 * @return true iff for all pair in the set, the first entry is an
	 *         accepting state and the set is not empty
	 */
	public boolean allFinal(final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		if (mCaller2presents.isEmpty()) {
			return false;
		}
		for (final Entry<STATE, Set<STATE>> entry : mCaller2presents.entrySet()) {
			for (final STATE upState : entry.getValue()) {
				if (!nwa.isFinal(upState)) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * @param stateFactory
	 *            A state factory.
	 * @return content created by the factory for the determinized state
	 */
	public STATE getContent(final IDeterminizeStateFactory<STATE> stateFactory) {
		if (mCachedResultingState == null) {
			mCachedResultingState = stateFactory.determinize(mCaller2presents);
		}
		return mCachedResultingState;
	}

	/**
	 * Adds the pair (caller,present) to the nested word automaton.
	 * 
	 * @param caller
	 *            caller state
	 * @param present
	 *            present state
	 * @param nwa
	 *            nested word automaton
	 */
	public void addPair(final STATE caller, final STATE present, final INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		if (mConstructionFinished) {
			throw new IllegalArgumentException("Construction finished must not add pairs.");
		}
		if (nwa.isFinal(present)) {
			mContainsFinal = true;
		}
		Set<STATE> presentStates = mCaller2presents.get(caller);
		if (presentStates == null) {
			presentStates = new HashSet<>();
			mCaller2presents.put(caller, presentStates);
		}
		presentStates.add(present);
	}

	/**
	 * Two DeterminizedStates are equivalent iff they represent the same set of
	 * state pairs.
	 */
	@Override
	public boolean equals(final Object obj) {
		if (obj == null || this.getClass() != obj.getClass()) {
			return false;
		}
		final DeterminizedState<?, ?> detState = (DeterminizedState<?, ?>) obj;
		return mCaller2presents.equals(detState.mCaller2presents);
	}

	@Override
	public int hashCode() {
		if (!mConstructionFinished) {
			mHashCode = mCaller2presents.hashCode();
			mConstructionFinished = true;
		}
		return mHashCode;
	}

	@Override
	public String toString() {
		return mCaller2presents.toString();
	}

	/**
	 * @param superset
	 *            Another determinized state.
	 * @return {@code true} iff all states represented by {@code this} are also represented by the other determinized
	 *         state
	 */
	public boolean isSubsetOf(final DeterminizedState<LETTER, STATE> superset) {
		for (final STATE downState : getDownStates()) {
			final Set<STATE> supersetUpStates = superset.getUpStates(downState);
			if (supersetUpStates == null) {
				return false;
			}
			for (final STATE upState : getUpStates(downState)) {
				if (!supersetUpStates.contains(upState)) {
					return false;
				}
			}
		}
		return true;
	}

	public boolean isEmpty() {
		return mCaller2presents.isEmpty();
	}

	/**
	 * @return The degree of nondeterminism with respect to outgoing transitions.
	 */
	public int degreeOfNondeterminism() {
		int degree = 0;
		for (final STATE down : getDownStates()) {
			degree += getUpStates(down).size();
		}
		return degree;
	}
}
