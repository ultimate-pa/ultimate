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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

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
 * @param <LETTER> Symbol
 * @param <STATE> Content
 */
public class DeterminizedState<LETTER,STATE> implements IDeterminizedState<LETTER, STATE> {
	
	/**
	 * Set of ordered pairs. The pair (present,caller) is in this set iff 
	 * present is contained in the image of caller.  
	 */
	private final Map<STATE,Set<STATE>> mCaller2presents;
	private boolean mConstructionFinished;
	private int mHashCode;
	private boolean mContainsFinal = false;
	private STATE mCachedResultingState = null;
	
	public DeterminizedState(final INestedWordAutomatonSimple<LETTER,STATE> nwa) {
		mCaller2presents = new HashMap<STATE,Set<STATE>>();
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
	 *     accepting state.
	 */
	public boolean containsFinal() {
		return mContainsFinal;
	}
	
	/**
	 * @return true iff for all pair in the set, the first entry is an
	 *     accepting state and the set is not empty
	 */
	public boolean allFinal(final INestedWordAutomatonSimple<LETTER,STATE> nwa) {
		if (mCaller2presents.isEmpty()) {
			return false;
		}
		for (final Entry<STATE, Set<STATE>> entry : mCaller2presents.entrySet()) {
			for (final STATE up : entry.getValue()) {
				if (!nwa.isFinal(up)) {
					return false;
				}
			}
		}
		return true;
	}
	

	/**
	 * By the contentFactory created content for the determinized state.
	 */
	public STATE getContent(final IStateFactory<STATE> stateFactory) {
		if (mCachedResultingState == null) {
			mCachedResultingState = stateFactory.determinize(mCaller2presents);
		}
		return mCachedResultingState;
	}


	/**
	 * Add the pair (caller,present) to the set. 
	 */
	public void addPair(final STATE caller, final STATE present, final INestedWordAutomatonSimple<LETTER,STATE> nwa) {
		if (mConstructionFinished) {
			throw new IllegalArgumentException("Construction finished must not add pairs.");
		}
		if (nwa.isFinal(present)) {
			mContainsFinal = true;
		}
		Set<STATE> presentStates = mCaller2presents.get(caller);
		if (presentStates == null) {
			presentStates = new HashSet<STATE>();
			mCaller2presents.put(caller, presentStates);
		}
		presentStates.add(present);
	}
	
	
	/**
	 * Two DeterminizedStates are equivalent iff they represent the same set of
	 * state pairs. 
	 */
	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(final Object obj) {
		if (obj instanceof DeterminizedState) {
			final DeterminizedState<LETTER,STATE> detState = (DeterminizedState<LETTER,STATE>) obj;
			return mCaller2presents.equals(detState.mCaller2presents);
		} else {
			return false;
		}
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
	
	public boolean isSubsetOf(final DeterminizedState<LETTER,STATE> superset) {
		for (final STATE down : getDownStates()) {
			final Set<STATE> supersetUpStates = superset.getUpStates(down);
			if (supersetUpStates == null) {
				return false;
			} else {
				for (final STATE up : getUpStates(down)) {
					if (!supersetUpStates.contains(up)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	public boolean isEmpty() {
		return mCaller2presents.isEmpty();
	}
	
	public int degreeOfNondeterminism() {
		int degree = 0;
		for ( final STATE down : getDownStates()) {
			degree += getUpStates(down).size();
		}
		return degree;
	}
}
