/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;




//TODO deal with automata with large alphabet
public class StateWa implements IStateWa, Comparable<StateWa> {

	private final int mId;
	private final Map<Integer, IntSet> mSuccessors;
	public StateWa(int id) {
		this.mId = id;
		this.mSuccessors = new HashMap<>();
	}
	
	@Override
	public int getId() {
		return mId;
	}

	@Override
	public void addSuccessor(int letter, int state) {
		IntSet succs = mSuccessors.get(letter);
		if(succs == null) {
			succs =  UtilIntSet.newIntSet();
		}
		succs.set(state);
		mSuccessors.put(letter, succs);
	}

	@Override
	public IntSet getSuccessors(int letter) {
		IntSet succs = mSuccessors.get(letter);
		if(succs == null) { // transition function may not be complete
			return UtilIntSet.newIntSet();
		}
		return succs.clone();
	}

	@Override
	public Set<Integer> getEnabledLetters() {
		return Collections.unmodifiableSet(mSuccessors.keySet());
	}

	@Override
	public int compareTo(StateWa other) {
		return mId - other.mId;
	}
	
	@Override
	public boolean equals(Object other) {
		if(this == other) return true;
		if(!(other instanceof StateWa)) {
			return false;
		}
		StateWa otherState = (StateWa)other;
		return otherState.mId == this.mId;
	}
	
	@Override
	public int hashCode() {
		return mId;
	}
	
	@Override
	public String toString() {
		return "s" + mId;
	}

}
