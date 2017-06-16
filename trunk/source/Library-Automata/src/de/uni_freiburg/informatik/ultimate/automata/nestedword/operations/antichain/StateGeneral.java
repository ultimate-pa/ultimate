/*
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.antichain;

import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;


/**
 * @author Yong Li (liyong@ios.ac.cn)
 * */
public class StateGeneral implements IState, Comparable<StateGeneral> {

	private final int mId;
	private final Map<Integer, BitSet> mSuccessors;
	private final BitSet mVisitedLetters = new BitSet();
	
	public StateGeneral(int id) {
		this.mId = id;
		this.mSuccessors = new HashMap<>();
	}
	
	@Override
	public int getId() {
		return mId;
	}

	@Override
	public void addSuccessor(int letter, int state) {
		// TODO Auto-generated method stub
		BitSet succs = mSuccessors.get(letter);
		mVisitedLetters.set(letter);
		if(succs == null) {
			succs = new BitSet();
		}
		succs.set(state);
		mSuccessors.put(letter, succs);
	}

	@Override
	public BitSet getSuccessors(int letter) {
		// TODO Auto-generated method stub
		BitSet succs = mSuccessors.get(letter);
		if(succs == null) { // transition function may not be complete
			return new BitSet();
		}
		return (BitSet)succs.clone();
	}

	@Override
	public Set<Integer> getEnabledLetters() {
		// TODO Auto-generated method stub
		return Collections.unmodifiableSet(mSuccessors.keySet());
	}

	@Override
	public int compareTo(StateGeneral other) {
		// TODO Auto-generated method stub
		return mId - other.mId;
	}
	
	
	public boolean equals(Object other) {
		if(!(other instanceof StateGeneral)) {
			return false;
		}
		StateGeneral otherState = (StateGeneral)other;
		return otherState.mId == this.mId;
	}
	
	public int hashCode() {
		return mId;
	}
	
	public String toString() {
		return "s" + mId;
	}

	@Override
	public boolean isLetterVisited(int letter) {
		// TODO Auto-generated method stub
		return mVisitedLetters.get(letter);
	}

}
