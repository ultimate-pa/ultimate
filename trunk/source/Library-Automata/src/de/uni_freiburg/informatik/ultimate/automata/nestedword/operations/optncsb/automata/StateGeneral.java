package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;


//TODO deal with automata with large alphabet
public class StateGeneral implements IState, Comparable<StateGeneral> {

	private final int mId;
	private final Map<Integer, IntSet> mSuccessors;
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
	public int compareTo(StateGeneral other) {
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

}
