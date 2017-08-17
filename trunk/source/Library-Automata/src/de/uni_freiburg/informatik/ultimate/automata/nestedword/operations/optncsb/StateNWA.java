package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;


import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.StateGeneral;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntIterator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;

public class StateNWA<LETTER, STATE> extends StateGeneral {

	private BuchiSimpleNWA<LETTER, STATE> mBuchi;
	
	private Set<Integer> mEnabledLetters;
	
	public StateNWA(BuchiSimpleNWA<LETTER, STATE> buchi, int id) {
		super(id);
		this.mBuchi = buchi;
		this.mEnabledLetters = new HashSet<>();
	}
	
	
	@Override
	public Set<Integer> getEnabledLetters() {
		return Collections.unmodifiableSet(mEnabledLetters);
	}
	
	// support on-the-fly exploration
	@Override
	public IntSet getSuccessors(int letter) {
		if(mEnabledLetters.contains(letter)) {
			return super.getSuccessors(letter);
		}else {
			mEnabledLetters.add(letter);
			IntSet succs = mBuchi.computeSuccessors(getId(), letter);
			IntIterator iter = succs.iterator();
			while(iter.hasNext()) {
				super.addSuccessor(letter, iter.next());
			}
			return succs;
		}
	}
	
	

}
