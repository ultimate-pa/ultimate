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

import java.io.PrintStream;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;



/**
 * State class for Buchi Nested Word Automata
 * */
public class StateNwa implements IStateNwa, Comparable<StateNwa> {
	
	private final IBuchiNwa mBuchi;
	private final int mId;
	
	private final Map<Integer, IntSet> mSuccessorsInternal;
	private final Map<Integer, IntSet> mSuccessorsCall;
	// letter * hier -> succ
	private final Map<Integer, Map<Integer, IntSet>> mSuccessorsReturn; 
	
	public StateNwa(IBuchiNwa buchi, int id) {
		this.mBuchi = buchi;
		this.mId = id;
		this.mSuccessorsCall = new HashMap<>();
		this.mSuccessorsInternal = new HashMap<>();
		this.mSuccessorsReturn = new HashMap<>();
	}

	@Override
	public int getId() {
		return mId;
	}
	
	private void addSuccessors(Map<Integer, IntSet> succMap, int letterOrHier, int state) {
		IntSet succs = succMap.get(letterOrHier);
		if(succs == null) {
			succs =  UtilIntSet.newIntSet();
		}
		succs.set(state);
		succMap.put(letterOrHier, succs);	
	}

	@Override
	public void addSuccessorInternal(int letter, int state) {
		assert mBuchi.getAlphabetInternal().get(letter);
		addSuccessors(mSuccessorsInternal, letter, state);
	}

	@Override
	public void addSuccessorCall(int letter, int state) {
		assert mBuchi.getAlphabetCall().get(letter);
		addSuccessors(mSuccessorsCall, letter, state);		
	}

	@Override
	public void addSuccessorReturn(int hier, int letter, int state) {
		assert mBuchi.getAlphabetReturn().get(letter);
		Map<Integer, IntSet> succMap = mSuccessorsReturn.get(letter);
		if(succMap == null) {
			succMap = new HashMap<>();
		}
		addSuccessors(succMap, hier, state);
		mSuccessorsReturn.put(letter, succMap);
	}

	private IntSet getSuccessors(Map<Integer, IntSet> succMap, int letter) {
		IntSet succs = succMap.get(letter);
		if(succs == null) { // transition function may not be complete
			return UtilIntSet.newIntSet();
		}
		return succs.clone();
	}
	
	@Override
	public IntSet getSuccessorsInternal(int letter) {
		assert mBuchi.getAlphabetInternal().get(letter);
		return getSuccessors(mSuccessorsInternal, letter);
	}

	@Override
	public IntSet getSuccessorsCall(int letter) {
		assert mBuchi.getAlphabetCall().get(letter);
		return getSuccessors(mSuccessorsCall, letter);
	}

	@Override
	public IntSet getSuccessorsReturn(int hier, int letter) {
		assert mBuchi.getAlphabetReturn().get(letter);
		Map<Integer, IntSet> succMap = mSuccessorsReturn.get(letter);
		if(succMap == null) {
			return UtilIntSet.newIntSet();
		}
		return getSuccessors(succMap, hier);
	}

	@Override
	public Set<Integer> getEnabledLettersInternal() {
		return mSuccessorsInternal.keySet();
	}

	@Override
	public Set<Integer> getEnabledLettersCall() {
		return mSuccessorsCall.keySet();
	}

	@Override
	public Set<Integer> getEnabledLettersReturn() {
		return mSuccessorsReturn.keySet();
	}

	@Override
	public Set<Integer> getEnabledHiersReturn(int letter) {
		Map<Integer, IntSet> succMap = mSuccessorsReturn.get(letter);
		if(succMap ==null) {
			return Collections.emptySet();
		}
		return succMap.keySet();
	}
	
	@Override
	public int compareTo(StateNwa other) {
		return mId - other.mId;
	}
	
	@Override
	public boolean equals(Object other) {
		if(this == other) return true;
		if(!(other instanceof StateNwa)) {
			return false;
		}
		
		StateNwa otherState = (StateNwa)other;
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
	

	@Override
	public void toDot(PrintStream printer, List<String> alphabet) {
		Set<Integer> callLetters = this.getEnabledLettersCall();
		for(Integer letter : callLetters) {
        	IntSet succs = this.getSuccessorsCall(letter);
    		transToDot(printer, alphabet, succs, alphabet.get(letter) + "<");
        }
		
		Set<Integer> internalLetters = this.getEnabledLettersInternal();
		for(Integer letter : internalLetters) {
        	IntSet succs = this.getSuccessorsInternal(letter);
    		transToDot(printer, alphabet, succs, alphabet.get(letter).toString());
        }
		
		Set<Integer> returnLetters = this.getEnabledLettersReturn();
		for(Integer letter : returnLetters) {
			Set<Integer> predHiers = this.getEnabledHiersReturn(letter);
			for(Integer predHier : predHiers) {
	        	IntSet succs = this.getSuccessorsReturn(predHier, letter);
	    		transToDot(printer, alphabet, succs, predHier + ",>" + alphabet.get(letter));
			}
        }
	}
	
	private void transToDot(PrintStream printer, List<String> alphabet, IntSet succs, String letter) {
		for(final Integer succ : succs.iterable()) {
			printer.print("  " + this.getId() + " -> " + succ + " [label=\"" + letter.replaceAll("\"", "") + "\"];\n");
		}
	}

}
