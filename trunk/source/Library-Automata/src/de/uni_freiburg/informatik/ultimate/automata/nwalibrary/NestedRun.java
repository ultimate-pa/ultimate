/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.IRun;

public class NestedRun<LETTER,STATE> implements IRun<LETTER,STATE> {
	
	private NestedWord<LETTER> mNestedWord;
	private ArrayList<STATE> mStateSequence;
	
	public NestedRun(NestedWord<LETTER> nw,
					ArrayList<STATE> stateSequence) {
		if (nw.length()+1 == stateSequence.size()) {
			this.mNestedWord = nw;
			this.mStateSequence = stateSequence;
		}
		else {
			throw new IllegalArgumentException("In a run the length of the" +
					" sequence of states is length of the word plus 1.");
		}
	}
	
	/**
	 * Constructor for a run of length 1. 
	 */

	public NestedRun(STATE state) {
		mStateSequence = new ArrayList<STATE>(1);
		mStateSequence.add(state);
		@SuppressWarnings("unchecked")
		LETTER[] word =  (LETTER[])new Object[] { };
		int[] nestingRelation = {};
		mNestedWord = new NestedWord<LETTER>(word, nestingRelation);
	}

	/**
	 * Constructor for a run of length 2. 
	 */
	public NestedRun(STATE q0,
			 		  LETTER symbol,
			 		  int position,
			 		  STATE q1) {
		if (position != NestedWord.INTERNAL_POSITION
			&& position != NestedWord.MINUS_INFINITY
			&& position != NestedWord.PLUS_INFINITY) {
			throw new IllegalArgumentException();
		}
		@SuppressWarnings("unchecked")
		LETTER[] word = (LETTER[])new Object[] {symbol};
		int[] nestingRelation = { position };
		mNestedWord = new NestedWord<LETTER>(word,nestingRelation);
		mStateSequence = new ArrayList<STATE>(2);
		mStateSequence.add(q0);
		mStateSequence.add(q1);
	}
	
		
	
	public NestedWord<LETTER> getWord() {
		return this.mNestedWord;
	}
	
	
	public ArrayList<STATE> getStateSequence() {
		return this.mStateSequence;
	}
	
	
	/**
	 * Length of this runs state sequence.
	 */	
	public int getLength() {
		return this.mStateSequence.size();
	}
		
	/**
	 * @param i
	 * @return
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord#isCallPosition(int)
	 */
	public boolean isCallPosition(int i) {
		return mNestedWord.isCallPosition(i);
	}

	

	/**
	 * @param i
	 * @return
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord#isInternalPosition(int)
	 */
	public boolean isInternalPosition(int i) {
		return mNestedWord.isInternalPosition(i);
	}

	/**
	 * @param i
	 * @return
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord#isReturnPosition(int)
	 */
	public boolean isReturnPosition(int i) {
		return mNestedWord.isReturnPosition(i);
	}

	/**
	 * @param i
	 * @return
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord#isPendingCall(int)
	 */
	public boolean isPendingCall(int i) {
		return mNestedWord.isPendingCall(i);
	}

	public NestedRun<LETTER,STATE> concatenate(NestedRun<LETTER,STATE> run) {
		STATE lastStateOfThis = mStateSequence.get(mStateSequence.size()-1);
		STATE firstStateOfRun = run.mStateSequence.get(0);
		
		if (lastStateOfThis.equals(firstStateOfRun)) {
	
		NestedWord<LETTER> concatNestedWord =
			mNestedWord.concatenate(run.getWord());
			ArrayList<STATE> concatStateSeq =
					new ArrayList<STATE>(mStateSequence);
			for (int i=1; i<run.getStateSequence().size(); i++) {
				concatStateSeq.add(run.getStateSequence().get(i));
			}
			return new NestedRun<LETTER, STATE>(concatNestedWord,concatStateSeq);
		}
		else {
			throw new IllegalArgumentException("Can only concatenate two runs" +
					" where the last element of the first runs statement" +
					" sequence is the same state as the last element of the" +
					" second runs statement sequence."); 
		}
	}
		

	
	public STATE getStateAtPosition(int i) {
		return mStateSequence.get(i);
	}
	
	public LETTER getSymbol(int i) {
		return mNestedWord.getSymbolAt(i);
	}
	

	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i<mNestedWord.length(); i++) {
			sb.append(getStateAtPosition(i) + " ");
			if (mNestedWord.isInternalPosition(i)) {
				sb.append(mNestedWord.getSymbolAt(i)+" ");
			}
			else if (mNestedWord.isCallPosition(i)) {
				sb.append(mNestedWord.getSymbolAt(i)+"< ");
			}
			else if (mNestedWord.isReturnPosition(i)) {
				sb.append(">" + mNestedWord.getSymbolAt(i) + " ");
			}
		}
		sb.append(getStateAtPosition(mStateSequence.size()-1) + " ");
		return sb.toString();
	}
	
}
