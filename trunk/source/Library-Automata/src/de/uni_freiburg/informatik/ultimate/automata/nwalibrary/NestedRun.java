/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
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
	
	private NestedWord<LETTER> m_NestedWord;
	private ArrayList<STATE> m_StateSequence;
	
	public NestedRun(NestedWord<LETTER> nw,
					ArrayList<STATE> stateSequence) {
		if (nw.length()+1 == stateSequence.size()) {
			this.m_NestedWord = nw;
			this.m_StateSequence = stateSequence;
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
		m_StateSequence = new ArrayList<STATE>(1);
		m_StateSequence.add(state);
		@SuppressWarnings("unchecked")
		LETTER[] word =  (LETTER[])new Object[] { };
		int[] nestingRelation = {};
		m_NestedWord = new NestedWord<LETTER>(word, nestingRelation);
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
		m_NestedWord = new NestedWord<LETTER>(word,nestingRelation);
		m_StateSequence = new ArrayList<STATE>(2);
		m_StateSequence.add(q0);
		m_StateSequence.add(q1);
	}
	
		
	
	public NestedWord<LETTER> getWord() {
		return this.m_NestedWord;
	}
	
	
	public ArrayList<STATE> getStateSequence() {
		return this.m_StateSequence;
	}
	
	
	/**
	 * Length of this runs state sequence.
	 */	
	public int getLength() {
		return this.m_StateSequence.size();
	}
		
	/**
	 * @param i
	 * @return
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord#isCallPosition(int)
	 */
	public boolean isCallPosition(int i) {
		return m_NestedWord.isCallPosition(i);
	}

	

	/**
	 * @param i
	 * @return
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord#isInternalPosition(int)
	 */
	public boolean isInternalPosition(int i) {
		return m_NestedWord.isInternalPosition(i);
	}

	/**
	 * @param i
	 * @return
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord#isReturnPosition(int)
	 */
	public boolean isReturnPosition(int i) {
		return m_NestedWord.isReturnPosition(i);
	}

	/**
	 * @param i
	 * @return
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord#isPendingCall(int)
	 */
	public boolean isPendingCall(int i) {
		return m_NestedWord.isPendingCall(i);
	}

	public NestedRun<LETTER,STATE> concatenate(NestedRun<LETTER,STATE> run) {
		STATE lastStateOfThis = m_StateSequence.get(m_StateSequence.size()-1);
		STATE firstStateOfRun = run.m_StateSequence.get(0);
		
		if (lastStateOfThis.equals(firstStateOfRun)) {
	
		NestedWord<LETTER> concatNestedWord =
			m_NestedWord.concatenate(run.getWord());
			ArrayList<STATE> concatStateSeq =
					new ArrayList<STATE>(m_StateSequence);
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
		return m_StateSequence.get(i);
	}
	
	public LETTER getSymbol(int i) {
		return m_NestedWord.getSymbolAt(i);
	}
	

	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i<m_NestedWord.length(); i++) {
			sb.append(getStateAtPosition(i) + " ");
			if (m_NestedWord.isInternalPosition(i)) {
				sb.append(m_NestedWord.getSymbolAt(i)+" ");
			}
			else if (m_NestedWord.isCallPosition(i)) {
				sb.append(m_NestedWord.getSymbolAt(i)+"< ");
			}
			else if (m_NestedWord.isReturnPosition(i)) {
				sb.append(">" + m_NestedWord.getSymbolAt(i) + " ");
			}
		}
		sb.append(getStateAtPosition(m_StateSequence.size()-1) + " ");
		return sb.toString();
	}
	
}
