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
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;


/**
 * A PetriNetRun is a sequence of Markings m_0 ... m_{n+1} and a word w_0 .. w_n
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Type of alphabet symbols.
 * @param <C> Type of labels for Places
 */
public class PetriNetRun<S,C> implements IRun<S,C> {
	
	private Word<S> m_Word;
	private ArrayList<Marking<S,C>> m_MarkingSequence;
	
	/**
	 * Construct PetriNet run of length 0
	 */
	public PetriNetRun(Marking<S,C> m0) {
		m_Word = new NestedWord<S>();
		m_MarkingSequence = new ArrayList<Marking<S,C>>();
		m_MarkingSequence.add(m0);
	}

	/**
	 * Construct PetriNet run of length 1
	 */
	public PetriNetRun(Marking<S,C> m0, S symbol, Marking<S,C> m1) {
		m_Word = new NestedWord<S>(symbol, NestedWord.INTERNAL_POSITION);
		m_MarkingSequence = new ArrayList<Marking<S,C>>();
		m_MarkingSequence.add(m0);
		m_MarkingSequence.add(m1);
	}
	
	/**
	 * Construct PetriNet run of arbitrary length 1
	 */
	public PetriNetRun(ArrayList<Marking<S,C>> sequenceOfMarkings, 
					   Word<S> word) {
		if (sequenceOfMarkings.size() -1 != word.length()) {
			throw new IllegalArgumentException(
									"run consists of word length +1 markings");
		}
		m_MarkingSequence = sequenceOfMarkings;
		m_Word = word;
	}

	public S getSymbol(int i) {
		return m_Word.getSymbol(i);
	}
	
	public Word<S> getWord() {
		return m_Word;
	}
	
	public Marking<S,C> getMarking(int i) {
		return m_MarkingSequence.get(i);
	}
	
// use this method only if needed
//	public ArrayList<Marking<S,C>> getMarkingSequence() {
//		return m_MarkingSequence;
//	}
	
	/**
	 * Returns a new run which is the concatenation of this and run2.
	 * This is not changed.
	 */
	public PetriNetRun<S,C> concatenate(PetriNetRun<S,C> run2) {
		Word<S> concatWord = m_Word.concatenate(run2.getWord());
		ArrayList<Marking<S, C>> concatMarkingSequence = 
												new ArrayList<Marking<S,C>>();
		for (int i=0; i<this.m_MarkingSequence.size(); i++){
			concatMarkingSequence.add(this.getMarking(i));
		}
		if (!getMarking(m_MarkingSequence.size()-1).equals(run2.getMarking(0))) {
			throw new IllegalArgumentException("can only concatenate runs " +
					"where last Marking of first run and first Marking of" +
					"second run coincide"); 
		}
		for (int i=1; i<run2.m_MarkingSequence.size(); i++){
			concatMarkingSequence.add(run2.getMarking(i));
		}
		return new PetriNetRun<S, C>(concatMarkingSequence, concatWord);
	}

	@Override
	public int getLength() {
		return m_MarkingSequence.size();
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i<m_Word.length(); i++) {
			sb.append(m_MarkingSequence.get(i) + " ");
			sb.append(m_Word.getSymbol(i)+" ");
		}
		sb.append(m_MarkingSequence.get(m_MarkingSequence.size()-1));
		return sb.toString();
	}

}
