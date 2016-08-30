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
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;


/**
 * A PetriNetRun is a sequence of Markings m0 ... m_{n+1} and a word w_0 .. w_n
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <S> Type of alphabet symbols.
 * @param <C> Type of labels for Places
 */
public class PetriNetRun<S,C> implements IRun<S,C> {
	
	private final Word<S> mWord;
	private final ArrayList<Marking<S,C>> mMarkingSequence;
	
	/**
	 * Construct PetriNet run of length 0.
	 */
	public PetriNetRun(final Marking<S,C> m0) {
		mWord = new NestedWord<S>();
		mMarkingSequence = new ArrayList<Marking<S,C>>();
		mMarkingSequence.add(m0);
	}

	/**
	 * Construct PetriNet run of length 1.
	 */
	public PetriNetRun(final Marking<S,C> m0, final S symbol, final Marking<S,C> m1) {
		mWord = new NestedWord<S>(symbol, NestedWord.INTERNAL_POSITION);
		mMarkingSequence = new ArrayList<Marking<S,C>>();
		mMarkingSequence.add(m0);
		mMarkingSequence.add(m1);
	}
	
	/**
	 * Construct PetriNet run of arbitrary length 1
	 */
	public PetriNetRun(final ArrayList<Marking<S,C>> sequenceOfMarkings, 
					   final Word<S> word) {
		if (sequenceOfMarkings.size() - 1 != word.length()) {
			throw new IllegalArgumentException(
									"run consists of word length +1 markings");
		}
		mMarkingSequence = sequenceOfMarkings;
		mWord = word;
	}

	@Override
	public S getSymbol(final int i) {
		return mWord.getSymbol(i);
	}
	
	@Override
	public Word<S> getWord() {
		return mWord;
	}
	
	public Marking<S,C> getMarking(final int i) {
		return mMarkingSequence.get(i);
	}
	
// use this method only if needed
//	public ArrayList<Marking<S,C>> getMarkingSequence() {
//		return mMarkingSequence;
//	}
	
	/**
	 * Returns a new run which is the concatenation of this and run2.
	 * This is not changed.
	 */
	public PetriNetRun<S,C> concatenate(final PetriNetRun<S,C> run2) {
		final Word<S> concatWord = mWord.concatenate(run2.getWord());
		final ArrayList<Marking<S, C>> concatMarkingSequence = 
												new ArrayList<Marking<S,C>>();
		for (int i = 0; i < mMarkingSequence.size(); i++) {
			concatMarkingSequence.add(this.getMarking(i));
		}
		if (!getMarking(mMarkingSequence.size() - 1).equals(run2.getMarking(0))) {
			throw new IllegalArgumentException("can only concatenate runs "
					+ "where last Marking of first run and first Marking of"
					+ "second run coincide"); 
		}
		for (int i = 1; i < run2.mMarkingSequence.size(); i++) {
			concatMarkingSequence.add(run2.getMarking(i));
		}
		return new PetriNetRun<S, C>(concatMarkingSequence, concatWord);
	}

	@Override
	public int getLength() {
		return mMarkingSequence.size();
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (int i = 0; i < mWord.length(); i++) {
			sb.append(mMarkingSequence.get(i) + " ");
			sb.append(mWord.getSymbol(i) + " ");
		}
		sb.append(mMarkingSequence.get(mMarkingSequence.size() - 1));
		return sb.toString();
	}

}
