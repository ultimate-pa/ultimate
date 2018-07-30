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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;

/**
 * A Petri net run is a sequence of markings <tt>m0 ... m_{n+1}</tt> and a word <tt>w_0 ... w_n</tt>.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbols type
 * @param <PLACE>
 *            place content type
 */
public class PetriNetRun<LETTER, PLACE> implements IRun<LETTER, PLACE, Marking<LETTER, PLACE>> {

	private final Word<LETTER> mWord;
	private final ArrayList<Marking<LETTER, PLACE>> mMarkingSequence;

	/**
	 * Construct Petri net run of length 0.
	 *
	 * @param m0
	 *            initial marking
	 */
	public PetriNetRun(final Marking<LETTER, PLACE> m0) {
		mWord = new NestedWord<>();
		mMarkingSequence = new ArrayList<>();
		mMarkingSequence.add(m0);
	}

	/**
	 * Constructs Petri net run of length 1.
	 *
	 * @param m0
	 *            initial marking
	 * @param symbol
	 *            first symbol
	 * @param m1
	 *            next marking
	 */
	public PetriNetRun(final Marking<LETTER, PLACE> m0, final LETTER symbol, final Marking<LETTER, PLACE> m1) {
		mWord = new NestedWord<>(symbol, NestedWord.INTERNAL_POSITION);
		mMarkingSequence = new ArrayList<>();
		mMarkingSequence.add(m0);
		mMarkingSequence.add(m1);
	}

	/**
	 * Constructs Petri net run of arbitrary length.
	 *
	 * @param sequenceOfMarkings
	 *            sequence of markings
	 * @param word
	 *            corresponding word
	 */
	public PetriNetRun(final ArrayList<Marking<LETTER, PLACE>> sequenceOfMarkings, final Word<LETTER> word) {
		if (sequenceOfMarkings.size() - 1 != word.length()) {
			throw new IllegalArgumentException("run consists of word length +1 markings");
		}
		mMarkingSequence = sequenceOfMarkings;
		mWord = word;
	}

	@Override
	public LETTER getSymbol(final int pos) {
		return mWord.getSymbol(pos);
	}

	@Override
	public Word<LETTER> getWord() {
		return mWord;
	}

	/**
	 * @param pos
	 *            Position.
	 * @return marking at the given position
	 */
	public Marking<LETTER, PLACE> getMarking(final int pos) {
		return mMarkingSequence.get(pos);
	}

	/*
	// use this method only if needed
	public ArrayList<Marking<S,C>> getMarkingSequence() {
		return mMarkingSequence;
	}
	*/

	/**
	 * @param run2
	 *            Another run.
	 * @return A new run which is the concatenation of this and run2. This is not changed.
	 */
	public PetriNetRun<LETTER, PLACE> concatenate(final PetriNetRun<LETTER, PLACE> run2) {
		final ArrayList<Marking<LETTER, PLACE>> concatMarkingSequence = new ArrayList<>();
		for (int i = 0; i < mMarkingSequence.size(); i++) {
			concatMarkingSequence.add(this.getMarking(i));
		}
		if (!getMarking(mMarkingSequence.size() - 1).equals(run2.getMarking(0))) {
			throw new IllegalArgumentException("can only concatenate runs where last Marking of first run and first "
					+ "Marking of second run coincide");
		}
		for (int i = 1; i < run2.mMarkingSequence.size(); i++) {
			concatMarkingSequence.add(run2.getMarking(i));
		}
		final Word<LETTER> concatWord = mWord.concatenate(run2.getWord());
		return new PetriNetRun<>(concatMarkingSequence, concatWord);
	}

	@Override
	public int getLength() {
		return mMarkingSequence.size();
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (int i = 0; i < mWord.length(); i++) {
			sb.append(mMarkingSequence.get(i)).append(' ');
			sb.append(mWord.getSymbol(i)).append(' ');
		}
		sb.append(mMarkingSequence.get(mMarkingSequence.size() - 1));
		return sb.toString();
	}

	@Override
	public List<Marking<LETTER, PLACE>> getStateSequence() {
		return mMarkingSequence;
	}
}
