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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.IRun;

/**
 * A run over a nested word.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @see NestedWord
 */
public class NestedRun<LETTER, STATE> implements IRun<LETTER, STATE, STATE> {
	private static final char BLANK = ' ';
	
	private NestedWord<LETTER> mNestedWord;
	private ArrayList<STATE> mStateSequence;
	
	/**
	 * Constructor with a nested word and a sequence of states.
	 * 
	 * @param nestedWord
	 *            nested word
	 * @param stateSequence
	 *            sequence of states
	 */
	public NestedRun(final NestedWord<LETTER> nestedWord, final ArrayList<STATE> stateSequence) {
		if (nestedWord.length() + 1 == stateSequence.size()) {
			mNestedWord = nestedWord;
			mStateSequence = stateSequence;
		} else {
			throw new IllegalArgumentException(
					"In a run the length of the sequence of states is the length of the word plus 1.");
		}
	}
	
	/**
	 * Constructor for a run of length 1.
	 * 
	 * @param state
	 *            the only state
	 */
	public NestedRun(final STATE state) {
		@SuppressWarnings("unchecked")
		final LETTER[] word = (LETTER[]) new Object[] {};
		final int[] nestingRelation = {};
		mNestedWord = new NestedWord<>(word, nestingRelation);
		
		mStateSequence = new ArrayList<>(1);
		mStateSequence.add(state);
	}
	
	/**
	 * Constructor for a run of length 2.
	 * 
	 * @param state0
	 *            first state
	 * @param symbol
	 *            symbol
	 * @param position
	 *            position in the nested word
	 * @param state1
	 *            second state
	 */
	public NestedRun(final STATE state0, final LETTER symbol, final int position, final STATE state1) {
		if (position != NestedWord.INTERNAL_POSITION && position != NestedWord.MINUS_INFINITY
				&& position != NestedWord.PLUS_INFINITY) {
			throw new IllegalArgumentException("Wrong position in the nested word.");
		}
		@SuppressWarnings("unchecked")
		final LETTER[] word = (LETTER[]) new Object[] { symbol };
		final int[] nestingRelation = { position };
		mNestedWord = new NestedWord<>(word, nestingRelation);
		
		mStateSequence = new ArrayList<>(2);
		mStateSequence.add(state0);
		mStateSequence.add(state1);
	}
	
	@Override
	public NestedWord<LETTER> getWord() {
		return mNestedWord;
	}
	
	public ArrayList<STATE> getStateSequence() {
		return mStateSequence;
	}
	
	/**
	 * @return Length of this run's state sequence.
	 */
	@Override
	public int getLength() {
		return mStateSequence.size();
	}
	
	/**
	 * @param position
	 *            The position.
	 * @return true iff the position is a call position
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord#isCallPosition(int)
	 *      NestedWord.isCallPosition(int)
	 */
	public boolean isCallPosition(final int position) {
		return mNestedWord.isCallPosition(position);
	}
	
	/**
	 * @param position
	 *            The position.
	 * @return true iff the position is an internal position
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord#isInternalPosition(int)
	 *      NestedWord.isInternalPosition(int)
	 */
	public boolean isInternalPosition(final int position) {
		return mNestedWord.isInternalPosition(position);
	}
	
	/**
	 * @param position
	 *            The position.
	 * @return true iff the position is a return position
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord#isReturnPosition(int)
	 *      NestedWord.isReturnPosition(int)
	 */
	public boolean isReturnPosition(final int position) {
		return mNestedWord.isReturnPosition(position);
	}
	
	/**
	 * @param position
	 *            The position.
	 * @return true iff the position is a pending return
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord#isPendingCall(int)
	 *      NestedWord.isPendingCall(int)
	 */
	public boolean isPendingCall(final int position) {
		return mNestedWord.isPendingCall(position);
	}
	
	/**
	 * Concatenate another nested run.
	 * 
	 * @param run
	 *            another nested run
	 * @return new nested run being the concatenation
	 */
	public NestedRun<LETTER, STATE> concatenate(final NestedRun<LETTER, STATE> run) {
		final STATE lastStateOfThis = mStateSequence.get(mStateSequence.size() - 1);
		final STATE firstStateOfRun = run.mStateSequence.get(0);
		
		if (lastStateOfThis.equals(firstStateOfRun)) {
			final NestedWord<LETTER> concatNestedWord = mNestedWord.concatenate(run.getWord());
			final ArrayList<STATE> concatStateSeq = new ArrayList<>(mStateSequence);
			for (int i = 1; i < run.getStateSequence().size(); i++) {
				concatStateSeq.add(run.getStateSequence().get(i));
			}
			return new NestedRun<>(concatNestedWord, concatStateSeq);
		}
		throw new IllegalArgumentException("Can only concatenate two runs"
				+ " where the last element of the first runs statement"
				+ " sequence is the same state as the last element of the" + " second runs statement sequence.");
	}
	
	/**
	 * @param position
	 *            Position.
	 * @return the state at the given position in the run
	 */
	public STATE getStateAtPosition(final int position) {
		return mStateSequence.get(position);
	}
	
	@Override
	public LETTER getSymbol(final int position) {
		return mNestedWord.getSymbolAt(position);
	}
	
	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		// @formatter:off
		for (int i = 0; i < mNestedWord.length(); i++) {
			builder.append(getStateAtPosition(i))
					.append(BLANK);
			if (mNestedWord.isInternalPosition(i)) {
				builder.append(mNestedWord.getSymbolAt(i))
						.append(BLANK);
			} else if (mNestedWord.isCallPosition(i)) {
				builder.append(mNestedWord.getSymbolAt(i))
						.append("< ");
			} else if (mNestedWord.isReturnPosition(i)) {
				builder.append('>')
						.append(mNestedWord.getSymbolAt(i))
						.append(BLANK);
			}
		}
		builder.append(getStateAtPosition(mStateSequence.size() - 1))
				.append(BLANK);
		// @formatter:on
		return builder.toString();
	}
}
