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
package de.uni_freiburg.informatik.ultimate.automata;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;


public class Word<LETTER> implements Iterable<LETTER> {

	protected LETTER[] mWord;
	
	/**
	 * Construct Word consisting of a sequence of symbols
	 * 
	 * @param symbols sequence of symbols
	 */
	@SafeVarargs
	public Word(final LETTER... symbols) {
		this.mWord = symbols;
	}
	
	/**
	 * @return The length of the Word is 0 for the empty word, 1 for the
	 * word that consists of one symbol, etc.
	 */
	public int length() {
		return mWord.length;
	}
	
	/**
	 * @return list of symbols
	 */
	public List<LETTER> asList() {
		return Arrays.asList(mWord);
	}
	
	/**
	 * @param position position in word
	 * @return Symbol at position.
	 */
	public LETTER getSymbol(final int position) {
		if (position < 0 || position >= mWord.length) {
			throw new IllegalArgumentException("index out of range");
		}
		return mWord[position];
	}
	
	/**
	 * @param word2 other word
	 * @return concatenation 'this.word2'
	 */
	@SuppressWarnings("unchecked")
	public Word<LETTER> concatenate(final Word<LETTER> word2) {
		final int lengthWord1 = this.length();
		final int lengthWord2 = word2.length();
		final LETTER[] concatenationSymbols = 
			(LETTER[]) new Object[lengthWord1 + lengthWord2];
		
		for (int i=0; i<lengthWord1; i++) {
			concatenationSymbols[i] = this.getSymbol(i);
		}
		for (int i=0; i<lengthWord2; i++) {
			concatenationSymbols[lengthWord1+i] = word2.getSymbol(i);
		}
		return new Word<LETTER>(concatenationSymbols);
	}		
	
	@Override
	public String toString() {
		//return mWord.toString();
		final StringBuilder sb = new StringBuilder();
		sb.append('[');
		for (int i = 0; i < mWord.length; i++) {
			sb.append(mWord[i]);
		}
		sb.append(']');
		return sb.toString();
	}
	
	@Override
	public Iterator<LETTER> iterator() {
		return Arrays.asList(mWord).iterator();
	}
}
