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


	public class Word<Symbol> implements Iterable<Symbol> {

		protected Symbol[] mWord;
		
	
		/**
		 * Construct Word consisting of a sequence of symbols
		 */
		@SafeVarargs
		public Word(Symbol... symbols) {
			this.mWord = symbols;
		}
		
		
		/**
		 * @return The length of the Word is 0 for the empty word, 1 for the
		 * word that consists of one symbol, etc.
		 */
		public int length() {
			return mWord.length;
		}
		
		public List<Symbol> asList() {
			return Arrays.asList(mWord);
		}
		
		
		/**
		 * 
		 * @param position
		 * @return Symbol at position;
		 */
		public Symbol getSymbol(int position) 
		{
			if (position < 0 || position >= mWord.length) {
				throw new IllegalArgumentException("index out of range");
			}
			return mWord[position];
		}
		
		
		@SuppressWarnings("unchecked")
		public Word<Symbol> concatenate(Word<Symbol> nestedWord2) {
			final int lengthWord1 = this.length();
			final int lengthWord2 = nestedWord2.length();
			final Symbol[] concatenationSymbols = 
				(Symbol[]) new Object[lengthWord1 + lengthWord2];
			
			for (int i=0; i<lengthWord1; i++) {
				concatenationSymbols[i] = this.getSymbol(i);
			}
			for (int i=0; i<lengthWord2; i++) {
				concatenationSymbols[lengthWord1+i] = nestedWord2.getSymbol(i);
			}
			return new Word<Symbol>(concatenationSymbols);
		}		
		
		
		public List<Symbol> lettersAsList() {
			return Arrays.asList(mWord);
		}
		

		@Override
		public String toString() {
			//return mWord.toString();
			String s = "[";
			for (int i = 0; i < mWord.length; i++) {
				s += mWord[i];
			}
			s += "]";
			return s;
		}


		@Override
		public Iterator<Symbol> iterator() {
			return Arrays.asList(mWord).iterator();
		}
	}
