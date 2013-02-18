package de.uni_freiburg.informatik.ultimate.automata;


	public class Word<Symbol> {

		protected Symbol[] m_Word;
		
	
		/**
		 * Construct Word consisting of a sequence of symbols
		 */
		public Word(Symbol ... symbols) {
			this.m_Word = symbols;
		}
		
		
		/**
		 * @return The length of the Word is 0 for the empty word, 1 for the
		 * word that consists of one symbol, etc.
		 */
		public int length() {
			return m_Word.length;
		}
		
		
		/**
		 * 
		 * @param position
		 * @return Symbol at position;
		 */
		public Symbol getSymbol(int position) 
		{
			if (position < 0 || position >= m_Word.length) {
				throw new IllegalArgumentException("index out of range");
			}
			return m_Word[position];
		}
		
		
		@SuppressWarnings("unchecked")
		public Word<Symbol> concatenate(Word<Symbol> nestedWord2) {
			int lengthWord1 = this.length();
			int lengthWord2 = nestedWord2.length();
			Symbol[] concatenationSymbols = 
				(Symbol[]) new Object[lengthWord1 + lengthWord2];
			
			for (int i=0; i<lengthWord1; i++) {
				concatenationSymbols[i] = this.getSymbol(i);
			}
			for (int i=0; i<lengthWord2; i++) {
				concatenationSymbols[lengthWord1+i] = nestedWord2.getSymbol(i);
			}
			return new Word<Symbol>(concatenationSymbols);
		}		

		@Override
		public String toString() {
			//return m_Word.toString();
			String s = "[";
			for (int i = 0; i < m_Word.length; i++) {
				s += m_Word[i];
			}
			s += "]";
			return s;
		}
	}