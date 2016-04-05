package de.uni_freiburg.informatik.ultimate.automata.tree.operators;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;

/**
 * An abstract class that contains type conversion from Ultimate's states
 * to Lethal's state.
 * 
 * 
 * @param <LETTER> is the type of the alphabet.
 * @param <STATE> is the type of the states.
 * 
 * @author Mostafa M.A.
 */
public abstract class Converter {

	class MySymbol<LETTER> implements RankedSymbol {
		MySymbol(LETTER letter, int arity) {
			this.letter = letter;
			this.arity = arity;
		}
		@Override
		public int getArity() {
			return arity;
		}
		public LETTER getLetter() {
			return letter;
		}
		public String toString() {
			return arity + letter.toString();
		}
		@Override
		public boolean equals(Object other) {
			if ((LETTER) other != letter)
				return ((LETTER) other).equals(letter);
			else
				return true;
		}
		private LETTER letter;
		private int arity;
	}
	
	class MyState<STATE> implements State {
		MyState(STATE state) {
			this.state = state;
		}
		public STATE getState() {
			return state;
		}
		private STATE state;
		
		public String toString() {
			return state.toString();
		}
		@Override
		public boolean equals(Object other) {
			if (((STATE) other) != state)
				return ((STATE) other).equals(state);
			else
				return true;
		}
	}
	
}
