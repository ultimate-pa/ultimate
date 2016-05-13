package de.uni_freiburg.informatik.ultimate.automata.tree.operators;

import de.uni_muenster.cs.sev.lethal.states.State;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;

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
	}
	
}
