package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.text.MessageFormat;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingTransitionlet;

/**
 * Class for Transition form one state of the automaton to another.
 * @author grugelt@uni-freiburg.de
 *
 * @param <LETTER> Letter for the transition.
 * @param <STATE> States for the transition.
 */
public class OutgoingTreeTransition<LETTER, STATE> implements OutgoingTransitionlet<LETTER, STATE> {
	
		private final LETTER mLetter; 
		private final STATE mSucc;
		
		public OutgoingTreeTransition(LETTER letter, STATE succ) {
			mLetter = letter;
			mSucc = succ;
		}
		
		@Override
		public LETTER getLetter() {
			return mLetter;
		}
		
		@Override
		public STATE getSucc() {
			return mSucc;
		}
		
		@Override
		public String toString() {
			return MessageFormat.format("( _ , {0} , {1} )", getLetter(), getSucc());
		}
		
}
