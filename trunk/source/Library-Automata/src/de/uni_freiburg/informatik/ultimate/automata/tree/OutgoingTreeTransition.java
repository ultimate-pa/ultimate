package de.uni_freiburg.informatik.ultimate.automata.tree;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingTransitionlet;
import java.text.MessageFormat;

/**
 * Class for Transition form one state of the automaton to another.
 * @author grugelt@uni-freiburg.de
 *
 * @param <LETTER> Letter for the transition.
 * @param <STATE> States for the transition.
 */
public class OutgoingTreeTransition<LETTER, STATE> implements OutgoingTransitionlet<LETTER, STATE> {
	
		private final LETTER m_Letter; 
		private final STATE m_Succ;
		
		public OutgoingTreeTransition(LETTER letter, STATE succ) {
			m_Letter = letter;
			m_Succ = succ;
		}
		
		public LETTER getLetter() {
			return m_Letter;
		}
		
		public STATE getSucc() {
			return m_Succ;
		}
		
		public String toString() {
			return MessageFormat.format("( _ , {0} , {1} )", getLetter(), getSucc());
		}
		
}
