package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.text.MessageFormat;


/**
 * Internal Transition of a successor state.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class IncomingInternalTransition<LETTER,STATE> implements Transitionlet<LETTER,STATE> {
	
	private final LETTER m_Letter; 
	private final STATE m_Pred;
	
	public IncomingInternalTransition(STATE pred, LETTER letter) {
		m_Pred = pred;
		m_Letter = letter;
	}
	
	public LETTER getLetter() {
		return m_Letter;
	}
	
	public STATE getPred() {
		return m_Pred;
	}
	
	
	public String toString() {
		return MessageFormat.format("( {0} , {1} , _ )",getPred(), getLetter());
	}
}
