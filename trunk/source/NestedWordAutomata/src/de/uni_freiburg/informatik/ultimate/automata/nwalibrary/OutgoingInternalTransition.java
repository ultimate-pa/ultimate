package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.text.MessageFormat;


/**
 * Outgoing internal transition of a state.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class OutgoingInternalTransition<LETTER,STATE> {
	
	private final LETTER m_Letter; 
	private final STATE m_Succ;
	
	public OutgoingInternalTransition(LETTER letter, STATE succ) {
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
