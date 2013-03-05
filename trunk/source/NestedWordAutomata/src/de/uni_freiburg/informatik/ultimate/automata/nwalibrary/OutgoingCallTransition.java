package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;


/**
 * Outgoing call transition of a state.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class OutgoingCallTransition<LETTER,STATE> {
	
	private final LETTER m_Letter; 
	private final STATE m_Succ;
	
	public OutgoingCallTransition(LETTER letter, STATE succ) {
		m_Letter = letter;
		m_Succ = succ;
	}
	
	public LETTER getLetter() {
		return m_Letter;
	}
	
	public STATE getSucc() {
		return m_Succ;
	}
	
}
