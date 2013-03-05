package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;


/**
 * Return transition outgoing of some state.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class OutgoingReturnTransition<LETTER,STATE> {
	
	private final STATE m_HierPred;
	private final LETTER m_Letter; 
	private final STATE m_Succ;

	
	public OutgoingReturnTransition(STATE hierPred, LETTER letter, STATE succ) {
		m_HierPred = hierPred;
		m_Letter = letter;
		m_Succ = succ;
	}
	
	public STATE getHierPred() {
		return m_HierPred;
	}
	
	public LETTER getLetter() {
		return m_Letter;
	}
	
	public STATE getSucc() {
		return m_Succ;
	}

	
}
