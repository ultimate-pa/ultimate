package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;


/**
 * Return Transition of a hierarchical predecessor.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class SummaryReturnTransition<LETTER,STATE> {
	
	private final STATE m_LinPred;
	private final LETTER m_Letter; 
	private final STATE m_Succ;
	
	public SummaryReturnTransition(STATE linPred, LETTER letter, STATE succ) {
		m_LinPred = linPred;
		m_Letter = letter;
		m_Succ = succ;
	}
	
	public STATE getLinPred() {
		return m_LinPred;
	}
	public LETTER getLetter() {
		return m_Letter;
	}
	public STATE getSucc() {
		return m_Succ;
	}
	
}
