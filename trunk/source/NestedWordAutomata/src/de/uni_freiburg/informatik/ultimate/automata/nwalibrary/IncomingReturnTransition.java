package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.text.MessageFormat;


/**
 * Return Transition of a successor state.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class IncomingReturnTransition<LETTER,STATE> {
	
	private final STATE m_LinPred;
	private final STATE m_HierPred;
	private final LETTER m_Letter; 

	
	public IncomingReturnTransition(STATE linPred, STATE hierPred, LETTER letter) {
		m_LinPred = linPred;
		m_HierPred = hierPred;
		m_Letter = letter;
	}
	
	public STATE getLinPred() {
		return m_LinPred;
	}
	
	public STATE getHierPred() {
		return m_HierPred;
	}
	
	public LETTER getLetter() {
		return m_Letter;
	}
	
	
	public String toString() {
		return MessageFormat.format("( {0} , {1} , {2} , _ )",getLinPred(), getHierPred(), getLetter());
	}
	
}
