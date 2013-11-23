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
public class IncomingReturnTransition<LETTER,STATE> implements Transitionlet<LETTER,STATE> {
	
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

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((m_HierPred == null) ? 0 : m_HierPred.hashCode());
		result = prime * result
				+ ((m_Letter == null) ? 0 : m_Letter.hashCode());
		result = prime * result
				+ ((m_LinPred == null) ? 0 : m_LinPred.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		IncomingReturnTransition other = (IncomingReturnTransition) obj;
		if (m_HierPred == null) {
			if (other.m_HierPred != null)
				return false;
		} else if (!m_HierPred.equals(other.m_HierPred))
			return false;
		if (m_Letter == null) {
			if (other.m_Letter != null)
				return false;
		} else if (!m_Letter.equals(other.m_Letter))
			return false;
		if (m_LinPred == null) {
			if (other.m_LinPred != null)
				return false;
		} else if (!m_LinPred.equals(other.m_LinPred))
			return false;
		return true;
	}
	
	
	
}
