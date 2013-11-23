package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;

class Summary<LETTER, STATE> {
	private final StateContainer<LETTER, STATE> m_HierPred;
	private final StateContainer<LETTER, STATE> m_LinPred;
	private final LETTER m_Letter;
	private final StateContainer<LETTER, STATE> m_Succ;
	public Summary(StateContainer<LETTER, STATE> hierPred, 
			StateContainer<LETTER, STATE> linPred,
			LETTER letter,
			StateContainer<LETTER, STATE> succ) {
		super();
		m_HierPred = hierPred;
		m_LinPred = linPred;
		m_Letter = letter;
		m_Succ = succ;
	}
	public StateContainer<LETTER, STATE> getHierPred() {
		return m_HierPred;
	}
	public StateContainer<LETTER, STATE> getLinPred() {
		return m_LinPred;
	}
	public LETTER getLetter() {
		return m_Letter;
	}
	public StateContainer<LETTER, STATE> getSucc() {
		return m_Succ;
	}
	

	
	public IncomingReturnTransition<LETTER, STATE> obtainIncomingReturnTransition(
			NestedWordAutomatonReachableStates<LETTER, STATE> nwars) {
		for (IncomingReturnTransition<LETTER, STATE> inTrans  : 
			nwars.returnPredecessors(getHierPred().getState(), getLetter(), getSucc().getState())) {
			if (getLinPred().getState().equals(inTrans.getLinPred())) {
				return inTrans;
			}
		}
		throw new AssertionError("no such transition");
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((m_HierPred == null) ? 0 : m_HierPred.hashCode());
		result = prime * result
				+ ((m_LinPred == null) ? 0 : m_LinPred.hashCode());
		result = prime * result
				+ ((m_Succ == null) ? 0 : m_Succ.hashCode());
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
		Summary other = (Summary) obj;
		if (m_HierPred == null) {
			if (other.m_HierPred != null)
				return false;
		} else if (!m_HierPred.equals(other.m_HierPred))
			return false;
		if (m_LinPred == null) {
			if (other.m_LinPred != null)
				return false;
		} else if (!m_LinPred.equals(other.m_LinPred))
			return false;
		if (m_Succ == null) {
			if (other.m_Succ != null)
				return false;
		} else if (!m_Succ.equals(other.m_Succ))
			return false;
		return true;
	}
	@Override
	public String toString() {
		return "(" + m_HierPred + ", " + m_LinPred + ", " + m_Succ + ")";
	}
	
	
}
