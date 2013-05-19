package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DoubleDeckerVisitor.ReachFinal;

public class DoubleDeckerAutomaton<LETTER, STATE> extends NestedWordAutomaton<LETTER, STATE> 
							implements IDoubleDeckerAutomaton<LETTER, STATE> {
	
	
	private Map<STATE,Map<STATE,ReachFinal>> m_Up2Down;
	
	public DoubleDeckerAutomaton(Collection<LETTER> internalAlphabet,
			   Collection<LETTER> callAlphabet,
			   Collection<LETTER> returnAlphabet,
			   StateFactory<STATE> stateFactory) {
		super(internalAlphabet, callAlphabet, returnAlphabet, stateFactory);
	}
	
	
	public boolean up2DownIsSet() {
		return m_Up2Down != null; 
	}
	
	@Deprecated
	public Set<STATE> getDownStates(STATE up) {
		return m_Up2Down.get(up).keySet();
	}
	
	public void setUp2Down(Map<STATE,Map<STATE,ReachFinal>> up2Down) {
		if (m_Up2Down == null) {
			m_Up2Down = up2Down;
		} else {
			throw new AssertionError("up2down already set");
		}
	}
	
	
	
	/**
	 * Returns true iff there is a reachable configuration in which the 
	 * automaton is in STATE <i>up</i> and the STATE <i>down</i> is the topmost
	 * stack element.
	 */
	public boolean isDoubleDecker(STATE up, STATE down) {
		if (m_Up2Down == null) {
			throw new AssertionError("up2down not set");
		} else {
			if (this.getStates().contains(up)) {
				Map<STATE, ReachFinal> downStates = m_Up2Down.get(up);
				if (this.getStates().contains(down)) {
					return downStates.get(down) != null;
				} else {
					return false;
				}
			} else {
				return false;
			}
		}
	}
}
