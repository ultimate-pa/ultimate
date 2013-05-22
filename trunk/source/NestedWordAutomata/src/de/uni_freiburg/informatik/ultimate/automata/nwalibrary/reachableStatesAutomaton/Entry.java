package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates.ReachProp;

class Entry<LETTER,STATE> {
	private final STATE m_State;
	private final Map<STATE,ReachProp> m_Down;

	Entry(STATE state) {
		assert state != null;
		this.m_State = state;
		this.m_Down = new HashMap<STATE,ReachProp>();
	}

	STATE getState() {
		return m_State;
	}
	
	Map<STATE,ReachProp> getDownStates() {
		return m_Down;
	}

	public String toString() {
		return m_State.toString();
	}
	

}
