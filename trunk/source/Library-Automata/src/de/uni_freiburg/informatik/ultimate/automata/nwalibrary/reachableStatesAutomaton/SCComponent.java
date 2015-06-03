package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.HashSet;
import java.util.Set;

public class SCComponent<LETTER, STATE> {

	protected StateContainer<LETTER, STATE> m_RootNode;
	protected final Set<StateContainer<LETTER, STATE>> m_AllStates = new HashSet<StateContainer<LETTER, STATE>>();

	public SCComponent() {
		super();
	}

	public int getNumberOfStates() {
		return m_AllStates.size();
	}

	public StateContainer<LETTER, STATE> getRootNode() {
		return m_RootNode;
	}

	/**
	 * @return The {@link StateContainer}s of all states that are 
	 * contained in this SCC.
	 */
	public Set<StateContainer<LETTER, STATE>> getAllStatesContainers() {
		return m_AllStates;
	}

}