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

	/**
	 * @return all states (not state containers) of this SCC.
	 * This methods is not efficient because a new Set is constructed.
	 * At the moment this is a workaround for Thomas' loop complexity
	 * project.
	 */
	public Set<STATE> getNodes() {
		Set<STATE> result = new HashSet<>();
		for (StateContainer<LETTER, STATE> sc : m_AllStates) {
			result.add(sc.getState());
		}
		return result;
	}

}