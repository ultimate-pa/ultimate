package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.HashRelation;

public class SCComponentForNWARS<LETTER, STATE> extends SCComponent<LETTER, STATE> {
	final Set<StateContainer<LETTER, STATE>> m_AcceptingStates = new HashSet<StateContainer<LETTER, STATE>>();
	final NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates;
	/**
	 * States that have an outgoing summary. The summary successor may
	 * could be outside of this SCC. We determine the needed set only if
	 * construction of this SCC is finished.
	 */
	Set<StateContainer<LETTER, STATE>> m_HasOutgoingAcceptingSum = new HashSet<StateContainer<LETTER, STATE>>();
	final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> m_AcceptingSummariesOfSCC = new HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>>();
	/**
	 * State of SCC with lowest serial number.
	 */
	private StateContainer<LETTER, STATE> m_StateWithLowestSerialNumber;
	/**
	 * State of SCC with lowest serial number that is accepting or
	 * successor
	 */
	private StateContainer<LETTER, STATE> m_AcceptingWithLowestSerialNumber;
	
	public SCComponentForNWARS(NestedWordAutomatonReachableStates<LETTER, STATE> nwars) {
		nestedWordAutomatonReachableStates = nwars;
	}

	public void addState(StateContainer<LETTER, STATE> cont) {
		if (m_RootNode != null) {
			throw new UnsupportedOperationException("If root node is set SCC may not be modified");
		}
		m_AllStates.add(cont);
		m_StateWithLowestSerialNumber = StateContainer.returnLower(m_StateWithLowestSerialNumber, cont);

		if (nestedWordAutomatonReachableStates.isFinal(cont.getState())) {
			m_AcceptingStates.add(cont);
			m_AcceptingWithLowestSerialNumber = StateContainer.returnLower(m_AcceptingWithLowestSerialNumber,
					cont);
		}
		if (nestedWordAutomatonReachableStates.getAcceptingSummariesComputation().getAcceptingSummaries().getDomain().contains(cont)) {
			m_HasOutgoingAcceptingSum.add(cont);
			// if we have to update lowest is determined later
		}
	}

	public void setRootNode(StateContainer<LETTER, STATE> rootNode) {
		if (m_RootNode != null) {
			throw new UnsupportedOperationException("If root node is set SCC may not be modified");
		}
		this.m_RootNode = rootNode;
		// TODO: Optimization: compute this only if there is no
		// accepting state in SCC
		for (StateContainer<LETTER, STATE> pred : m_HasOutgoingAcceptingSum) {
			for (Summary<LETTER, STATE> summary : nestedWordAutomatonReachableStates.getAcceptingSummariesComputation().getAcceptingSummaries().getImage(pred)) {
				if (m_AllStates.contains(summary.getSucc())) {
					m_AcceptingWithLowestSerialNumber = StateContainer.returnLower(
							m_AcceptingWithLowestSerialNumber, pred);
					m_AcceptingSummariesOfSCC.addPair(pred, summary);
				}
			}
		}
		m_HasOutgoingAcceptingSum = null;
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

	public Set<StateContainer<LETTER, STATE>> getAcceptingStatesContainers() {
		return m_AcceptingStates;
	}
	
	public HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> getAcceptingSummariesOfSCC() {
		return m_AcceptingSummariesOfSCC;
	}

	public StateContainer<LETTER, STATE> getStateWithLowestSerialNumber() {
		return m_StateWithLowestSerialNumber;
	}

	public boolean isAccepting() {
		return m_AcceptingWithLowestSerialNumber != null;
	}

	/**
	 * Returns the state with the lowest serial number that is accepting
	 * or call predecessor of an accepting summary. Returns null if no
	 * such state exists.
	 * 
	 * @return
	 */
	public StateContainer<LETTER, STATE> getAcceptingWithLowestSerialNumber() {
		return m_AcceptingWithLowestSerialNumber;
	}

}