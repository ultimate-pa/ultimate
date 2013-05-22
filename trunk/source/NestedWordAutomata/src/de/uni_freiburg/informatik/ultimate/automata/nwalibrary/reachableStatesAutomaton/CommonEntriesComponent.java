package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


class CommonEntriesComponent<LETTER,STATE> {
	int m_Size = 0;
	final Set<Entry<LETTER,STATE>> m_Entries;
	final Set<STATE> m_DownStates;
	final Set<STATE> m_ReturnOutCandidates;
	final Map<StateContainer<LETTER,STATE>,Set<StateContainer<LETTER,STATE>>> m_BorderOut;


	CommonEntriesComponent(HashSet<Entry<LETTER,STATE>> entries, HashSet<STATE> downStates) {
		assert NestedWordAutomatonReachableStates.noElementIsNull(entries);
		this.m_Entries = entries;
		this.m_DownStates = downStates;
		this.m_ReturnOutCandidates = new HashSet<STATE>();
		this.m_BorderOut = new HashMap<StateContainer<LETTER,STATE>,Set<StateContainer<LETTER,STATE>>>();
	}



	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Entries: ").append(m_Entries).append("\n");
		sb.append("DownStates: ").append(m_DownStates).append("\n");
		sb.append("Size: ").append(m_Size).append("\n");
		sb.append("ReturnOutCandiates: ").append(m_ReturnOutCandidates).append("\n");
		sb.append("BorderOut: ").append(m_BorderOut).append("\n");
		return sb.toString();
	}

	Set<Entry<LETTER,STATE>> getEntries() {
		return Collections.unmodifiableSet(this.m_Entries);
	}

	void addReturnOutCandicate(STATE returnCandidate) {
		m_ReturnOutCandidates.add(returnCandidate);
	}
	//
	//private void removeReturnOutCandicate(STATE returnCandidate) {
	//boolean modified = m_ReturnOutCandidates.remove(returnCandidate);
	//if (!modified) {
	//throw new AssertionError("state not contained");
	//}
	//}

	Set<STATE> getReturnOutCandidates() {
		assert m_ReturnOutCandidates.size() == m_Size;
		return m_ReturnOutCandidates;
	}

	Set<STATE> getDownStates() {
		assert m_ReturnOutCandidates.size() == m_Size;
		return Collections.unmodifiableSet(this.m_DownStates);
	}

	private boolean isBorderState(StateContainer<LETTER, STATE> state) {
		assert m_ReturnOutCandidates.size() == m_Size;
		return m_BorderOut.containsKey(state);
	}

	private void removeBorderState(StateContainer<LETTER, STATE> resident) {
		Set<StateContainer<LETTER,STATE>> foreigners = m_BorderOut.remove(resident);
		if (foreigners == null) {
			throw new AssertionError("state not contained");
		}
	}

	private Set<StateContainer<LETTER,STATE>> getForeigners(StateContainer<LETTER, STATE> resident) {
		assert m_ReturnOutCandidates.size() == m_Size;
		return m_BorderOut.get(resident);
	}

	void addBorderCrossing(StateContainer<LETTER,STATE> resident, StateContainer<LETTER,STATE> foreigner) {
		Set<StateContainer<LETTER,STATE>> foreigners = m_BorderOut.get(resident);
		if (foreigners == null) {
			foreigners = new HashSet<StateContainer<LETTER,STATE>>();
			m_BorderOut.put(resident, foreigners);
		}
		foreigners.add(foreigner);
	}


	void addDownState(STATE down) {
		m_DownStates.add(down);
	}

	void moveWithoutBorderUpdate(StateContainer<LETTER, STATE> sc, CommonEntriesComponent targetCec) {
		sc.setCommonEntriesComponent(targetCec);
		m_Size--;
		targetCec.m_Size++;
		if (m_ReturnOutCandidates.contains(sc.getState())) {
			targetCec.m_ReturnOutCandidates.add(sc.getState());
			this.m_ReturnOutCandidates.remove(sc.getState());
		}
	}
}

	
	
