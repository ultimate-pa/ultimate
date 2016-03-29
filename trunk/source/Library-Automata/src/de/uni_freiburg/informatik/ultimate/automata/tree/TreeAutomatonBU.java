package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public class TreeAutomatonBU<LETTER, STATE> implements ITreeAutomaton<LETTER, STATE> {
	
	private Map<List<STATE>, Map<LETTER, Iterable<STATE>>> parentsMap;
	private Map<STATE, Map<LETTER, Iterable<List<STATE>>>> childrenMap;
	private Set<LETTER> alphabet;
	private Set<STATE> finalStates, initalStates, states;
	
	public void addRule(LETTER letter, List<STATE> src, STATE dest) {
		// f(q1,...,qn) -> q
		if (alphabet == null) {
			alphabet = new HashSet<LETTER>();
		}
		alphabet.add(letter);
		
		// children(q)[f] = <q1, ..., qn>
		if (childrenMap == null) {
			childrenMap = new HashMap<STATE, Map<LETTER,Iterable<List<STATE>>>>();
		}
		if (!childrenMap.containsKey(dest)) {
			childrenMap.put(dest, new HashMap<LETTER, Iterable<List<STATE>>>());
		}
		Map<LETTER, Iterable<List<STATE>>> childLetter = childrenMap.get(dest);
		if (!childLetter.containsKey(letter)) {
			childLetter.put(letter, new LinkedList<List<STATE>>());
		}
		LinkedList<List<STATE>> children = (LinkedList<List<STATE>>) childLetter.get(letter);
		children.add(src);
		
		// parents(q1, ..., qn)[f] = q
		if (parentsMap == null) {
			parentsMap = new HashMap<List<STATE>, Map<LETTER,Iterable<STATE>>>();
		}
		if (!parentsMap.containsKey(src)) {
			parentsMap.put(src, new HashMap<LETTER, Iterable<STATE>>());
		}
		Map<LETTER, Iterable<STATE>> parentLetter = parentsMap.get(src);
		if (!parentLetter.containsKey(letter)) {
			parentLetter.put(letter, new LinkedList<STATE>());
		}
		LinkedList<STATE> parents = (LinkedList<STATE>) parentLetter.get(letter);
		parents.add(dest);
	}
	@Override
	public Set<LETTER> getAlphabet() {
		// TODO Auto-generated method stub
		return alphabet;
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return states.size();
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return size() + " nodes";
	}

	@Override
	public Set<STATE> getInitialStates() {
		// TODO Auto-generated method stub
		return initalStates;
	}

	@Override
	public boolean isFinalState(STATE state) {
		// TODO Auto-generated method stub
		return finalStates.contains(state);
	}

	@Override
	public Iterable<OutgoingTreeTransition<LETTER, STATE>> getSuccessors(List<STATE> states) {
		List<OutgoingTreeTransition<LETTER, STATE>> successors = new LinkedList<OutgoingTreeTransition<LETTER, STATE>>();
		for (LETTER letter : parentsMap.get(states).keySet()) {
			for (STATE state : parentsMap.get(states).get(letter)) {
				successors.add(new OutgoingTreeTransition<LETTER, STATE>(letter, state));
			}
		}
		return successors;
	}

	@Override
	public Iterable<STATE> getSuccessors(List<STATE> states, LETTER letter) {
		return parentsMap.get(states).get(letter);
	}

	public Map<LETTER, Iterable<List<STATE>>> getPredecessors(STATE state) {
		return childrenMap.get(state);
	}

	public Iterable<List<STATE>> getPredecessors(STATE state, LETTER letter) {
		return childrenMap.get(state).get(letter);
	}
}
