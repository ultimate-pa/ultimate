package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
/*
 * A Bottom-up TreeAutomaton. The rules have the form f(q1,...,qn) ~> q
 * 
 * 
 * @param <LETTER> is the type of the alphabet.
 * @param <STATE> is the type of the states.
 * 
 * @author Mostafa M.A.
 */
public class TreeAutomatonBU<LETTER, STATE> implements ITreeAutomaton<LETTER, STATE> {
	
	private Map<List<STATE>, Map<LETTER, Iterable<STATE>>> parentsMap;
	private Map<STATE, Map<LETTER, Iterable<List<STATE>>>> childrenMap;
	private Set<LETTER> alphabet;
	private Set<STATE> finalStates, initalStates, states;
	
	public TreeAutomatonBU() {
		childrenMap = new HashMap<STATE, Map<LETTER,Iterable<List<STATE>>>>();
		parentsMap = new HashMap<List<STATE>, Map<LETTER,Iterable<STATE>>>();
		alphabet = new HashSet<LETTER>();

		finalStates = new HashSet<STATE>();
		states = new HashSet<STATE>();
		initalStates = new HashSet<STATE>();
		
	}
	public void addRule(LETTER letter, List<STATE> src, STATE dest) {
		// f(q1,...,qn) -> q
		addLetter(letter);
		addState(dest);
		for (STATE state : src) {
			addState(state);
		}
		// children(q)[f] = <q1, ..., qn>
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

	public void addLetter(LETTER letter) {
		alphabet.add(letter);
	}

	public void addState(STATE state) {
		states.add(state);
	}
	public void addFinalState(STATE state) {
		finalStates.add(state);
		addState(state);
	}
	public void addInitialState(STATE state) {
		initalStates.add(state);
		addState(state);
	}
	
	@Override
	public Set<LETTER> getAlphabet() {
		return alphabet;
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return null;
	}

	@Override
	public int size() {
		return states.size();
	}

	@Override
	public String sizeInformation() {
		return size() + " nodes";
	}

	@Override
	public Set<STATE> getInitialStates() {
		return initalStates;
	}

	public Set<STATE> getStates() {
		return states;
	}
	@Override
	public boolean isFinalState(STATE state) {
		// TODO Auto-generated method stub
		return finalStates.contains(state);
	}

	@Override
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getSuccessors(List<STATE> states) {
		List<TreeAutomatonRule<LETTER, STATE>> successors = new LinkedList<TreeAutomatonRule<LETTER, STATE>>();
		for (LETTER letter : parentsMap.get(states).keySet()) {
			for (STATE state : parentsMap.get(states).get(letter)) {
				successors.add(new TreeAutomatonRule<LETTER, STATE>(letter, states, state));
			}
		}
		return successors;
	}
	
	@Override
	public boolean isInitialState(STATE state) {
		return initalStates.contains(state);
	}

	public Iterator<TreeAutomatonRule<LETTER, STATE>> getRulesIterator() {
		
		final Iterator<STATE> qStates = states.iterator();
		return new Iterator<TreeAutomatonRule<LETTER, STATE>>() {

			Iterator<LETTER> letters;
			Iterator<List<STATE>> parents;

			LETTER currentLetter;
			STATE currentState;
			List<STATE> currentParent;
			private boolean initalized = false;
			
			private boolean moveNextState() {
				if (!qStates.hasNext()) {currentState = null; return false;}
				currentState = qStates.next();
				letters = getPredecessors(currentState).keySet().iterator();
				return true;
			}
			private boolean moveNextLetter() {
				if (letters == null || !letters.hasNext()) {
					if (!moveNextState()) { currentLetter = null; return false; }
					return moveNextLetter();
				}
				currentLetter = letters.next();
				parents = getPredecessors(currentState, currentLetter).iterator();
				return true;
			}
			private boolean moveNextParent() { 
				if (parents == null || !parents.hasNext()) {
					if (!moveNextLetter()) { currentParent = null; return false;}
					return moveNextParent();
				}
				currentParent = parents.next();
				return true;
			}
			private void initalize() {
				if (!initalized) {
					initalized = true;
					moveNextParent();
				}
			}
			public boolean hasNext() {
				initalize();
				return currentParent != null;
			}

			@Override
			public TreeAutomatonRule<LETTER, STATE> next() {
				if (!hasNext()) {
					throw new NoSuchElementException();
				}
				TreeAutomatonRule<LETTER, STATE> rule = new TreeAutomatonRule<LETTER, STATE>(currentLetter, currentParent, currentState);
				moveNextParent();
				return rule;
			}
		};
	}
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getRules() {

		ArrayList<TreeAutomatonRule<LETTER, STATE>> list = new ArrayList<>();

		for (STATE child : childrenMap.keySet()) {
			for (LETTER letter : childrenMap.get(child).keySet()) {
				for (List<STATE> rule : childrenMap.get(child).get(letter)) {
					list.add(new TreeAutomatonRule<LETTER, STATE>(letter, rule, child));
				}
			}
		}
		return list;
	}
	@Override
	public Iterable<STATE> getSuccessors(List<STATE> states, LETTER letter) {
		return parentsMap.get(states).get(letter);
	}

	@Override
	public Map<LETTER, Iterable<List<STATE>>> getPredecessors(STATE state) {
		return childrenMap.get(state);
	}

	@Override
	public Iterable<List<STATE>> getPredecessors(STATE state, LETTER letter) {
		return childrenMap.get(state).get(letter);
	}
	
	public void complementFinals() {
		Set<STATE> newFinals = new HashSet<STATE>();
		for (STATE st : states) {
			if (!isFinalState(st)) {
				newFinals.add(st);
			}
		}
		finalStates = newFinals;
	}
	public String stateString(STATE state) {
		String res = state.toString();
		if (initalStates.contains(state))
			res += "_";
		if (isFinalState(state))
			res += "*";
		return res;
	}
	public String toString() {
		String statesString = "";
		for (STATE state : states) {
			statesString += stateString(state) + " ";
		}
		String rulesString = "";
		for (STATE child : childrenMap.keySet()) {
			for (LETTER letter : childrenMap.get(child).keySet()) {
				for (List<STATE> rule : childrenMap.get(child).get(letter)) {
					rulesString += String.format("%s%s ~~> %s\n", letter, rule, stateString(child));
				}
			}
		}
		return statesString + "\n" + rulesString;
	}
}
