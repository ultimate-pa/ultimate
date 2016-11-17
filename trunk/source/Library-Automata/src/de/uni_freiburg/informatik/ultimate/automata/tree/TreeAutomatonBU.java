package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
/**
 * A Bottom-up TreeAutomaton. The rules have the form f(q1,...,qn) ~> q
 * 
 * 
 * @param <LETTER> is the type of the alphabet.
 * @param <STATE> is the type of the states.
 * 
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 */
public class TreeAutomatonBU<LETTER, STATE> implements ITreeAutomaton<LETTER, STATE> {
	
	private final Map<List<STATE>, Map<LETTER, Iterable<STATE>>> parentsMap;
	private final Map<STATE, Map<LETTER, Iterable<List<STATE>>>> childrenMap;
	private final Map<LETTER, Iterable<TreeAutomatonRule<LETTER, STATE>>> lettersMap;
	private final Map<STATE, Iterable<TreeAutomatonRule<LETTER, STATE>>> sourceMap;
	private final Set<LETTER> alphabet;
	private final Set<STATE> finalStates;
	private final Set<STATE> initalStates;
	private final Set<STATE> states;
	
	/**
	 * Create a TreeAutomaton.	
	 */
	public TreeAutomatonBU() {
		childrenMap = new HashMap<>();
		parentsMap = new HashMap<>();
		alphabet = new HashSet<>();
		lettersMap = new HashMap<>();
		sourceMap = new HashMap<>();

		finalStates = new HashSet<>();
		states = new HashSet<>();
		initalStates = new HashSet<>();
	}
	
	/**
	 * Add a rule to the automaton.
	 * @param rule
	 */
	public void addRule(final TreeAutomatonRule<LETTER, STATE> rule) {
		final LETTER letter = rule.getLetter();
		final STATE dest = rule.getDest();
		final List<STATE> src = rule.getSource();
		
		// f(q1,...,qn) -> q
		addLetter(letter);
		addState(dest);
		for (final STATE state : src) {
			addState(state);
		}
		// children(q)[f] = <q1, ..., qn>
		if (!childrenMap.containsKey(dest)) {
			childrenMap.put(dest, new HashMap<LETTER, Iterable<List<STATE>>>());
		}
		final Map<LETTER, Iterable<List<STATE>>> childLetter = childrenMap.get(dest);
		if (!childLetter.containsKey(letter)) {
			childLetter.put(letter, new HashSet<List<STATE>>());
		}
		final HashSet<List<STATE>> children = (HashSet<List<STATE>>) childLetter.get(letter);
		children.add(src);
		
		// parents(q1, ..., qn)[f] = q
		if (!parentsMap.containsKey(src)) {
			parentsMap.put(src, new HashMap<LETTER, Iterable<STATE>>());
		}
		final Map<LETTER, Iterable<STATE>> parentLetter = parentsMap.get(src);
		if (!parentLetter.containsKey(letter)) {
			parentLetter.put(letter, new HashSet<STATE>());
		}
		final Set<STATE> parents = (Set<STATE>) parentLetter.get(letter);
		parents.add(dest);
		
		// lettersMap[f] = [f(p) -> q]
		if (!lettersMap.containsKey(letter)) {
			lettersMap.put(letter, new HashSet<>());
		}
		final HashSet<TreeAutomatonRule<LETTER, STATE>> rulesByLetter = (HashSet<TreeAutomatonRule<LETTER, STATE>>) lettersMap.get(letter);
		rulesByLetter.add(rule);
		
		// sourceRules[q] = {f(p1, ..., q, ... pn) -> p0}
		for (final STATE st : src) {
			if (!sourceMap.containsKey(st)) {
				sourceMap.put(st, new HashSet<>());
			}
			final HashSet<TreeAutomatonRule<LETTER, STATE>> rulesBySource = (HashSet<TreeAutomatonRule<LETTER, STATE>>) sourceMap.get(st);
			rulesBySource.add(rule);
		}
	}
	
	public void extendAlphabet(final Collection<LETTER> sigma) {
		alphabet.addAll(sigma);
	}
	
	public void addRule(final LETTER letter, final List<STATE> src, final STATE dest) {
		addRule(new TreeAutomatonRule<LETTER, STATE>(letter, src, dest));
	}

	public void addLetter(final LETTER letter) {
		alphabet.add(letter);
	}

	public void addState(final STATE state) {
		states.add(state);
	}
	
	public void addFinalState(final STATE state) {
		finalStates.add(state);
		addState(state);
	}
	
	public void addInitialState(final STATE state) {
		initalStates.add(state);
		addState(state);
	}
	
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getRulesByLetter(final LETTER letter) {
		return lettersMap.get(letter);
	}

	public Iterable<TreeAutomatonRule<LETTER, STATE>> getRulesBySource(final STATE src) {
		return sourceMap.get(src);
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

	@Override
	public Set<STATE> getStates() {
		return states;
	}
	
	@Override
	public boolean isFinalState(final STATE state) {
		return finalStates.contains(state);
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
			@Override
			public boolean hasNext() {
				initalize();
				return currentParent != null;
			}

			@Override
			public TreeAutomatonRule<LETTER, STATE> next() {
				if (!hasNext()) {
					throw new NoSuchElementException();
				}
				final TreeAutomatonRule<LETTER, STATE> rule = new TreeAutomatonRule<LETTER, STATE>(currentLetter, currentParent, currentState);
				moveNextParent();
				return rule;
			}
		};
	}
	@Override
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getRules() {

		final ArrayList<TreeAutomatonRule<LETTER, STATE>> list = new ArrayList<>();

		for (final STATE child : childrenMap.keySet()) {
			for (final LETTER letter : childrenMap.get(child).keySet()) {
				for (final List<STATE> rule : childrenMap.get(child).get(letter)) {
					list.add(new TreeAutomatonRule<LETTER, STATE>(letter, rule, child));
				}
			}
		}
		return list;
	}

	@Override
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getSuccessors(final List<STATE> states) {
		final List<TreeAutomatonRule<LETTER, STATE>> successors = new ArrayList<>();
		for (final LETTER letter : parentsMap.get(states).keySet()) {
			for (final STATE state : parentsMap.get(states).get(letter)) {
				successors.add(new TreeAutomatonRule<LETTER, STATE>(letter, states, state));
			}
		}
		return successors;
	}
	
	@Override
	public Iterable<STATE> getSuccessors(final List<STATE> states, final LETTER letter) {
		if (!parentsMap.containsKey(states) || !parentsMap.get(states).containsKey(letter)) {
			return new ArrayList<>();
		}
		return parentsMap.get(states).get(letter);
	}

	@Override
	public Map<LETTER, Iterable<List<STATE>>> getPredecessors(final STATE state) {
		if (!childrenMap.containsKey(state)) {
			return new HashMap<>();
		}
		return childrenMap.get(state);
	}

	@Override
	public Iterable<List<STATE>> getPredecessors(final STATE state, final LETTER letter) {
		if (!childrenMap.containsKey(state) || !childrenMap.get(state).containsKey(letter)) {
			return new ArrayList<>();
		}
		return childrenMap.get(state).get(letter);
	}
	
	public void complementFinals() {
		final Set<STATE> newFinals = new HashSet<>();
		for (final STATE st : states) {
			if (!isFinalState(st)) {
				newFinals.add(st);
			}
		}
		finalStates.clear();
		finalStates.addAll(newFinals);
	}
	
	public String stateString(STATE state) {
		String res = state.toString();
		if (initalStates.contains(state)) {
			res += "_";
		}
		if (isFinalState(state)) {
			res += "*";
		}
		return res;
	}
	
	public String DebugString() {
		String statesString = "";
		for (final STATE state : states) {
			statesString += stateString(state) + " ";
		}
		String rulesString = "";
		for (final STATE child : childrenMap.keySet()) {
			for (final LETTER letter : childrenMap.get(child).keySet()) {
				for (final List<STATE> rule : childrenMap.get(child).get(letter)) {
					rulesString += String.format("%s%s ~~> %s\n", letter, rule, stateString(child));
				}
			}
		}
		return statesString + "\n" + rulesString;
	}
	
	@Override
	public String toString() {
		
		String alphabet = "";
		for (final LETTER letter : this.alphabet) {
			if (!alphabet.isEmpty()) {
				alphabet += " ";
			}
			alphabet += letter.toString();
		}
		
		String states = "";
		for (final STATE state : this.states) {
			if (!states.isEmpty()) {
				states += " ";
			}
			states += state.toString();
		}
		
		String initialStates = "";
		for (final STATE state : this.initalStates) {
			if (!initialStates.isEmpty()) {
				initialStates += " ";
			}
			initialStates += state.toString();
		}
		
		String finalStates = "";
		for (final STATE state : this.finalStates) {
			if (!finalStates.isEmpty()) {
				finalStates += " ";
			}
			finalStates += state.toString();
		}
		
		String transitionTable = "";
		for (final TreeAutomatonRule<LETTER, STATE> rule : getRules()) {
			if (!transitionTable.isEmpty()) {
				transitionTable += "\n";
			}
			String src = "";
			for (final STATE st : rule.getSource()) {
				if (!src.isEmpty()) {
					src += " ";
				}
				src += st.toString();
			}
			transitionTable += String.format("\t\t((%s) %s %s)", src, rule.getLetter(), rule.getDest());
		}
		return String.format("TreeAutomaton %s = {\n\talphabet = {%s},\n\tstates = {%s},\n\tinitialStates = {%s},\n\tfinalStates = {%s},\n\ttransitionTable = {\n%s\n\t}\n}", "ta" + hashCode() % 1000000 , alphabet, states, initialStates, finalStates, transitionTable);
		
	}
}
