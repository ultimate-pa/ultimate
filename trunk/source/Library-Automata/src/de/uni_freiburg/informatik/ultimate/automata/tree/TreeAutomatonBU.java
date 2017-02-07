/*
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2014-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
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
public class TreeAutomatonBU<LETTER, STATE> implements ITreeAutomatonBU<LETTER, STATE> {
	
	private final Map<List<STATE>, Map<LETTER, Iterable<TreeAutomatonRule<LETTER, STATE>>>> mParentsMap;
	private final Map<STATE, Map<LETTER, Iterable<TreeAutomatonRule<LETTER, STATE>>>> mChildrenMap;
	private final Map<LETTER, Iterable<TreeAutomatonRule<LETTER, STATE>>> mLettersMap;
	private final Map<STATE, Iterable<TreeAutomatonRule<LETTER, STATE>>> mSourceMap;
	private final Set<TreeAutomatonRule<LETTER, STATE>> mRules;
	private final Set<LETTER> mAlphabet;
	private final Set<STATE> mFinalStates;
	private final Set<STATE> mInitalStates;
	private final Set<STATE> mStates;
	
	/**
	 * Create a TreeAutomaton.	
	 */
	public TreeAutomatonBU() {
		mChildrenMap = new HashMap<>();
		mParentsMap = new HashMap<>();
		mAlphabet = new HashSet<>();
		mLettersMap = new HashMap<>();
		mSourceMap = new HashMap<>();
		mRules = new HashSet<>();
		mFinalStates = new HashSet<>();
		mStates = new HashSet<>();
		mInitalStates = new HashSet<>();
	}
	
	/**
	 * Add a rule to the automaton.
	 * @param rule
	 */
	public void addRule(final TreeAutomatonRule<LETTER, STATE> rule) {
		for (TreeAutomatonRule<LETTER, STATE> x : mRules) {
			System.err.println("\t" + x);
		}
		System.err.println(rule);
		System.err.println();
		if (mRules.contains(rule)) {
			// If rule already exists, do nothing
			return;
		}
		mRules.add(rule);
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
		if (!mChildrenMap.containsKey(dest)) {
			mChildrenMap.put(dest, new HashMap<LETTER, Iterable<TreeAutomatonRule<LETTER, STATE>>>());
		}
		final Map<LETTER, Iterable<TreeAutomatonRule<LETTER, STATE>>> childLetter = mChildrenMap.get(dest);
		if (!childLetter.containsKey(letter)) {
			childLetter.put(letter, new HashSet<TreeAutomatonRule<LETTER, STATE>>());
		}
		final HashSet<TreeAutomatonRule<LETTER, STATE>> children = (HashSet<TreeAutomatonRule<LETTER, STATE>>) childLetter.get(letter);
		children.add(rule);
		
		// parents(q1, ..., qn)[f] = q
		if (!mParentsMap.containsKey(src)) {
			mParentsMap.put(src, new HashMap<LETTER, Iterable<TreeAutomatonRule<LETTER, STATE>>>());
		}
		final Map<LETTER, Iterable<TreeAutomatonRule<LETTER, STATE>>> parentLetter = mParentsMap.get(src);
		if (!parentLetter.containsKey(letter)) {
			parentLetter.put(letter, new HashSet<TreeAutomatonRule<LETTER, STATE>>());
		}
		final Set<TreeAutomatonRule<LETTER, STATE>> parents = (Set<TreeAutomatonRule<LETTER, STATE>>) parentLetter.get(letter);
		parents.add(rule);
		
		// lettersMap[f] = [f(p) -> q]
		if (!mLettersMap.containsKey(letter)) {
			mLettersMap.put(letter, new HashSet<>());
		}
		final HashSet<TreeAutomatonRule<LETTER, STATE>> rulesByLetter = (HashSet<TreeAutomatonRule<LETTER, STATE>>) mLettersMap.get(letter);
		rulesByLetter.add(rule);
		
		// sourceRules[q] = {f(p1, ..., q, ... pn) -> p0}
		for (final STATE st : src) {
			if (!mSourceMap.containsKey(st)) {
				mSourceMap.put(st, new HashSet<>());
			}
			final HashSet<TreeAutomatonRule<LETTER, STATE>> rulesBySource = (HashSet<TreeAutomatonRule<LETTER, STATE>>) mSourceMap.get(st);
			rulesBySource.add(rule);
		}
	}
	
	public void extendAlphabet(final Collection<LETTER> sigma) {
		mAlphabet.addAll(sigma);
	}
	

	public void addLetter(final LETTER letter) {
		mAlphabet.add(letter);
	}

	public void addState(final STATE state) {
		mStates.add(state);
	}
	
	public void addFinalState(final STATE state) {
		mFinalStates.add(state);
		addState(state);
	}
	
	public void addInitialState(final STATE state) {
		mInitalStates.add(state);
		addState(state);
	}
	
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getRulesByLetter(final LETTER letter) {
		return mLettersMap.get(letter);
	}

	public Iterable<TreeAutomatonRule<LETTER, STATE>> getRulesBySource(final STATE src) {
		return mSourceMap.get(src);
	}
	
	@Override
	public Set<LETTER> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return null;
	}

	@Override
	public int size() {
		return mStates.size();
	}

	@Override
	public String sizeInformation() {
		return size() + " nodes";
	}

	@Override
	public Set<STATE> getInitialStates() {
		return mInitalStates;
	}

	@Override
	public Set<STATE> getStates() {
		return mStates;
	}
	
	@Override
	public boolean isFinalState(final STATE state) {
		return mFinalStates.contains(state);
	}

	@Override
	public boolean isInitialState(STATE state) {
		return mInitalStates.contains(state);
	}

	public Iterator<TreeAutomatonRule<LETTER, STATE>> getRulesIterator() {
		
		final Iterator<STATE> qStates = mStates.iterator();
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
		return mRules;
	}

	@Override
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getSuccessors(final List<STATE> states) {
		final Set<TreeAutomatonRule<LETTER, STATE>> successors = new HashSet<>();
		for (final LETTER letter : mParentsMap.get(states).keySet()) {
			for (final TreeAutomatonRule<LETTER, STATE> rule : mParentsMap.get(states).get(letter)) {
				successors.add(rule);
			}
		}
		return successors;
	}
	
	@Override
	public Iterable<STATE> getSuccessors(final List<STATE> states, final LETTER letter) {
		if (!mParentsMap.containsKey(states) || !mParentsMap.get(states).containsKey(letter)) {
			return new HashSet<>();
		}
		final Set<STATE> result = new HashSet<>();
		for (final TreeAutomatonRule<LETTER, STATE> rule : mParentsMap.get(states).get(letter)) {
			result.add(rule.getDest());
		}
		return result;
	}

	@Override
	public Map<LETTER, Iterable<List<STATE>>> getPredecessors(final STATE state) {
		if (!mChildrenMap.containsKey(state)) {
			return new HashMap<>();
		}
		final Map<LETTER, Iterable<List<STATE>>> result = new HashMap<>();
		for (final LETTER letter : mChildrenMap.get(state).keySet()) {
			final Set<List<STATE>> st = new HashSet<>();
			for (final TreeAutomatonRule<LETTER, STATE> rule : mChildrenMap.get(state).get(letter)) {
				st.add(rule.getSource());
			}
			result.put(letter, st);
		}
		return result;
	}

	@Override
	public Iterable<List<STATE>> getPredecessors(final STATE state, final LETTER letter) {
		if (!mChildrenMap.containsKey(state) || !mChildrenMap.get(state).containsKey(letter)) {
			return new ArrayList<>();
		}
		final Set<List<STATE>> result = new HashSet<>();
		for (final TreeAutomatonRule<LETTER, STATE> rule : mChildrenMap.get(state).get(letter)) {
			result.add(rule.getSource());
		}
		return result;
	}
	
	public void complementFinals() {
		final Set<STATE> newFinals = new HashSet<>();
		for (final STATE st : mStates) {
			if (!isFinalState(st)) {
				newFinals.add(st);
			}
		}
		mFinalStates.clear();
		mFinalStates.addAll(newFinals);
	}
	
	public String stateString(STATE state) {
		String res = state.toString();
		if (mInitalStates.contains(state)) {
			res += "_";
		}
		if (isFinalState(state)) {
			res += "*";
		}
		return res;
	}
	
	public String DebugString() {
		String statesString = "";
		for (final STATE state : mStates) {
			statesString += stateString(state) + " ";
		}
		String rulesString = "";
		for (final TreeAutomatonRule<LETTER, STATE> rule : mRules) {
			rulesString += String.format("%s%s ~~> %s\n", rule.getLetter(), rule.getSource(), stateString(rule.getDest()));
		}
		return statesString + "\n" + rulesString;
	}
	
	@Override
	public String toString() {
		
		String alphabet = "";
		for (final LETTER letter : this.mAlphabet) {
			if (!alphabet.isEmpty()) {
				alphabet += " ";
			}
			alphabet += letter.toString();
		}
		
		String states = "";
		for (final STATE state : this.mStates) {
			if (!states.isEmpty()) {
				states += " ";
			}
			states += state.toString();
		}
		
		String initialStates = "";
		for (final STATE state : this.mInitalStates) {
			if (!initialStates.isEmpty()) {
				initialStates += " ";
			}
			initialStates += state.toString();
		}
		
		String finalStates = "";
		for (final STATE state : this.mFinalStates) {
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
