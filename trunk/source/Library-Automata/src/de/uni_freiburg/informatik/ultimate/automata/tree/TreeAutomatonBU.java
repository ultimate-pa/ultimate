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
 * @param <R>
 *            is the type of the alphabet.
 * @param <S>
 *            is the type of the states.
 * 
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 */
public class TreeAutomatonBU<R, S> implements ITreeAutomatonBU<R, S> {

	private final Map<List<S>, Map<R, Iterable<TreeAutomatonRule<R, S>>>> mParentsMap;
	private final Map<S, Map<R, Iterable<TreeAutomatonRule<R, S>>>> mChildrenMap;
	private final Map<R, Iterable<TreeAutomatonRule<R, S>>> mLettersMap;
	private final Map<S, Iterable<TreeAutomatonRule<R, S>>> mSourceMap;
	private final Set<TreeAutomatonRule<R, S>> mRules;
	private final Set<R> mAlphabet;
	private final Set<S> mFinalStates;
	private final Set<S> mInitalStates;
	private final Set<S> mStates;

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
	 * 
	 * @param rule
	 */
	public void addRule(final TreeAutomatonRule<R, S> rule) {
		if (mRules.contains(rule)) {
			// If rule already exists, do nothing
			return;
		}
		mRules.add(rule);
		final R letter = rule.getLetter();
		final S dest = rule.getDest();
		final List<S> src = rule.getSource();

		// f(q1,...,qn) -> q
		addLetter(letter);
		addState(dest);
		for (final S state : src) {
			addState(state);
		}
		// children(q)[f] = <q1, ..., qn>
		if (!mChildrenMap.containsKey(dest)) {
			mChildrenMap.put(dest, new HashMap<R, Iterable<TreeAutomatonRule<R, S>>>());
		}
		final Map<R, Iterable<TreeAutomatonRule<R, S>>> childLetter = mChildrenMap.get(dest);
		if (!childLetter.containsKey(letter)) {
			childLetter.put(letter, new HashSet<TreeAutomatonRule<R, S>>());
		}
		final HashSet<TreeAutomatonRule<R, S>> children = (HashSet<TreeAutomatonRule<R, S>>) childLetter.get(letter);
		children.add(rule);

		// parents(q1, ..., qn)[f] = q
		if (!mParentsMap.containsKey(src)) {
			mParentsMap.put(src, new HashMap<R, Iterable<TreeAutomatonRule<R, S>>>());
		}
		final Map<R, Iterable<TreeAutomatonRule<R, S>>> parentLetter = mParentsMap.get(src);
		if (!parentLetter.containsKey(letter)) {
			parentLetter.put(letter, new HashSet<TreeAutomatonRule<R, S>>());
		}
		final Set<TreeAutomatonRule<R, S>> parents = (Set<TreeAutomatonRule<R, S>>) parentLetter.get(letter);
		parents.add(rule);

		// lettersMap[f] = [f(p) -> q]
		if (!mLettersMap.containsKey(letter)) {
			mLettersMap.put(letter, new HashSet<>());
		}
		final HashSet<TreeAutomatonRule<R, S>> rulesByLetter = (HashSet<TreeAutomatonRule<R, S>>) mLettersMap
				.get(letter);
		rulesByLetter.add(rule);

		// sourceRules[q] = < f(p1, ..., q, ... pn) -> p0 >
		for (final S st : src) {
			if (!mSourceMap.containsKey(st)) {
				mSourceMap.put(st, new HashSet<>());
			}
			final HashSet<TreeAutomatonRule<R, S>> rulesBySource = (HashSet<TreeAutomatonRule<R, S>>) mSourceMap
					.get(st);
			rulesBySource.add(rule);
		}
	}

	/***
	 * Extend the alphabet.
	 * 
	 * @param sigma
	 */
	public void extendAlphabet(final Collection<R> sigma) {
		mAlphabet.addAll(sigma);
	}

	/***
	 * Add a letter
	 * 
	 * @param letter
	 */
	public void addLetter(final R letter) {
		mAlphabet.add(letter);
	}

	/***
	 * Add a state
	 * 
	 * @param state
	 */
	public void addState(final S state) {
		mStates.add(state);
	}

	/***
	 * Add Final state
	 * 
	 * @param state
	 */
	public void addFinalState(final S state) {
		mFinalStates.add(state);
		addState(state);
	}

	/***
	 * Add initial state.
	 * 
	 * @param state
	 */
	public void addInitialState(final S state) {
		mInitalStates.add(state);
		addState(state);
	}

	/***
	 * Get rules that use a specific character.
	 * 
	 * @param letter
	 * @return
	 */
	public Iterable<TreeAutomatonRule<R, S>> getRulesByLetter(final R letter) {
		return mLettersMap.get(letter);
	}

	/***
	 * Get rules by source.
	 * 
	 * @param src
	 * @return
	 */
	public Iterable<TreeAutomatonRule<R, S>> getRulesBySource(final S src) {
		return mSourceMap.get(src);
	}

	@Override
	public Set<R> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public IStateFactory<S> getStateFactory() {
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
	public Set<S> getInitialStates() {
		return mInitalStates;
	}

	@Override
	public Set<S> getStates() {
		return mStates;
	}

	@Override
	public boolean isFinalState(final S state) {
		return mFinalStates.contains(state);
	}

	@Override
	public boolean isInitialState(S state) {
		return mInitalStates.contains(state);
	}

	@Override
	public Iterable<TreeAutomatonRule<R, S>> getRules() {
		return mRules;
	}

	@Override
	public Iterable<TreeAutomatonRule<R, S>> getSuccessors(final List<S> states) {
		final Set<TreeAutomatonRule<R, S>> successors = new HashSet<>();
		for (final R letter : mParentsMap.get(states).keySet()) {
			for (final TreeAutomatonRule<R, S> rule : mParentsMap.get(states).get(letter)) {
				successors.add(rule);
			}
		}
		return successors;
	}

	@Override
	public Iterable<S> getSuccessors(final List<S> states, final R letter) {
		if (!mParentsMap.containsKey(states) || !mParentsMap.get(states).containsKey(letter)) {
			return new HashSet<>();
		}
		final Set<S> result = new HashSet<>();
		for (final TreeAutomatonRule<R, S> rule : mParentsMap.get(states).get(letter)) {
			result.add(rule.getDest());
		}
		return result;
	}

	@Override
	public Map<R, Iterable<List<S>>> getPredecessors(final S state) {
		if (!mChildrenMap.containsKey(state)) {
			return new HashMap<>();
		}
		final Map<R, Iterable<List<S>>> result = new HashMap<>();
		for (final R letter : mChildrenMap.get(state).keySet()) {
			final Set<List<S>> st = new HashSet<>();
			for (final TreeAutomatonRule<R, S> rule : mChildrenMap.get(state).get(letter)) {
				st.add(rule.getSource());
			}
			result.put(letter, st);
		}
		return result;
	}

	@Override
	public Iterable<List<S>> getPredecessors(final S state, final R letter) {
		if (!mChildrenMap.containsKey(state) || !mChildrenMap.get(state).containsKey(letter)) {
			return new ArrayList<>();
		}
		final Set<List<S>> result = new HashSet<>();
		for (final TreeAutomatonRule<R, S> rule : mChildrenMap.get(state).get(letter)) {
			result.add(rule.getSource());
		}
		return result;
	}

	/***
	 * Complement the set of final states.
	 */
	public void complementFinals() {
		final Set<S> newFinals = new HashSet<>();
		for (final S st : mStates) {
			if (!isFinalState(st)) {
				newFinals.add(st);
			}
		}
		mFinalStates.clear();
		mFinalStates.addAll(newFinals);
	}

	private String stateString(S state) {
		final StringBuilder res = new StringBuilder(state.toString());
		if (mInitalStates.contains(state)) {
			res.append("_");
		}
		if (isFinalState(state)) {
			res.append("*");
		}
		return res.toString();
	}

	/***
	 * A debug string representation
	 * @return
	 */
	public String DebugString() {
		final StringBuilder statesString = new StringBuilder();
		for (final S state : mStates) {
			statesString.append(stateString(state));
			statesString.append(" ");
		}
		final StringBuilder rulesString = new StringBuilder();
		for (final TreeAutomatonRule<R, S> rule : mRules) {
			rulesString.append(
					String.format("%s%s ~~> %s\n", rule.getLetter(), rule.getSource(), stateString(rule.getDest())));
		}
		return statesString + "\n" + rulesString;
	}

	@Override
	public String toString() {

		final StringBuilder alphabet = new StringBuilder();
		for (final R letter : this.mAlphabet) {
			if (alphabet.length() > 0) {
				alphabet.append(" ");
			}
			alphabet.append(letter);
		}

		final StringBuilder states = new StringBuilder();
		for (final S state : this.mStates) {
			if (states.length() > 0) {
				states.append(" ");
			}
			states.append(state);
		}

		final StringBuilder initialStates = new StringBuilder();
		for (final S state : this.mInitalStates) {
			if (initialStates.length() > 0) {
				initialStates.append(" ");
			}
			initialStates.append(state);
		}

		final StringBuilder finalStates = new StringBuilder();
		for (final S state : this.mFinalStates) {
			if (finalStates.length() > 0) {
				finalStates.append(" ");
			}
			finalStates.append(state);
		}

		final StringBuilder transitionTable = new StringBuilder();
		for (final TreeAutomatonRule<R, S> rule : getRules()) {
			if (transitionTable.length() > 0) {
				transitionTable.append("\n");
			}
			final StringBuilder src = new StringBuilder();
			for (final S st : rule.getSource()) {
				if (src.length() > 0) {
					src.append(" ");
				}
				src.append(st);
			}
			transitionTable.append(String.format("\t\t((%s) %s %s)", src, rule.getLetter(), rule.getDest()));
		}
		return String.format(
				"TreeAutomaton %s = {\n\talphabet = {%s},\n\tstates = {%s},\n\tinitialStates = {%s},\n\tfinalStates = {%s},\n\ttransitionTable = {\n%s\n\t}\n}",
				"ta" + hashCode() % 1000000, alphabet, states, initialStates, finalStates, transitionTable);

	}
}
