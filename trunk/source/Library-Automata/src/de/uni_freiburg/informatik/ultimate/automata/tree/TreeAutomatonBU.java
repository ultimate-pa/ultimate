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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * A Bottom-up TreeAutomaton. The rules have the form f(q1,...,qn) ~> q
 *
 *
 * @param <LETTER>
 *            is the type of the alphabet.
 * @param <STATE>
 *            is the type of the states.
 *
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public class TreeAutomatonBU<LETTER extends IRankedLetter, STATE> implements ITreeAutomatonBU<LETTER, STATE> {

	private final Set<LETTER> mAlphabet;
	private final Map<STATE, Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>>> mChildrenMap;
	private final Set<STATE> mFinalStates;
	private final Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> mLettersMap;
	private final Map<List<STATE>, Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>>> mParentsMap;
	private final Set<TreeAutomatonRule<LETTER, STATE>> mRules;
	private final Map<STATE, Collection<TreeAutomatonRule<LETTER, STATE>>> mSourceMap;
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
	}

	/***
	 * Add Final state
	 *
	 * @param state
	 */
	public void addFinalState(final STATE state) {
		mFinalStates.add(state);
		addState(state);
	}

	/***
	 * Add a letter
	 *
	 * @param letter
	 */
	public void addLetter(final LETTER letter) {
		mAlphabet.add(letter);
	}

	/**
	 * Add a rule to the automaton.
	 *
	 * @param rule
	 */
	@Override
	public void addRule(final TreeAutomatonRule<LETTER, STATE> rule) {
		if (mRules.contains(rule)) {
			// If rule already exists, do nothing
			return;
		}
		mRules.add(rule);
		final LETTER letter = rule.getLetter();
		final STATE dest = rule.getDest();
		final List<STATE> src = rule.getSource();

		// f(q1,...,qn) -> q
		assert letter.getRank() == rule.getSource().size();
		if (letter.getRank() != rule.getSource().size()) {
			System.err.println(letter + " " + rule);
		}
		addLetter(letter);
		addState(dest);
		for (final STATE state : src) {
			addState(state);
		}
		// children(q)[f] = <q1, ..., qn>
		if (!mChildrenMap.containsKey(dest)) {
			mChildrenMap.put(dest, new HashMap<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>>());
		}
		final Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> childLetter = mChildrenMap.get(dest);
		if (!childLetter.containsKey(letter)) {
			childLetter.put(letter, new HashSet<TreeAutomatonRule<LETTER, STATE>>());
		}
		final HashSet<TreeAutomatonRule<LETTER, STATE>> children = (HashSet<TreeAutomatonRule<LETTER, STATE>>) childLetter
				.get(letter);
		children.add(rule);

		// parents(q1, ..., qn)[f] = q
		if (!mParentsMap.containsKey(src)) {
			mParentsMap.put(src, new HashMap<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>>());
		}
		final Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> parentLetter = mParentsMap.get(src);
		if (!parentLetter.containsKey(letter)) {
			parentLetter.put(letter, new HashSet<TreeAutomatonRule<LETTER, STATE>>());
		}
		final Set<TreeAutomatonRule<LETTER, STATE>> parents = (Set<TreeAutomatonRule<LETTER, STATE>>) parentLetter
				.get(letter);
		parents.add(rule);

		// lettersMap[f] = [f(p) -> q]
		if (!mLettersMap.containsKey(letter)) {
			mLettersMap.put(letter, new HashSet<>());
		}
		final HashSet<TreeAutomatonRule<LETTER, STATE>> rulesByLetter = (HashSet<TreeAutomatonRule<LETTER, STATE>>) mLettersMap
				.get(letter);
		rulesByLetter.add(rule);

		// sourceRules[q] = < f(p1, ..., q, ... pn) -> p0 >
		for (final STATE st : src) {
			if (!mSourceMap.containsKey(st)) {
				mSourceMap.put(st, new HashSet<>());
			}
			final HashSet<TreeAutomatonRule<LETTER, STATE>> rulesBySource = (HashSet<TreeAutomatonRule<LETTER, STATE>>) mSourceMap
					.get(st);
			rulesBySource.add(rule);
		}
	}

	/***
	 * Add a state
	 *
	 * @param state
	 */
	public void addState(final STATE state) {
		mStates.add(state);
	}

	/***
	 * Complement the set of final states.
	 */
	@Override
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

	/***
	 * A debug string representation
	 *
	 * @return
	 */
	public String DebugString() {
		final StringBuilder statesString = new StringBuilder();
		for (final STATE state : mStates) {
			statesString.append(stateString(state));
			statesString.append(" ");
		}
		final StringBuilder rulesString = new StringBuilder();
		for (final TreeAutomatonRule<LETTER, STATE> rule : mRules) {
			rulesString.append(
					String.format("%s%s ~~> %s\n", rule.getLetter(), rule.getSource(), stateString(rule.getDest())));
		}
		return statesString + "\n" + rulesString;
	}

	/***
	 * Extend the alphabet.
	 *
	 * @param sigma
	 */
	public void extendAlphabet(final Collection<LETTER> sigma) {
		mAlphabet.addAll(sigma);
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mAlphabet;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU#
	 * getAmountOfRules()
	 */
	@Override
	public int getAmountOfRules() {
		return this.mRules.size();
	}

	public Set<STATE> getFinalStates() {
		return mFinalStates;
	}

	//@Override
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

	//@Override
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

	public Iterable<TreeAutomatonRule<LETTER, STATE>> getRules() {
		return mRules;
	}

	/***
	 * Get rules that use a specific character.
	 *
	 * @param letter
	 * @return
	 */

	@Override
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getSuccessors(final LETTER letter) {
		final Set<TreeAutomatonRule<LETTER, STATE>> res = new HashSet<>();
		for (final List<STATE> src : getSourceCombinations()) {
			for (final STATE dest : getSuccessors(src, letter)) {
				res.add(new TreeAutomatonRule<LETTER, STATE>(letter, src, dest));
			}
		}
		return res;
		//return mLettersMap.get(letter);
	}


	/***
	 * Get rules by source.
	 *
	 * @param src
	 * @return
	 */
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getRulesBySource(final STATE src) {
		return mSourceMap.get(src);
	}

	@Override
	public Set<STATE> getStates() {
		return mStates;
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
	public boolean isFinalState(final STATE state) {
		return mFinalStates.contains(state);
	}

	public <ST> TreeAutomatonBU<LETTER, ST> reconstruct(final Map<STATE, ST> mp) {
		final TreeAutomatonBU<LETTER, ST> res = new TreeAutomatonBU<>();
		res.extendAlphabet(mAlphabet);
		for (final STATE s : mStates) {
			res.addState(mp.get(s));
			if (isFinalState(s)) {
				res.addFinalState(mp.get(s));
			}
		}
		for (final TreeAutomatonRule<LETTER, STATE> rule : mRules) {
			final List<ST> src = new ArrayList<>();
			for (final STATE s : rule.getSource()) {
				src.add(mp.get(s));
			}
			final ST dest = mp.get(rule.getDest());
			res.addRule(new TreeAutomatonRule<LETTER, ST>(rule.getLetter(), src, dest));
		}
		return res;
	}

	/***
	 * Remove a given state from all the rules
	 *
	 * @param st
	 */
	public void removeState(final STATE st) {
		final Set<TreeAutomatonRule<LETTER, STATE>> badRules = new HashSet<>();
		for (final TreeAutomatonRule<LETTER, STATE> rule : mRules) {
			if (ruleContains(rule, st)) {
				badRules.add(rule);
			}
		}
		for (final Entry<List<STATE>, Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>>> e : mParentsMap
				.entrySet()) {
			for (final Entry<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> e2 : e.getValue().entrySet()) {
				e2.getValue().removeAll(badRules);
			}
		}
		for (final Entry<STATE, Map<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>>> e : mChildrenMap
				.entrySet()) {
			for (final Entry<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> e2 : e.getValue().entrySet()) {
				e2.getValue().removeAll(badRules);
			}
		}
		for (final Entry<LETTER, Collection<TreeAutomatonRule<LETTER, STATE>>> e : mLettersMap.entrySet()) {
			e.getValue().removeAll(badRules);
		}
		for (final Entry<STATE, Collection<TreeAutomatonRule<LETTER, STATE>>> e : mSourceMap.entrySet()) {
			e.getValue().removeAll(badRules);
		}
		mRules.removeAll(badRules);
		mStates.remove(st);
		mFinalStates.remove(st);
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
	public String toString() {

		final StringBuilder alphabet = new StringBuilder();
		for (final LETTER letter : this.mAlphabet) {
			if (alphabet.length() > 0) {
				alphabet.append(" ");
			}
			alphabet.append('"');
			alphabet.append(letter);
			alphabet.append('"');
		}

		final StringBuilder states = new StringBuilder();
		for (final STATE state : this.mStates) {
			if (states.length() > 0) {
				states.append(" ");
			}
			states.append('"');
			states.append(state);
			states.append('"');
		}

		final StringBuilder finalStates = new StringBuilder();
		for (final STATE state : this.mFinalStates) {
			if (finalStates.length() > 0) {
				finalStates.append(" ");
			}
			finalStates.append('"');
			finalStates.append(state);
			finalStates.append('"');
		}

		final StringBuilder transitionTable = new StringBuilder();

		for (final TreeAutomatonRule<LETTER, STATE> rule : getRules()) {
			if (transitionTable.length() > 0) {
				transitionTable.append("\n");
			}
			final StringBuilder src = new StringBuilder();
			for (final STATE st : rule.getSource()) {
				if (src.length() > 0) {
					src.append(" ");
				}
				src.append('"');
				src.append(st);
				src.append('"');
			}
			final StringBuilder dest = new StringBuilder();
			dest.append('"');
			dest.append(rule.getDest());
			dest.append('"');

			final StringBuilder letter = new StringBuilder();
			letter.append('"');
			letter.append(rule.getLetter());
			letter.append('"');
			transitionTable.append(String.format("\t\t((%s) %s %s)", src, letter, dest));
		}
		return String.format(
				// "TreeAutomaton %s = " +
				"TreeAutomaton(\n" + "\talphabet = {%s},\n" + "\tstates = {%s},\n" + "\tfinalStates = {%s},\n"
						+ "\ttransitionTable = {\n%s\n\t}\n)",
				// "ta" + hashCode() % 1000000,
				alphabet, states, finalStates, transitionTable);
	}

	private boolean ruleContains(final TreeAutomatonRule<LETTER, STATE> rule, final STATE st) {
		if (rule.getDest().equals(st)) {
			return true;
		}
		for (final STATE state : rule.getSource()) {
			if (state.equals(st)) {
				return true;
			}
		}

		return false;
	}

	private String stateString(final STATE state) {
		final StringBuilder res = new StringBuilder(state.toString());
		res.append('"');
		if (isFinalState(state)) {
			res.append("*");
		}
		res.append('"');
		return res.toString();
	}

	@Override
	public IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<List<STATE>> getSourceCombinations() {
		return mParentsMap.keySet();
	}
}
