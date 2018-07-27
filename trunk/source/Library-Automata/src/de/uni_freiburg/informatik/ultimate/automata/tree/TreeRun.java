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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISemanticReducerFactory;


/**
 * A run of a tree automaton.
 *
 * (alex:) Effectively this is used for representing any tree with some nodes and some edge labels. (e.g. in HCSsa)
 *
 *
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 *
 * @param <LETTER> Symbols of the automaton
 * @param <STATE> States of the automaton.
 */
public class TreeRun<LETTER extends IRankedLetter, STATE> implements ITreeRun<LETTER, STATE> {

	/*
	 * fields that determine the TreeRun
	 */
	private final STATE mState;
	private final LETTER mLetter;
	private final List<TreeRun<LETTER, STATE>> mChildren;

	/*
	 * helper fields
	 */
	private final Collection<STATE> mAllStates;
	private final Collection<TreeAutomatonRule<LETTER, STATE>> mAllRules;

	/**
	 * Constructs a run that consists of one state, and no transitions.
	 * @param state
	 */
	public TreeRun(final STATE state) {
		this(state, null, new ArrayList<>());
	}

	/**
	 * Constructs a run, by the final state, transition symbol, transition children.
	 * Run := letter(childrenRuns) ~> state
	 * @param state: final state of the computation.
	 * @param letter: the letter taken by the final transition.
	 * @param children: The children runs.
	 */
	public TreeRun(final STATE state, final LETTER letter, final List<TreeRun<LETTER, STATE>> children) {
		this.mState = state;
		this.mLetter = letter;
		this.mChildren = children;

		/*
		 * compute all rules and all states from this and children
		 * TODO: perhaps do this lazy
		 */
		final Set<STATE> allStates = new HashSet<>();
		final Set<TreeAutomatonRule<LETTER, STATE>> allRules = new HashSet<>();
		final List<STATE> childStates = new ArrayList<>();
		for (final TreeRun<LETTER, STATE> child : children) {
			allStates.addAll(child.getStates());
			childStates.add(child.getRoot());
			allRules.addAll(child.getRules());
		}
		if (mLetter != null) {
			allRules.add(new TreeAutomatonRule<LETTER, STATE>(mLetter, childStates, state));
		}
		allStates.add(mState);

		mAllStates = Collections.unmodifiableSet(allStates);
		mAllRules = Collections.unmodifiableSet(allRules);

		assert !mAllStates.stream().anyMatch(Objects::isNull);
	}

	/***
	 * Rebuild the tree run with new states.
	 * <ST> Type of the terminal state.
	 * @param stMap map of the old states to the new states.
	 * @return
	 */

	public <ST> TreeRun<LETTER, ST> reconstruct(final Map<STATE, ST> stMap) {
		final List<TreeRun<LETTER, ST>> child = new ArrayList<>();
		for (final TreeRun<LETTER, STATE> c : mChildren) {
			child.add(c.reconstruct(stMap));
		}

		return new TreeRun<>(stMap.containsKey(mState) ? stMap.get(mState) : null, mLetter, child);
	}

	/***
	 * Rebuild the tree run with new states.
	 * <ST> Type of the terminal state.
	 * @param stMap map of the old states to the new states.
	 * @return
	 */

	public <ST> TreeRun<LETTER, ST> reconstructViaSubtrees(final Map<TreeRun<LETTER, STATE>, ST> stMap) {
		final List<TreeRun<LETTER, ST>> children = new ArrayList<>();
		for (final TreeRun<LETTER, STATE> c : mChildren) {
			children.add(c.reconstructViaSubtrees(stMap));
		}
		if (stMap.get(this) == null) {
			return (TreeRun<LETTER, ST>) this;
		} else {
			return new TreeRun<>(stMap.get(this), mLetter, children);
		}
	}


	public List<TreeRun<LETTER, STATE>> getChildren() {
		return mChildren;
	}

	private Collection<TreeAutomatonRule<LETTER, STATE>> getRules() {
		return mAllRules;
	}
	private Collection<STATE> getStates() {
		return mAllStates;
	}

	@Override
	public <SF extends ISemanticReducerFactory<STATE, LETTER>> InterpolantTreeAutomatonBU<LETTER, STATE> getInterpolantAutomaton(
			final SF factory) {
		final InterpolantTreeAutomatonBU<LETTER, STATE> treeAutomaton = new InterpolantTreeAutomatonBU<>(factory);

		for (final STATE st : getStates()) {
			treeAutomaton.addState(st);
		}
		treeAutomaton.addFinalState(mState);

		for (final TreeAutomatonRule<LETTER, STATE> rule : getRules()) {
			treeAutomaton.addRule(rule);
		}

		return treeAutomaton;
	}

	@Override
	public ITreeAutomatonBU<LETTER, STATE> getAutomaton() {
		final TreeAutomatonBU<LETTER, STATE> treeAutomaton = new TreeAutomatonBU<>();

		for (final STATE st : getStates()) {
			treeAutomaton.addState(st);
		}
		treeAutomaton.addFinalState(mState);

		for (final TreeAutomatonRule<LETTER, STATE> rule : getRules()) {
			treeAutomaton.addRule(rule);
		}

		return treeAutomaton;
	}

	@Override
	public Tree<LETTER> getTree() {
		final List<Tree<LETTER>> treeChildren = new ArrayList<>();
		for (final TreeRun<LETTER, STATE> run : this.mChildren) {
			treeChildren.add(run.getTree());
		}
		return new Tree<>(mLetter, treeChildren);
	}

	@Override
	public STATE getRoot() {
		return mState;
	}

	@Override
	public LETTER getRootSymbol() {
		return mLetter;
	}

	@Override
	public String toString() {
		final StringBuilder res = new StringBuilder();
		for (final TreeRun<LETTER, STATE> st : mChildren) {
			if (res.length() > 0) {
				res.append(", ");
			}
			res.append(st.toString());
		}
		if (res.length() > 0) {
			res.insert(0, "(");
			res.append(")");
		}
		return String.format("%s[%s]%s", mLetter, mState, res);
	}
}
