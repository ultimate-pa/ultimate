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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A run of a tree automaton.
 * 
 * (alex:) Effectively this is used for representing any tree with some nodes and some edge labels. (e.g. in HCSsa)
 * 
 * 
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 *
 * @param <R> Symbols of the automaton
 * @param <S> States of the automaton.
 */
public class TreeRun<R, S> implements ITreeRun<R, S> {

	private final S state;
	private final R letter;
	private final List<TreeRun<R, S>> children;
	
	/**
	 * Constructs a run that consists of one state, and no transitions.
	 * @param state
	 */
	public TreeRun(final S state) {
		this(state, null, new ArrayList<>());
	}
	
	/**
	 * Constructs a run, by the final state, transition symbol, transition children.
	 * Run := letter(childrenRuns) ~> state
	 * @param state: final state of the computation.
	 * @param letter: the letter taken by the final transition.
	 * @param children: The children runs.
	 */
	public TreeRun(final S state, final R letter, final List<TreeRun<R, S>> children) {
		this.state = state;
		this.letter = letter;
		this.children = children;
	}

	/***
	 * Rebuild the tree run with new states.
	 * <ST> Type of the terminal state.
	 * @param stMap map of the old states to the new states.
	 * @return
	 */
	
	public <ST> TreeRun<R, ST> reconstruct(final Map<S, ST> stMap) {
		List<TreeRun<R, ST>> child = new ArrayList<>();
		for (final TreeRun<R, S> c : children) {
			child.add(c.reconstruct(stMap));
		}
		
		return new TreeRun<>(stMap.containsKey(state) ? stMap.get(state) : null, letter, child);
	}
	
	public Collection<TreeRun<R, S>> getChildren() {
		return children;
	}
	
	private Collection<TreeAutomatonRule<R, S>> getRules() {
		final Set<TreeAutomatonRule<R, S>> res = new HashSet<>();
		
		if (!children.isEmpty()) {
			final List<S> src = new ArrayList<>();
			for (final TreeRun<R, S> run : children) {
				src.add(run.state); // Index States
				res.addAll(run.getRules());
			}
			res.add(new TreeAutomatonRule<R, S>(letter, src, state));
		}
		return res;
	}
	private Collection<S> getStates() {
		final Set<S> res = new HashSet<>();
		res.add(state);
		for (final TreeRun<R, S> st : children) {
			res.addAll(st.getStates());
		}
		return res;
	}
	
	private Collection<S> getInitialStates() {
		final Set<S> res = new HashSet<>();
		if (children.isEmpty()) {
			res.add(state);
		} else {
			for (final TreeRun<R, S> st : children) {
				res.addAll(st.getInitialStates());
			}
		}
		return res;
	}
	
	@Override
	public ITreeAutomatonBU<R, S> getAutomaton() {
		final TreeAutomatonBU<R, S> treeAutomaton = new TreeAutomatonBU<>();
		
		for (final S st : getStates()) {
			treeAutomaton.addState(st);
		}
		for (final S st : getInitialStates()) {
			treeAutomaton.addInitialState(st);
		}
		treeAutomaton.addFinalState(state);
		
		for (final TreeAutomatonRule<R, S> rule : getRules()) {
			treeAutomaton.addRule(rule);
		}
		
		return treeAutomaton;
	}

	@Override
	public Tree<R> getTree() {
		if (children.isEmpty()) {
			return null;
		}
		final List<Tree<R>> treeChildren = new ArrayList<>();
		for (final TreeRun<R, S> run : this.children) {
			treeChildren.add(run.getTree());
		}
		return new Tree<>(letter, treeChildren);
	}

	@Override
	public S getRoot() {
		return state;
	}
	
	@Override
	public R getRootSymbol() {
		return letter;
	}
	
	@Override
	public String toString() {
		if (children.isEmpty()) {
			return state.toString();
		}
		final StringBuilder res = new StringBuilder();
		for (final TreeRun<R, S> st : children) {
			if (res.length() > 0) {
				res.append(", ");
			}
			res.append(st.toString());
		}
		if (res.length() > 0) {
			res.append("(");
			res.append(res);
			res.append(")");
		}
		return String.format("%s[%s]%s", letter, state, res);
	}
}
