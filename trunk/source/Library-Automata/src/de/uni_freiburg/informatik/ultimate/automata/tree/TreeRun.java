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
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER> Symbols of the automaton
 * @param <STATE> States of the automaton.
 */
public class TreeRun<LETTER, STATE> implements ITreeRun<LETTER, STATE> {

	private final STATE state;
	private final LETTER letter;
	private final List<TreeRun<LETTER, STATE>> children;
	
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
		this.state = state;
		this.letter = letter;
		this.children = children;
	}
	
	public TreeRun<LETTER, STATE> reconstruct(final Map<STATE, STATE> stMap) {
		List<TreeRun<LETTER, STATE>> child = new ArrayList<>();
		for (final TreeRun<LETTER, STATE> c : children) {
			child.add(c.reconstruct(stMap));
		}
		
		return new TreeRun<LETTER, STATE>(stMap.containsKey(state) ? stMap.get(state) : state, letter, child);
	}
	/*
	public TreeRun(final STATE state, final LETTER letter, final TreeRun<LETTER, STATE>[] children) {
		this.state = state;
		this.letter = letter;
		this.children = toArrayList(children);
	}

	private ArrayList<TreeRun<LETTER, STATE>> toArrayList(final TreeRun<LETTER, STATE>[] t) {
		final ArrayList<TreeRun<LETTER, STATE>> ret = new ArrayList<>();
		
		for (TreeRun<LETTER, STATE> st : t) {
			ret.add(st);
		}
		
		return ret;
	}
	*/
	
	public Collection<TreeRun<LETTER, STATE>> getChildren() {
		return children;
	}
	
	private Collection<TreeAutomatonRule<LETTER, STATE>> getRules() {
		final Set<TreeAutomatonRule<LETTER, STATE>> res = new HashSet<>();
		
		if (!children.isEmpty()) {
			final List<STATE> src = new ArrayList<>();
			for (final TreeRun<LETTER, STATE> run : children) {
				src.add(run.state); // Index States
				res.addAll(run.getRules());
			}
			res.add(new TreeAutomatonRule<LETTER, STATE>(letter, src, state));
		}
		return res;
	}
	private Collection<STATE> getStates() {
		final Set<STATE> res = new HashSet<>();
		res.add(state);
		for (final TreeRun<LETTER, STATE> st : children) {
			res.addAll(st.getStates());
		}
		return res;
	}
	
	private Collection<STATE> getInitialStates() {
		final Set<STATE> res = new HashSet<>();
		if (children.isEmpty()) {
			res.add(state);
		} else {
			for (final TreeRun<LETTER, STATE> st : children) {
				res.addAll(st.getInitialStates());
			}
		}
		return res;
	}
	
	@Override
	public ITreeAutomatonBU<LETTER, STATE> getAutomaton() {
		final TreeAutomatonBU<LETTER, STATE> treeAutomaton = new TreeAutomatonBU<>();
		
		for (final STATE st : getStates()) {
			treeAutomaton.addState(st);
		}
		for (final STATE st : getInitialStates()) {
			treeAutomaton.addInitialState(st);
		}
		treeAutomaton.addFinalState(state);
		
		for (final TreeAutomatonRule<LETTER, STATE> rule : getRules()) {
			treeAutomaton.addRule(rule);
		}
		
		return treeAutomaton;
	}

	@Override
	public Tree<LETTER> getTree() {
		if (children.isEmpty()) {
			return null;
		}
		final List<Tree<LETTER>> treeChildren = new ArrayList<>();
		for (final TreeRun<LETTER, STATE> run : this.children) {
			treeChildren.add(run.getTree());
		}
		return new Tree<>(letter, treeChildren);
	}

	@Override
	public STATE getRoot() {
		return state;
	}
	
	@Override
	public LETTER getRootSymbol() {
		return letter;
	}
	
	@Override
	public String toString() {
		if (children.isEmpty()) {
			return state.toString();
		}
		String res = "";
		for (final TreeRun<LETTER, STATE> st : children) {
			if (!res.isEmpty()) {
				res += ", ";
			}
			res += st.toString();
		}
		if (!res.isEmpty()) {
			res = "(" + res + ")";
		}
		return String.format("%s[%s]%s", letter, state, res);
	}
}
