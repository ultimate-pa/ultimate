package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class TreeRun<LETTER, STATE> implements ITreeRun<LETTER, STATE> {

	private STATE state;
	private LETTER letter;
	private List<TreeRun<LETTER, STATE>> children;
	
	public TreeRun(STATE state) {
		this.state = state;
		children = new ArrayList<>();
	}
	public TreeRun(STATE state, LETTER letter, List<TreeRun<LETTER, STATE>> children) {
		this.state = state;
		this.letter = letter;
		this.children = children;
	}
	
	public Collection<TreeRun<LETTER, STATE>> getChildren() {
		return children;
	}
	
	private Collection<TreeAutomatonRule<LETTER, STATE>> getRules() {
		Set<TreeAutomatonRule<LETTER, STATE>> res = new HashSet<TreeAutomatonRule<LETTER, STATE>>();
		
		if (!children.isEmpty()) {
			List<STATE> src = new ArrayList<>();
			for (TreeRun<LETTER, STATE> run : children) {
				src.add(run.state); // Index States
				res.addAll(run.getRules());
			}
			res.add(new TreeAutomatonRule<LETTER, STATE>(letter, src, state));
		}
		return res;
	}
	private Collection<STATE> getStates() {
		Set<STATE> res = new HashSet<STATE>();
		res.add(state);
		for (TreeRun<LETTER, STATE> st : children) {
			res.addAll(st.getStates());
		}
		return res;
	}
	
	private Collection<STATE> getInitialStates() {
		Set<STATE> res = new HashSet<STATE>();
		if (children.isEmpty()) {
			res.add(state);
		} else {
			for (TreeRun<LETTER, STATE> st : children) {
				res.addAll(st.getInitialStates());
			}
		}
		return res;
	}
	
	@Override
	public ITreeAutomaton<LETTER, STATE> getAutomaton() {
		TreeAutomatonBU<LETTER, STATE> treeAutomaton = new TreeAutomatonBU<>();
		
		for (STATE state : getStates()) {
			treeAutomaton.addState(state);
		}
		for (STATE state : getInitialStates()) {
			treeAutomaton.addInitialState(state);
		}
		treeAutomaton.addFinalState(state);
		
		for (TreeAutomatonRule<LETTER, STATE> rule : getRules()) {
			treeAutomaton.addRule(rule);
		}
		
		return treeAutomaton;
	}

	@Override
	public Tree<LETTER> getTree() {
		if (children.isEmpty()) {
			return null;
		}
		List<Tree<LETTER>> children = new ArrayList<>();
		for (TreeRun<LETTER, STATE> run : this.children) {
			children.add(run.getTree());
		}
		return new Tree<LETTER>(letter, children);
	}

	@Override
	public STATE getRoot() {
		return state;
	}
	
	public String toString() {
		if (children.isEmpty())
			return "";
		String res = "";
		for (TreeRun<LETTER, STATE> st : children) {
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
