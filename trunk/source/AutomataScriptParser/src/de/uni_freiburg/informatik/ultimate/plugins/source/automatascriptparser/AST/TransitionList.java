/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * Is used to hold transitions for nestedword automata (internal-, call-, and
 * return-transitions) and for Petri nets.
 * 
 * 
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class TransitionList extends AtsASTNode {
	
	public class Pair<L, R> {
		public final L left;
		public final R right;
		
		public Pair(L left, R right) {
			this.left = left;
			this.right = right;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 7;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + ((left == null) ? 0 : left.hashCode());
			result = prime * result + ((right == null) ? 0 : right.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			@SuppressWarnings("unchecked")
			Pair<L, R> other = (Pair<L, R>) obj;
			if (!getOuterType().equals(other.getOuterType()))
				return false;
			if (left == null) {
				if (other.left != null)
					return false;
			} else if (!left.equals(other.left))
				return false;
			if (right == null) {
				if (other.right != null)
					return false;
			} else if (!right.equals(other.right))
				return false;
			return true;
		}

		private TransitionList getOuterType() {
			return TransitionList.this;
		}
		
		
	}

	/**
	 * 
	 */
	private static final long serialVersionUID = 4468320445354864058L;
	private Map<Pair<String, String> , Set<String>> m_Transitions;
	private Map<Pair<String, String>, Pair<String, Set<String>>> m_ReturnTransitions;
	private List<PetriNetTransition> m_netTransitions;
	
	
	public TransitionList() {
		m_Transitions = new HashMap<Pair<String,String>, Set<String>>();
		m_ReturnTransitions = new HashMap<Pair<String, String>, Pair<String, Set<String>>>();
		m_netTransitions = new ArrayList<PetriNetTransition>();
	}
	
	
	/**
	 * Method to add an internal or call transition for nested word automaton.
	 * @param fromState
	 * @param label
	 * @param toState
	 */
	public void addTransition(String fromState, String label, String toState) {
		Pair<String, String> stateSymbolPair = new Pair<String, String>(fromState, label);
		if (m_Transitions.containsKey(stateSymbolPair)) {
			Set<String> succs = m_Transitions.get(stateSymbolPair);
			succs.add(toState);
			m_Transitions.put(stateSymbolPair, succs);
		} else {
			Set<String> succs = new HashSet<String>();
			succs.add(toState);
			m_Transitions.put(stateSymbolPair, succs);
		}
	}
	
	/**
	 * Method to add a return transition for a nested word automaton.
	 * @param fromState
	 * @param returnState
	 * @param label
	 * @param toState
	 */
	public void addTransition(String fromState, String returnState, String label, String toState) {
		Pair<String, String> predHierPair = new Pair<String, String>(fromState, returnState);
		if (m_ReturnTransitions.containsKey(predHierPair)) {
			Pair<String, Set<String>> letter2succs = m_ReturnTransitions.get(predHierPair);
			letter2succs.right.add(toState);
			m_ReturnTransitions.put(predHierPair, letter2succs);
		} else {
			Set<String> succs = new HashSet<String>();
			succs.add(toState);
			Pair<String, Set<String>> letter2succs = new Pair<String, Set<String>>(label, succs);
			m_ReturnTransitions.put(predHierPair, letter2succs);
		}
		
	}
	
	public void addTransition(IdentifierList idList) {
		List<String> ids = idList.getIdentifierList();
		if (ids.size() == 3) {
			addTransition(ids.get(0), ids.get(1), ids.get(2));
		} else if (ids.size() == 4) {
			addTransition(ids.get(0), ids.get(1), ids.get(2), ids.get(3));
		}
	}

	public Map<Pair<String, String>, Set<String>> getTransitions() {
		return m_Transitions;
	}
	
	public Map<Pair<String, String>, Pair<String, Set<String>>> getReturnTransitions() {
		return m_ReturnTransitions;
	}
	
	/**
	 * Method to add a transition for Petri nets.
	 * @param nt the transition of a Petri net
	 */
	public void addNetTransition(PetriNetTransition nt) {
		m_netTransitions.add(nt);
	}

	public List<PetriNetTransition> getNetTransitions() {
		return m_netTransitions;
	}

	
}
