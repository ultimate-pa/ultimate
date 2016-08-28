package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;

/**
 * Interface to create a tree automaton
 * @author mostafa.amin93@gmail.com, grugelt@uni-freiburg.de
 */

public interface ITreeAutomaton<LETTER, STATE> extends IAutomaton<LETTER, STATE> {

	
	/**
	 * @return a set of all initial states in the automaton.
	 */
	public Set<STATE> getInitialStates();
	
	/**
	 * @return true, if given state is final.
	 */
	public boolean isFinalState(STATE state);

	/**
	 * @return true, if given state is initial.
	 */
	public boolean isInitialState(STATE state);
	
	/**
	 * @return a list of all successor states for given states.
	 */
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getSuccessors(List<STATE> states);
	
	/**
	 * @return a list of all successors for given states and given letter.
	 */
	public Iterable<STATE> getSuccessors(List<STATE> states, LETTER letter);
	
	/**
	 * @return a map that denotes all the lists of rules that goes to given state.
	 */
	public Map<LETTER, Iterable<List<STATE>>> getPredecessors(STATE state);
	
	/**
	 * @return Given a letter and a state, get all rules that goes to the given state
	 * using the given letter.
	 */
	public Iterable<List<STATE>> getPredecessors(STATE state, LETTER letter);
	
	/**
	 * 
	 * @return Get the rules of the automaton.
	 */
	public Iterable<TreeAutomatonRule<LETTER, STATE>> getRules();
}
