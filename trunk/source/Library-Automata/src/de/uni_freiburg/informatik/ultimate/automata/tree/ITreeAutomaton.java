package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;

/**
 * Interface to create a tree automaton
 * 
 * @author grugelt@uni-freiburg.de
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
	 * @return a list of all successor states for given states.
	 */
	public Iterable<OutgoingTreeTransition<LETTER, STATE>> getSuccessors(List<STATE> states);
	
	/**
	 * @return a list of all successors for given states and given letter.
	 */
	public Iterable<STATE> getSuccessors(List<STATE> states, LETTER letter);
}
