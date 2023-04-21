package de.uni_freiburg.informatik.ultimate.automata.rabin;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

/**
 * Interface describing minimal operation set of Rabin automata
 *
 * @author Philipp Müller (pm251@venus.uni-freiburg.de)
 *
 * @param <LETTER>
 *            letter
 * @param <STATE>
 *            state
 */
public interface IRabinAutomaton<LETTER, STATE> extends IAutomaton<LETTER, STATE> {

	/**
	 * @return All initial states of the automaton.
	 */
	Iterable<STATE> getInitialStates();

	/**
	 * checks if state is initial
	 *
	 * @param state
	 *            state
	 * @return true iff the state is initial.
	 */
	boolean isInitial(STATE state);

	/**
	 * checks if state is accepting
	 *
	 * @param state
	 *            state
	 * @return true iff the state is accepting.
	 */
	boolean isAccepting(STATE state);

	/**
	 * checks if state is finite
	 *
	 * @param state
	 *            state
	 * @return true iff the state is finite. (Should only be visited finitely often.)
	 */
	boolean isFinite(STATE state);

	/**
	 * All successor transitions for a given state.
	 *
	 * @param state
	 *            state
	 * @return outgoing transitions all possible outgoing transitions for this state
	 */
	Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state);

	/**
	 * Successor transitions for a given state and letter pair.
	 *
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return resulting outgoing transitions for these parameters
	 */
	Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter);

}
