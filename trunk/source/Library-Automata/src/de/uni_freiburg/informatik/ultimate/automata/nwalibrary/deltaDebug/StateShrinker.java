package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.deltaDebug;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;

/**
 * Removes states.
 * 
 * This shrinker removes any kind of states.
 * Especially, it does not make an exception to initial states.
 * Transitions are added iff all respective states are still present.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class StateShrinker<STATE, LETTER>
		extends AShrinker<STATE, LETTER, STATE> {
	@Override
	public INestedWordAutomaton<LETTER, STATE> createAutomaton(
			final List<STATE> states) {
		// create fresh automaton
		INestedWordAutomaton<LETTER, STATE> automaton = m_factory.create();
		
		// add the complement of the passed states
		final Set<STATE> oldStates =
				new HashSet<STATE>(m_automaton.getStates());
		oldStates.removeAll(states);
		m_factory.addStates(automaton, oldStates);
		
		// add transitions which still remain
		m_factory.addFilteredTransitions(automaton);
		
		// store automaton temporarily
		m_prevAutomaton = automaton;
		
		return automaton;
	}
	
	@Override
	public List<STATE> extractList() {
		return new ArrayList<STATE>(m_automaton.getStates());
	}
}