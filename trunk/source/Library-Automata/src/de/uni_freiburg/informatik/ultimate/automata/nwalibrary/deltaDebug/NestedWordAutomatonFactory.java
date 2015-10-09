package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.deltaDebug;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * Factory for {@link NestedWordAutomaton} objects.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class NestedWordAutomatonFactory<LETTER, STATE>
		extends AAutomatonFactory<LETTER, STATE> {
	final IUltimateServiceProvider m_services;
	
	public NestedWordAutomatonFactory(
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final IUltimateServiceProvider services) {
		super(stateFactory, automaton);
		this.m_services = services;
	}
	
	/**
	 * @param automaton automaton interface
	 * @return cast automaton
	 */
	private NestedWordAutomaton<LETTER, STATE> getNWA(
			final INestedWordAutomaton<LETTER, STATE> automaton) {
		return ((NestedWordAutomaton<LETTER, STATE>) automaton);
	}
	
	@Override
	protected INestedWordAutomaton<LETTER, STATE> createWithAlphabets(
			Set<LETTER> internalAlphabet, Set<LETTER> callAlphabet,
			Set<LETTER> returnAlphabet) {
		return new NestedWordAutomaton<LETTER, STATE>(m_services,
				internalAlphabet, callAlphabet, returnAlphabet, m_stateFactory);
	}
	
	@Override
	public void addState(final INestedWordAutomaton<LETTER, STATE> automaton,
			final STATE state) {
		getNWA(automaton).addState(m_automaton.isInitial(state),
				m_automaton.isFinal(state), state);
	}
	
	@Override
	public void addInternalTransition(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final STATE pred, final LETTER letter, final STATE succ) {
		getNWA(automaton).addInternalTransition(pred, letter, succ);
	}
	
	@Override
	public void addCallTransition(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final STATE pred, final LETTER letter, final STATE succ) {
		getNWA(automaton).addCallTransition(pred, letter, succ);
	}
	
	@Override
	public void addReturnTransition(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final STATE pred, final STATE hier, final LETTER letter,
			final STATE succ) {
		getNWA(automaton).addReturnTransition(pred, hier, letter, succ);
	}
}