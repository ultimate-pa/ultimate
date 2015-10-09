package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.deltaDebug;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;

/**
 * Factory for {@link INestedWordAutomaton} objects.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public abstract class AAutomatonFactory<LETTER, STATE> {
	final StateFactory<STATE> m_stateFactory;
	final INestedWordAutomaton<LETTER, STATE> m_automaton;
	
	public AAutomatonFactory(final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> automaton) {
		this.m_stateFactory = stateFactory;
		this.m_automaton = automaton;
	}
	
	/**
	 * @return new {@link INestedWordAutomaton} object
	 */
	public INestedWordAutomaton<LETTER, STATE> create() {
		return create(null, null, null);
	}
	
	/**
	 * @param internalAlphabet internal alphabet, null uses original one
	 * @param callAlphabet call alphabet, null uses original one
	 * @param returnAlphabet return alphabet, null uses original one
	 * @return new {@link INestedWordAutomaton} object with specified alphabets
	 */
	public INestedWordAutomaton<LETTER, STATE> create(
			Set<LETTER> internalAlphabet, Set<LETTER> callAlphabet,
			Set<LETTER> returnAlphabet) {
		if (internalAlphabet == null) {
			internalAlphabet = m_automaton.getAlphabet();
		}
		if (callAlphabet == null) {
			callAlphabet = m_automaton.getCallAlphabet();
		}
		if (returnAlphabet == null) {
			returnAlphabet = m_automaton.getReturnAlphabet();
		}
		return createWithAlphabets(
				internalAlphabet, callAlphabet, returnAlphabet);
	}
	
	/**
	 * @param internalAlphabet internal alphabet
	 * @param callAlphabet call alphabet
	 * @param returnAlphabet return alphabet
	 * @return new {@link INestedWordAutomaton} object with specified alphabets
	 */
	protected abstract INestedWordAutomaton<LETTER, STATE> createWithAlphabets(
			final Set<LETTER> internalAlphabet, final Set<LETTER> callAlphabet,
			final Set<LETTER> returnAlphabet);
	
	/**
	 * @param automaton automaton
	 * @param state new state to add
	 */
	public abstract void addState(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final STATE state);
	
	/**
	 * @param automaton automaton
	 * @param pred predecessor state
	 * @param letter letter
	 * @param succ successor state
	 */
	public abstract void addInternalTransition(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final STATE pred, final LETTER letter, final STATE succ);
	
	/**
	 * @param automaton automaton
	 * @param pred predecessor state
	 * @param letter letter
	 * @param succ successor state
	 */
	public abstract void addCallTransition(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final STATE pred, final LETTER letter, final STATE succ);
	
	/**
	 * @param automaton automaton
	 * @param pred linear predecessor state
	 * @param hier hierarchical predecessor state
	 * @param letter letter
	 * @param succ successor state
	 */
	public abstract void addReturnTransition(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final STATE pred, final STATE hier, final LETTER letter,
			final STATE succ);
	
	/**
	 * @param automaton automaton
	 * @param states new states to add
	 */
	public void addStates(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final Collection<STATE> states) {
		for (final STATE state : states) {
			addState(automaton, state);
		}
	}
	
	/**
	 * Adds original transitions filtered by current states.
	 * 
	 * @param automaton automaton
	 */
	public void addFilteredTransitions(
			final INestedWordAutomaton<LETTER, STATE> automaton) {
		final Set<STATE> remainingStates = automaton.getStates();
		for (final STATE state : remainingStates) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans :
					m_automaton.internalSuccessors(state)) {
				final STATE succ = trans.getSucc();
				if (remainingStates.contains(succ)) {
					addInternalTransition(
							automaton, state, trans.getLetter(), succ);
				}
			}
			for (final OutgoingCallTransition<LETTER, STATE> trans :
					m_automaton.callSuccessors(state)) {
				final STATE succ = trans.getSucc();
				if (remainingStates.contains(succ)) {
					addCallTransition(
							automaton, state, trans.getLetter(), succ);
				}
			}
			for (final OutgoingReturnTransition<LETTER, STATE> trans :
					m_automaton.returnSuccessors(state)) {
				final STATE succ = trans.getSucc();
				final STATE hier = trans.getHierPred();
				if ((remainingStates.contains(succ)) &&
						(remainingStates.contains(hier))) {
					addReturnTransition(
							automaton, state, hier, trans.getLetter(), succ);
				}
			}
		}
	}
	
	@Override
	public String toString() {
		return this.getClass().getSimpleName();
	}
}