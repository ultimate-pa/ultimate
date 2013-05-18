package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;

public interface IOutTransitionNwa<LETTER, STATE> extends IAutomaton<LETTER, STATE> {
	
	public abstract Collection<LETTER> getInternalAlphabet();

	public abstract Collection<LETTER> getCallAlphabet();

	public abstract Collection<LETTER> getReturnAlphabet();
	
	public abstract STATE getEmptyStackState();

	public abstract StateFactory<STATE> getStateFactory();
	
	public abstract Iterable<STATE> getInitialStates();
	
	public abstract boolean isInitial(STATE state);

	public abstract boolean isFinal(STATE state);

	public abstract Collection<LETTER> lettersInternal(STATE state);

	public abstract Collection<LETTER> lettersCall(STATE state);

	public abstract Collection<LETTER> lettersReturn(STATE state);

	public abstract Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state, final LETTER letter);

	public abstract Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state);

	public abstract Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state, final LETTER letter);

	public abstract Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state);
	
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			final STATE state, final STATE hier, final LETTER letter);
	
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier);
}
