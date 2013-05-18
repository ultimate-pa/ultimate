package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;

public interface INestedWordAutomaton<LETTER, STATE> extends INestedWordAutomatonSimple<LETTER, STATE> {

	public abstract Collection<STATE> getStates();

	public abstract Collection<STATE> getInitialStates();

	public abstract Collection<LETTER> lettersInternalIncoming(STATE state);

	public abstract Collection<LETTER> lettersCallIncoming(STATE state);

	public abstract Collection<LETTER> lettersReturnIncoming(STATE state);

	public abstract Collection<LETTER> lettersReturnSummary(STATE state);

	public abstract Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			final LETTER letter, final STATE hier);

	public abstract Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final STATE succ);
	
	public abstract Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final LETTER letter, final STATE succ);

	public abstract Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final LETTER letter, final STATE succ);

	public abstract Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final STATE succ);

	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE hier, final LETTER letter, final STATE succ);
	
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final LETTER letter, final STATE succ);
	
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ);
	
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final LETTER letter);
	
	
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state);
	
}