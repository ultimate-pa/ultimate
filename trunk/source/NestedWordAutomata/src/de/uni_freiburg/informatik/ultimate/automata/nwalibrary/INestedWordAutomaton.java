package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.Set;

public interface INestedWordAutomaton<LETTER, STATE> extends INestedWordAutomatonSimple<LETTER, STATE> {

	public abstract Collection<STATE> getStates();

	public abstract Collection<STATE> getInitialStates();

	public abstract Set<LETTER> lettersInternalIncoming(STATE state);

	public abstract Set<LETTER> lettersCallIncoming(STATE state);

	public abstract Set<LETTER> lettersReturnIncoming(STATE state);

	public abstract Set<LETTER> lettersReturnSummary(STATE state);
	
	/**
	 * @return All states hier such that state has an outgoing 
	 * return transition (state, hier, letter, succ)
	 */
	public abstract Iterable<STATE> hierPred(STATE state, LETTER letter);

	public abstract Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			final LETTER letter, final STATE hier);
	
	public abstract Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			final STATE hier);

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