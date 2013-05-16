package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

public interface INWA<LETTER, STATE> {

	public abstract Collection<LETTER> getInternalAlphabet();

	public abstract Collection<LETTER> getCallAlphabet();

	public abstract Collection<LETTER> getReturnAlphabet();

	public abstract Collection<STATE> getStates();

	public abstract STATE getEmptyStackState();

	public abstract StateFactory<STATE> getStateFactory();

	public abstract int size();

	public abstract Collection<LETTER> getAlphabet();

	public abstract Collection<STATE> getInitialStates();

	public abstract boolean isInitial(STATE state);

	public abstract boolean isFinal(STATE state);

	public abstract Collection<LETTER> lettersInternal(STATE state);

	public abstract Collection<LETTER> lettersInternalIncoming(STATE state);

	public abstract Collection<LETTER> lettersCall(STATE state);

	public abstract Collection<LETTER> lettersCallIncoming(STATE state);

	public abstract Collection<LETTER> lettersReturn(STATE state);

	public abstract Collection<LETTER> lettersReturnIncoming(STATE state);

	public abstract Collection<LETTER> lettersReturnSummary(STATE state);

	public abstract Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			LETTER letter, STATE hier);

	public abstract Iterable<IncomingReturnTransition<LETTER, STATE>> getIncomingReturnTransitions(
			LETTER letter, STATE succ);

	public abstract Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final LETTER letter, final STATE succ);

	public abstract Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final STATE succ);

	public abstract Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final LETTER letter, final STATE succ);

	public abstract Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final STATE succ);

	public abstract Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state, final LETTER letter);

	public abstract Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state);

	public abstract Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state, final LETTER letter);

	public abstract Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state);
	
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE hier, final LETTER letter, final STATE succ);
	
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final LETTER letter, final STATE succ);
	
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ);
	
	
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			final STATE state, final STATE hier, final LETTER letter);
	
	
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final LETTER letter);
	
	
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state);
	
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier);

	public abstract String sizeInformation();



}