package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates.ReachProp;

public abstract class StateContainer<LETTER, STATE> {

	protected final STATE m_State;
	protected ReachProp m_ReachProp;
	protected CommonEntriesComponent<LETTER,STATE> cec;

	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(m_State.toString());
		sb.append(System.getProperty("line.separator"));
		for (OutgoingInternalTransition<LETTER, STATE> trans : internalSuccessors()) {
			sb.append(trans).append("  ");
		}
		sb.append(System.getProperty("line.separator"));
		for (IncomingInternalTransition<LETTER, STATE> trans : internalPredecessors()) {
			sb.append(trans).append("  ");
		}
		sb.append(System.getProperty("line.separator"));
		for (OutgoingCallTransition<LETTER, STATE> trans : callSuccessors()) {
			sb.append(trans).append("  ");
		}
		sb.append(System.getProperty("line.separator"));
		for (IncomingCallTransition<LETTER, STATE> trans : callPredecessors()) {
			sb.append(trans).append("  ");
		}
		sb.append(System.getProperty("line.separator"));
		for (OutgoingReturnTransition<LETTER, STATE> trans : returnSuccessors()) {
			sb.append(trans).append("  ");
		}
		sb.append(System.getProperty("line.separator"));
		for (IncomingReturnTransition<LETTER, STATE> trans : returnPredecessors()) {
			sb.append(trans).append("  ");
		}
		sb.append(System.getProperty("line.separator"));
		return sb.toString();
	}

	public StateContainer(STATE state, CommonEntriesComponent<LETTER,STATE> cec) {
		m_State = state;
		this.cec = cec;
		m_ReachProp = ReachProp.REACHABLE;
	}

	public ReachProp getReachProp() {
		return m_ReachProp;
	}

	public void setReachProp(ReachProp reachProp) {
		m_ReachProp = reachProp;
	}

	protected CommonEntriesComponent<LETTER,STATE> getCommonEntriesComponent() {
		return cec;
	}

	protected void setCommonEntriesComponent(CommonEntriesComponent<LETTER,STATE> cec) {
		this.cec = cec;
	}

	@Override
	public int hashCode() {
		return m_State.hashCode();
	}

	protected STATE getState() {
		return m_State;
	}

	protected boolean isEntry() {
		for (Entry<LETTER,STATE> entry : this.cec.getEntries()) {
			if (entry.getState().equals(this.getState())) {
				return true;
			}
		}
		return false;
	}

	protected boolean containsInternalTransition(LETTER letter, STATE succ) {
		for (OutgoingInternalTransition<LETTER, STATE> trans : internalSuccessors(letter)) {
			if (succ.equals(trans.getSucc())) {
				return true;
			}
		}
		return false;
	}

	protected boolean containsCallTransition(LETTER letter, STATE succ) {
		for (OutgoingCallTransition<LETTER, STATE> trans : callSuccessors(letter)) {
			if (succ.equals(trans.getSucc())) {
				return true;
			}
		}
		return false;
	}

	protected boolean containsReturnTransition(STATE hier, LETTER letter, STATE succ) {
		for (OutgoingReturnTransition<LETTER, STATE> trans : returnSucccessors(hier, letter)) {
			if (succ.equals(trans.getSucc())) {
				return true;
			}
		}
		return false;
	}
	
	
	public abstract Collection<LETTER> lettersInternal();

	public abstract Collection<LETTER> lettersInternalIncoming();

	public abstract Collection<LETTER> lettersCall();

	public abstract Collection<LETTER> lettersCallIncoming();

	public abstract Collection<LETTER> lettersReturn();

	public abstract Collection<LETTER> lettersReturnIncoming();

	public abstract Collection<LETTER> lettersReturnSummary();

	public abstract Collection<STATE> succInternal(LETTER letter);

	public abstract Collection<STATE> predInternal(LETTER letter);

	public abstract Collection<STATE> succCall(LETTER letter);

	public abstract Collection<STATE> predCall(LETTER letter);

	public abstract Collection<STATE> hierPred(LETTER letter);

	public abstract Collection<STATE> succReturn(STATE hier, LETTER letter);

	public abstract Collection<STATE> predReturnLin(LETTER letter, STATE hier);

	public abstract Collection<STATE> predReturnHier(LETTER letter);

	public abstract Iterable<SummaryReturnTransition<LETTER, STATE>> getSummaryReturnTransitions(
			LETTER letter);

	public abstract Iterable<IncomingReturnTransition<LETTER, STATE>> getIncomingReturnTransitions(
			LETTER letter);

	public abstract Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final LETTER letter);

	public abstract Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors();

	public abstract Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final LETTER letter);

	public abstract Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors();

	public abstract Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE hier, final LETTER letter);

	public abstract Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final LETTER letter);

	public abstract Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors();

	public abstract Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final LETTER letter);

	public abstract Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors();

	public abstract Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final LETTER letter);

	public abstract Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors();

	public abstract Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			final STATE hier, final LETTER letter);

	public abstract Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final LETTER letter);

	public abstract Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			final STATE hier);

	public abstract Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors();
	
	abstract void addInternalOutgoing(OutgoingInternalTransition<LETTER, STATE> internalOutgoing);

	abstract void addInternalIncoming(IncomingInternalTransition<LETTER, STATE> internalIncoming);

	abstract void addCallOutgoing(OutgoingCallTransition<LETTER, STATE> callOutgoing);

	abstract void addCallIncoming(IncomingCallTransition<LETTER, STATE> callIncoming);

	abstract void addReturnOutgoing(OutgoingReturnTransition<LETTER, STATE> returnOutgoing);

	abstract void addReturnIncoming(IncomingReturnTransition<LETTER, STATE> returnIncoming);

	abstract void addReturnTransition(STATE pred, LETTER letter, STATE succ);
}

