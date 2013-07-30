package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates.ReachProp;

public abstract class StateContainer<LETTER, STATE> {
	
	enum DownStateProp {
		REACH_FINAL_ONCE(1),
		REACH_FINAL_INFTY(2),
		REACHABLE_FROM_FINAL_WITHOUT_CALL(4);
		private final int bitcode;
		
		DownStateProp(int bitcode) {
			this.bitcode = bitcode;
		}
		
		public int getBitCode() {
			return bitcode;
		}
	}
	

	protected final STATE m_State;
	protected final int m_SerialNumber;
	protected ReachProp m_ReachProp;
	protected final Map<STATE, Integer> m_DownStates;
	protected Set<STATE> m_UnpropagatedDownStates;
	protected final boolean m_CanHaveOutgoingReturn;

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
		sb.append(m_DownStates.toString());
		sb.append(System.getProperty("line.separator"));
		return sb.toString();
	}

	public StateContainer(STATE state, int serialNumber, 
			HashMap<STATE, Integer> downStates, boolean canHaveOutgoingReturn) {
		m_State = state;
		m_SerialNumber = serialNumber;
		m_DownStates = downStates;
		m_ReachProp = ReachProp.REACHABLE;
		m_CanHaveOutgoingReturn = canHaveOutgoingReturn;
	}
	
	public int getSerialNumber() {
		return m_SerialNumber;
	}

	public ReachProp getReachProp() {
		return m_ReachProp;
	}

	public void setReachProp(ReachProp reachProp) {
		m_ReachProp = reachProp;
	}

	protected  Map<STATE, Integer> getDownStates() {
		return m_DownStates;
	}

	@Override
	public int hashCode() {
		return m_State.hashCode();
	}

	protected STATE getState() {
		return m_State;
	}
	
	/**
	 *  Add down state. Without any properties set. Returns true iff this down
	 *  state was not already there.
	 *  If the down state was already there it may not have had any 
	 *  DownStateProps
	 */
	boolean addReachableDownState(STATE down) {
		assert !m_DownStates.containsKey(down) || m_DownStates.get(down) == 0;
		Integer oldValue = m_DownStates.put(down, 0);
		if (oldValue == null) {
			if (m_UnpropagatedDownStates == null) {
				m_UnpropagatedDownStates = new HashSet<STATE>();
			}
			m_UnpropagatedDownStates.add(down);
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Set DownStateProp prop for down state. Returns true iff this property was
	 * already set.
	 */
	boolean setDownProp(STATE down, DownStateProp prop) {
		int currentProps = m_DownStates.get(down);
		if ((currentProps & prop.getBitCode()) == 0) {
			// property not yet set
			int newProps = currentProps | prop.getBitCode();
			m_DownStates.put(down,newProps);
			if (m_UnpropagatedDownStates == null) {
				m_UnpropagatedDownStates = new HashSet<STATE>();
			}
			m_UnpropagatedDownStates.add(down);
			return true;

		} else {
			// property already set, nothing modified
			return false;

		}
	}
	
	boolean hasDownProp(STATE down, DownStateProp prop) {
		int currentProps = m_DownStates.get(down);
		if ((currentProps & prop.getBitCode()) == 0) {
			return false;
		} else {
			return true;
		}
	}
	
	
	
	Set<STATE> getUnpropagatedDownStates() {
		return m_UnpropagatedDownStates;
	}
	
	void eraseUnpropagatedDownStates() {
		m_UnpropagatedDownStates = null;
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
		for (OutgoingReturnTransition<LETTER, STATE> trans : returnSuccessors(hier, letter)) {
			if (succ.equals(trans.getSucc())) {
				return true;
			}
		}
		return false;
	}
	
	
	public abstract Set<LETTER> lettersInternal();

	public abstract Set<LETTER> lettersInternalIncoming();

	public abstract Set<LETTER> lettersCall();

	public abstract Set<LETTER> lettersCallIncoming();

	public abstract Set<LETTER> lettersReturn();

	public abstract Set<LETTER> lettersReturnIncoming();

	public abstract Collection<STATE> succInternal(LETTER letter);

	public abstract Collection<STATE> predInternal(LETTER letter);

	public abstract Collection<STATE> succCall(LETTER letter);

	public abstract Collection<STATE> predCall(LETTER letter);

	public abstract Collection<STATE> hierPred(LETTER letter);

	public abstract Collection<STATE> succReturn(STATE hier, LETTER letter);

	public abstract Collection<STATE> predReturnLin(LETTER letter, STATE hier);

	public abstract Collection<STATE> predReturnHier(LETTER letter);


	public abstract Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final LETTER letter);

	public abstract Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors();

	public abstract Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final LETTER letter);

	public abstract Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors();
	
	public abstract Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final LETTER letter);

	public abstract Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors();

	public abstract Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final LETTER letter);

	public abstract Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors();
	
	public abstract Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE hier, final LETTER letter);

	public abstract Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final LETTER letter);

	public abstract Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE hier);

	public abstract Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors();

	public abstract Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE hier, final LETTER letter);

	public abstract Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final LETTER letter);

	public abstract Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors();

	
	
	
	abstract void addInternalOutgoing(OutgoingInternalTransition<LETTER, STATE> internalOutgoing);

	abstract void addInternalIncoming(IncomingInternalTransition<LETTER, STATE> internalIncoming);

	abstract void addCallOutgoing(OutgoingCallTransition<LETTER, STATE> callOutgoing);

	abstract void addCallIncoming(IncomingCallTransition<LETTER, STATE> callIncoming);

	abstract void addReturnOutgoing(OutgoingReturnTransition<LETTER, STATE> returnOutgoing);

	abstract void addReturnIncoming(IncomingReturnTransition<LETTER, STATE> returnIncoming);

}
