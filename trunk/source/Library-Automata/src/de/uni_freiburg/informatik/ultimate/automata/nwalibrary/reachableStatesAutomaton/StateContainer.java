/*
 * Copyright (C) 2009-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
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
		/**
		 * There is a (not necessarily initial) run starting in DoubleDecker 
		 * (up, down) that visits a final state at least once. 
		 */
		REACH_FINAL_ONCE(1),
		/**
		 * There is a (not necessarily initial) run starting in DoubleDecker 
		 * (up, down) that visits a final state at infinitely often. 
		 */
		REACH_FINAL_INFTY(2),
		REACHABLE_FROM_FINAL_WITHOUT_CALL(4),
		/**
		 * The DoubleDecker (up,down) cannot reach a final state 
		 * (REACH_FINAL_ONCE does not hold), but is still reachable, if dead 
		 * ends have been removed.
		 */
		REACHABLE_AFTER_DEADEND_REMOVAL(8),
		/**
		 * The DoubleDecker (up,down) cannot reach a final state infinitely 
		 * often (REACH_FINAL_INFTY) does not hold, but is still reachable, 
		 * if dead ends have been removed.
		 */
		REACHABLE_AFTER_NONLIVE_REMOVAL(16);
		
		
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
//		StringBuilder sb = new StringBuilder();
//		sb.append(m_State.toString());
//		sb.append(System.getProperty("line.separator"));
//		for (OutgoingInternalTransition<LETTER, STATE> trans : internalSuccessors()) {
//			sb.append(trans).append("  ");
//		}
//		sb.append(System.getProperty("line.separator"));
//		for (IncomingInternalTransition<LETTER, STATE> trans : internalPredecessors()) {
//			sb.append(trans).append("  ");
//		}
//		sb.append(System.getProperty("line.separator"));
//		for (OutgoingCallTransition<LETTER, STATE> trans : callSuccessors()) {
//			sb.append(trans).append("  ");
//		}
//		sb.append(System.getProperty("line.separator"));
//		for (IncomingCallTransition<LETTER, STATE> trans : callPredecessors()) {
//			sb.append(trans).append("  ");
//		}
//		sb.append(System.getProperty("line.separator"));
//		for (OutgoingReturnTransition<LETTER, STATE> trans : returnSuccessors()) {
//			sb.append(trans).append("  ");
//		}
//		sb.append(System.getProperty("line.separator"));
//		for (IncomingReturnTransition<LETTER, STATE> trans : returnPredecessors()) {
//			sb.append(trans).append("  ");
//		}
//		sb.append(System.getProperty("line.separator"));
//		sb.append(m_DownStates.toString());
//		sb.append(System.getProperty("line.separator"));
//		return sb.toString();
		return m_State.toString();
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
	
	/**
	 * Returns the StateContainer that has the lower serial number.
	 * If one is null return the other. If both are null return null;
	 */
	public static <LETTER, STATE> StateContainer<LETTER, STATE> returnLower(
			StateContainer<LETTER, STATE> fst, StateContainer<LETTER, STATE> snd) {
		if (fst == null) {
			return snd;
		} else if (snd == null) {
				return fst;
		} else {
			if (fst.getSerialNumber() < snd.getSerialNumber()) {
				return fst;
			} else {
				assert fst.getSerialNumber() != snd.getSerialNumber() || fst == snd :
					"two state container with similar serial number";
				return snd;
			}
		}
	}

}
