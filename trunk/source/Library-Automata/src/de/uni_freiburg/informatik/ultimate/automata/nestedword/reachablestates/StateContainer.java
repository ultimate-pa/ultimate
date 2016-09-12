/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates.ReachProp;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * Auxiliary data structure used by {@link NestedWordAutomatonReachableStates}.
 * This data structure stores
 * <ul>
 * <li>a state together with its incoming and outgoing transitions
 * <li>the down states of this state
 * <li>information about reachability of this state
 * <li>field in which algorithms of {@link NestedWordAutomatonReachableStates} store temporary data.
 * </ul>
 * <p>
 * TODO Christian 2016-09-10: A class which overrides hashCode() should also override equals()!
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class StateContainer<LETTER, STATE> {
	/**
	 * Properties of a down state.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
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
		
		private final int mBitcode;
		
		DownStateProp(final int bitcode) {
			this.mBitcode = bitcode;
		}
		
		public int getBitCode() {
			return mBitcode;
		}
	}
	
	protected final STATE mState;
	protected final int mSerialNumber;
	protected ReachProp mReachProp;
	protected final Map<STATE, Integer> mDownStates;
	protected Set<STATE> mUnpropagatedDownStates;
	protected final boolean mCanHaveOutgoingReturn;
	
	/**
	 * Constructor.
	 * 
	 * @param state
	 *            state
	 * @param serialNumber
	 *            serial number
	 * @param downStates
	 *            down states
	 * @param canHaveOutgoingReturn
	 *            {@code true} iff the state can have an outgoing return
	 */
	public StateContainer(final STATE state, final int serialNumber, final Map<STATE, Integer> downStates,
			final boolean canHaveOutgoingReturn) {
		mState = state;
		mSerialNumber = serialNumber;
		mDownStates = downStates;
		mReachProp = ReachProp.REACHABLE;
		mCanHaveOutgoingReturn = canHaveOutgoingReturn;
	}
	
	@Override
	public String toString() {
//		StringBuilder sb = new StringBuilder();
//		sb.append(mState.toString());
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
//		sb.append(mDownStates.toString());
//		sb.append(System.getProperty("line.separator"));
//		return sb.toString();
		return mState.toString();
	}
	
	public int getSerialNumber() {
		return mSerialNumber;
	}
	
	public ReachProp getReachProp() {
		return mReachProp;
	}
	
	public void setReachProp(final ReachProp reachProp) {
		mReachProp = reachProp;
	}
	
	protected Map<STATE, Integer> getDownStates() {
		return mDownStates;
	}
	
	@Override
	public int hashCode() {
		return mState.hashCode();
	}
	
	protected STATE getState() {
		return mState;
	}
	
	/**
	 * Add down state. Without any properties set. Returns true iff this down
	 * state was not already there.
	 * If the down state was already there it may not have had any
	 * DownStateProps
	 */
	boolean addReachableDownState(final STATE down) {
		assert !mDownStates.containsKey(down) || mDownStates.get(down) == 0;
		final Integer oldValue = mDownStates.put(down, 0);
		if (oldValue == null) {
			if (mUnpropagatedDownStates == null) {
				mUnpropagatedDownStates = new HashSet<>();
			}
			mUnpropagatedDownStates.add(down);
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Set DownStateProp prop for down state. Returns true iff this property was
	 * modified (not already set).
	 */
	boolean setDownProp(final STATE down, final DownStateProp prop) {
		final int currentProps = mDownStates.get(down);
		if ((currentProps & prop.getBitCode()) == 0) {
			// property not yet set
			final int newProps = currentProps | prop.getBitCode();
			mDownStates.put(down, newProps);
			if (mUnpropagatedDownStates == null) {
				mUnpropagatedDownStates = new HashSet<>();
			}
			mUnpropagatedDownStates.add(down);
			return true;
			
		} else {
			// property already set, nothing modified
			return false;
			
		}
	}
	
	boolean hasDownProp(final STATE down, final DownStateProp prop) {
		final int currentProps = mDownStates.get(down);
		return (currentProps & prop.getBitCode()) != 0;
	}
	
	Set<STATE> getUnpropagatedDownStates() {
		return mUnpropagatedDownStates;
	}
	
	void eraseUnpropagatedDownStates() {
		mUnpropagatedDownStates = null;
	}
	
	protected boolean containsInternalTransition(final LETTER letter, final STATE succ) {
		for (final OutgoingInternalTransition<LETTER, STATE> trans : internalSuccessors(letter)) {
			if (succ.equals(trans.getSucc())) {
				return true;
			}
		}
		return false;
	}
	
	protected boolean containsCallTransition(final LETTER letter, final STATE succ) {
		for (final OutgoingCallTransition<LETTER, STATE> trans : callSuccessors(letter)) {
			if (succ.equals(trans.getSucc())) {
				return true;
			}
		}
		return false;
	}
	
	protected boolean containsReturnTransition(final STATE hier, final LETTER letter, final STATE succ) {
		for (final OutgoingReturnTransition<LETTER, STATE> trans : returnSuccessors(hier, letter)) {
			if (succ.equals(trans.getSucc())) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * @return Outgoing internal letters of this state.
	 */
	public abstract Set<LETTER> lettersInternal();
	
	/**
	 * @return Incoming internal letters of this state.
	 */
	public abstract Set<LETTER> lettersInternalIncoming();
	
	/**
	 * @return Outgoing call letters of this state.
	 */
	public abstract Set<LETTER> lettersCall();
	
	/**
	 * @return Incoming call letters of this state.
	 */
	public abstract Set<LETTER> lettersCallIncoming();
	
	/**
	 * @return Outgoing return letters of this state.
	 */
	public abstract Set<LETTER> lettersReturn();
	
	/**
	 * @return Incoming return letters of this state.
	 */
	public abstract Set<LETTER> lettersReturnIncoming();
	
	/**
	 * @param letter
	 *            The letter.
	 * @return Internal successors.
	 */
	public abstract Collection<STATE> succInternal(LETTER letter);
	
	/**
	 * @param letter
	 *            The letter.
	 * @return Internal predecessors.
	 */
	public abstract Collection<STATE> predInternal(LETTER letter);
	
	/**
	 * @param letter
	 *            The letter.
	 * @return Call successors.
	 */
	public abstract Collection<STATE> succCall(LETTER letter);
	
	/**
	 * @param letter
	 *            The letter.
	 * @return Call predecessors.
	 */
	public abstract Collection<STATE> predCall(LETTER letter);
	
	/**
	 * @param letter
	 *            The letter.
	 * @return Hierarchical predecessors for outgoing return transitions.
	 */
	public abstract Collection<STATE> hierPred(LETTER letter);
	
	/**
	 * @param hier
	 *            The hierarchical predecessor.
	 * @param letter
	 *            The letter.
	 * @return Linear return successors.
	 */
	public abstract Collection<STATE> succReturn(STATE hier, LETTER letter);
	
	/**
	 * @param letter
	 *            The letter.
	 * @param hier
	 *            hierarchical predecessor
	 * @return Linear return predecessors.
	 */
	public abstract Collection<STATE> predReturnLin(LETTER letter, STATE hier);
	
	/**
	 * @param letter
	 *            The letter.
	 * @return Hierarchical predecessors for incoming return transitions.
	 */
	public abstract Collection<STATE> predReturnHier(LETTER letter);
	
	/**
	 * @param letter
	 *            The letter.
	 * @return Internal successors.
	 */
	public abstract Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final LETTER letter);
	
	/**
	 * @return Internal successors.
	 */
	public abstract Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors();
	
	/**
	 * @param letter
	 *            The letter.
	 * @return Internal predecessors.
	 */
	public abstract Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final LETTER letter);
	
	/**
	 * @return Internal predecessors.
	 */
	public abstract Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors();
	
	/**
	 * @param letter
	 *            The letter.
	 * @return Call successors.
	 */
	public abstract Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final LETTER letter);
	
	/**
	 * @return Call successors.
	 */
	public abstract Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors();
	
	/**
	 * @param letter
	 *            The letter.
	 * @return Call predecessors.
	 */
	public abstract Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final LETTER letter);
	
	/**
	 * @return Call predecessors.
	 */
	public abstract Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors();
	
	/**
	 * @param hier
	 *            The hierarchical predecessor.
	 * @param letter
	 *            The letter.
	 * @return Return successors.
	 */
	public abstract Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE hier,
			final LETTER letter);
	
	/**
	 * @param letter
	 *            The letter.
	 * @return Return successors.
	 */
	public abstract Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final LETTER letter);
	
	/**
	 * @return Return successors.
	 */
	public abstract Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors();
	
	/**
	 * @param hier
	 *            The hierarchical predecessor.
	 * @return Return successors.
	 */
	public abstract Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE hier);
	
	/**
	 * @param hier
	 *            The hierarchical predecessor.
	 * @param letter
	 *            The letter.
	 * @return Return predecessors.
	 */
	public abstract Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE hier,
			final LETTER letter);
	
	/**
	 * @param letter
	 *            The letter.
	 * @return Return predecessors.
	 */
	public abstract Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final LETTER letter);
	
	/**
	 * @return Return predecessors.
	 */
	public abstract Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors();
	
	/**
	 * @param internalOutgoing
	 *            New outgoing internal transition.
	 */
	abstract void addInternalOutgoing(OutgoingInternalTransition<LETTER, STATE> internalOutgoing);
	
	/**
	 * @param internalOutgoing
	 *            New incoming internal transition.
	 */
	abstract void addInternalIncoming(IncomingInternalTransition<LETTER, STATE> internalIncoming);
	
	/**
	 * @param internalOutgoing
	 *            New outgoing call transition.
	 */
	abstract void addCallOutgoing(OutgoingCallTransition<LETTER, STATE> callOutgoing);
	
	/**
	 * @param internalOutgoing
	 *            New incoming call transition.
	 */
	abstract void addCallIncoming(IncomingCallTransition<LETTER, STATE> callIncoming);
	
	/**
	 * @param internalOutgoing
	 *            New outgoing return transition.
	 */
	abstract void addReturnOutgoing(OutgoingReturnTransition<LETTER, STATE> returnOutgoing);
	
	/**
	 * @param internalOutgoing
	 *            New incoming return transition.
	 */
	abstract void addReturnIncoming(IncomingReturnTransition<LETTER, STATE> returnIncoming);
	
	/**
	 * @param fst
	 *            first state container
	 * @param snd
	 *            second state container
	 * @return The StateContainer that has the lower serial number.
	 *         If one is null return the other. If both are null return null;
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 */
	@SuppressWarnings("squid:S1698")
	public static <LETTER, STATE> StateContainer<LETTER, STATE> returnLower(
			final StateContainer<LETTER, STATE> fst, final StateContainer<LETTER, STATE> snd) {
		if (fst == null) {
			return snd;
		} else if (snd == null) {
			return fst;
		} else {
			if (fst.getSerialNumber() < snd.getSerialNumber()) {
				return fst;
			} else {
				// equality intended here
				assert fst.getSerialNumber() != snd.getSerialNumber()
						|| fst == snd : "two state container with similar serial number";
				return snd;
			}
		}
	}
}
