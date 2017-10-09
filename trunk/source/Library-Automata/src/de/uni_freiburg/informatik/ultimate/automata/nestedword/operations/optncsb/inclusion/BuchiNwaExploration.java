/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import java.util.Iterator;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchiNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IStateNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement.DoubleDecker;
import gnu.trove.iterator.TIntIterator;
import gnu.trove.map.TIntByteMap;
import gnu.trove.map.TIntObjectMap;
import gnu.trove.map.hash.TIntByteHashMap;
import gnu.trove.map.hash.TIntObjectHashMap;
import gnu.trove.set.TIntSet;
import gnu.trove.set.hash.TIntHashSet;


/**
 * Explore state space of Buchi Nested Word Automata
 * This implementation structure is from Ultimate 
 * */
public final class BuchiNwaExploration extends BuchiExploration<IBuchiNwa>{

	// store those state to be explored, every state will be only added once
	private final StateInfoQueue mWorkList;
	// store those state whose down states have been updated
	private final StateInfoQueue mPropagationList;
	private final TIntObjectMap<StateInfo> mStateInfoMap;
	// (q, {q'}) for every pair q and q', there exists a run from q to q'
	// over some well-matched nested word, actually they are from return transition
	// p * q * >r -> q' during the exploration
	private final TIntObjectMap<TIntSet> mReturnSummaryMap;
	
	private int numTrans = 0;
	
	public BuchiNwaExploration(IBuchiNwa operand) {
		super(operand);
		mWorkList = new StateInfoQueue();
		mPropagationList = new StateInfoQueue();
		mStateInfoMap = new TIntObjectHashMap<>();
		mReturnSummaryMap = new TIntObjectHashMap<>();
	}
	
	/**
	 * When a new state was created, it will be added into mWorkList only once.
	 * when the down states of a state which has been traversed has changed, that state
	 * should be added into mPropagationList 
	 *  */
	@Override
	protected void explore() {
		
		if(mExplored) return ;
		mExplored = true;
		// initialize
		addInitialStates();
		// loop begins
		numTrans = 0;
		do{
			
			while(! mWorkList.isEmpty()) {
				/** self loop new down states will be handled separately */
				final StateInfo currInfo = mWorkList.removeFirst();
				// unpropagateDownStates only for propagation purpose
				// in the main loop, we should clear this set
				currInfo.clearUnpropagateDownStates();
				final TIntSet newDownStatesLoops = 
						traverseReturnTransitionsWithHier(currInfo, currInfo.getDownStates());
				traverseInternalTransitions(currInfo);
				final TIntSet newDownStates = traverseCallTransitions(currInfo);
				if(newDownStates != null) {
					newDownStatesLoops.addAll(newDownStates);
				}
				
				addPropagateNewDownStates(currInfo, newDownStatesLoops);
			}
			
			/**
			 * if mWorkList is empty and propagation list is not empty, then
			 * we should propagate current new down states to successors
			 *  */
			while(mWorkList.isEmpty() && ! mPropagationList.isEmpty()) {
				propagateNewDownStates(mPropagationList.removeFirst());
			}
			
		}while(! mWorkList.isEmpty() || ! mPropagationList.isEmpty());
	}
	
	private TIntSet traverseReturnTransitionsWithHier(final StateInfo currInfo
			, final TIntSet downStates) {
		TIntSet newDownStatesLoops = new TIntHashSet();
		if(allowReturnTransitions()) {
			for(final Integer downState : iterable(downStates)){
				if(isNotEmptyDownState(downState)) {
					final TIntSet newDownStates = 
							traverseReturnTransitions(currInfo, downState);
					if(newDownStates != null) {
						newDownStatesLoops.addAll(newDownStates);
					}
				}
			}
		}
		return newDownStatesLoops;
	}
	
	
	private void addPropagateNewDownStates(final StateInfo currInfo
			, final TIntSet newDownStates) {
		assert newDownStates != null;
		if(!newDownStates.isEmpty()) {
			for(final Integer downState : iterable(newDownStates)) {
				currInfo.addDownState(downState);
			}
			addStateInfoInPropagationList(currInfo);
		}
	}
	

	private TIntSet traverseCallTransitions(final StateInfo currInfo) {
		boolean hasSelfLoops = false;
		final IStateNwa state = mOperand.getState(currInfo.getState());
		assert state != null;
		
		for(final Integer letter : mOperand.getAlphabetCall().iterable()) {
			for(final Integer succ : state.getSuccessorsCall(letter).iterable()) {
				// state * letter -> succ (downs of succ = state)
				StateInfo succInfo = getStateInfo(succ);
				final TIntByteMap succDownStates = new TIntByteHashMap();
				// put state in succ's down state set
				succDownStates.put(state.getId(), REACH_NORMAL);
				if (succInfo == null) {
					succInfo = addState(succ, succDownStates);
				} else {
					addNewDownStates(currInfo, succInfo, succDownStates.keySet());
					if (stateInfoEqual(currInfo, succInfo)) {
						hasSelfLoops = true;
					}
				}
				numTrans ++;
			}
		}
		
		if (hasSelfLoops) {
			final TIntSet newDownStates = new TIntHashSet(1);
			newDownStates.add(state.getId());
			return addNewDownStatesToItself(currInfo, newDownStates);
		}
		return null;
	}

	private void traverseInternalTransitions(final StateInfo currInfo) {
		final IStateNwa state = mOperand.getState(currInfo.getState());
		for(final Integer letter : mOperand.getAlphabetInternal().iterable()) {
			for(final Integer succ : state.getSuccessorsInternal(letter).iterable()) {
				// state * letter -> succ (downs of succ = downs of state)
				StateInfo succInfo = getStateInfo(succ);
				if(succInfo == null) {
					succInfo = addState(succ, new TIntByteHashMap(currInfo.getDownStatesMap()));
				}else {
					addNewDownStates(currInfo, succInfo, currInfo.getDownStates());
				}
				currInfo.addInternalSuccessors(succ);
				numTrans ++;
			}
		}
	}

	private TIntSet traverseReturnTransitions(final StateInfo currInfo, final int downState) {
		boolean hasSelfLoops = false;
		final IStateNwa state = mOperand.getState(currInfo.getState());
		final StateInfo downInfo = getStateInfo(downState);
		assert downInfo != null;
		
		for(final Integer letter : mOperand.getAlphabetReturn().iterable()) {
			for(final Integer succ : state.getSuccessorsReturn(downState, letter).iterable()) {
				IStateNwa succState = mOperand.getState(succ);
				assert succState != null;
				// state * downState * letter -> succState
				// (downs of succState = downs of downState)
				StateInfo succInfo = getStateInfo(succState.getId());
				if(succInfo == null) {
					succInfo = addState(succ, new TIntByteHashMap(downInfo.getDownStatesMap()));
				}else {
					addNewDownStates(currInfo, succInfo, downInfo.getDownStates());
					if(stateInfoEqual(currInfo, succInfo)) {
						hasSelfLoops = true;
					}
				}
				numTrans ++;
				// record that through hierarchy state downState, succState can be reached
				// by a return transition, and if down states of downState are updated, then
				// we should also update the down states of succState since from above we know
				// that (downs of succState = downs of downState)
				addSummary(downState, succState.getId());
			}
		}
		
		if(hasSelfLoops) {
			return addNewDownStatesToItself(currInfo, downInfo.getDownStates());
		}
		return null;		
	}
	
	private void addSummary(final int hier, final int succ) {
		addSummaryWithMap(mReturnSummaryMap, hier, succ);
	}
	
	private void addSummaryWithMap(final TIntObjectMap<TIntSet> summaryMap,
			final int hier, final int succ) {
		TIntSet succs = summaryMap.get(hier);
		if(succs == null) {
			succs = new TIntHashSet();
		}
		succs.add(succ);
		summaryMap.put(hier, succs);
	}
	
	private TIntSet getSummarySuccessorsWithMap(final TIntObjectMap<TIntSet> summaryMap,
			final int hier) {
		final TIntSet result = summaryMap.get(hier);
		if(result == null) return new TIntHashSet();
		return result;
	}
	
	private TIntSet getSummarySuccessors(final int hier) {
		return getSummarySuccessorsWithMap(mReturnSummaryMap, hier);
	}
	
	public TIntObjectMap<TIntSet> getReturnSummaries() {
		return mReturnSummaryMap;
	}

	/**
	 * Extra addNewDownStates in order to avoid multiple same calls
	 * */
	private TIntSet addNewDownStatesToItself(final StateInfo stateInfo,
			final TIntSet downStates) {
		TIntSet newDownStates = null;
		for(final Integer down : iterable(downStates)) {
			if (!stateInfo.getDownStates().contains(down)) {
				if (newDownStates == null) {
					newDownStates = new TIntHashSet();
				}
				newDownStates.add(down);
			}
		}
		return newDownStates;
	}
	
	private boolean stateInfoEqual(final StateInfo stateInfo1
			         , final StateInfo stateInfo2) {
		return stateInfo1 == stateInfo2;
	}
	

	/**
	 * add new down states to succStateInfo with the states in downStates
	 * */
	private void addNewDownStates(final StateInfo currInfo, final StateInfo succInfo
			, final TIntSet downStates) {
		
		// will be handled at other place, avoid multiple calls for itself
		if(stateInfoEqual(currInfo, succInfo)) return ;
		
		boolean needPropagation = false;
		for(final Integer down : iterable(downStates)) {
			final boolean newlyAdded = succInfo.addDownState(down);
			if (newlyAdded) {
				needPropagation = true;
			}
		}
		/**
		 * If there is new down state for succStateInfo, then the down state of
		 * succStateInfo should be propagated 
		 * */
		if (needPropagation) {
			addStateInfoInPropagationList(succInfo);
		}
	}
	
	/** 
	 * If a state has not been traversed, then no need to be added
	 * into mPropagationList
	 * */
	private void addStateInfoInPropagationList(final StateInfo stateInfo) {
		if(! mWorkList.hasStateInfo(stateInfo)) {
			mPropagationList.add(stateInfo);
		}
	}

	private StateInfo getStateInfo(final int state) {
		return mStateInfoMap.get(state);
	}

	private boolean allowReturnTransitions() {
		return ! mOperand.getAlphabetReturn().isEmpty();
	}
	
	private boolean isNotEmptyDownState(final int state) {
		return state != DoubleDecker.EMPTY_DOWN_STATE;
	}
	
	/**
	 * If a state has been added new down states, then those down states should be propagated to
	 * 
	 *   * its internal successors, since they share the same down states
	 *   * its return successors when it is hierarchy predecessors, since they share the same down states
	 *   
	 *   Also we should add new return transitions with its new down states
	 *   */
	private void propagateNewDownStates(final StateInfo currInfo) {
		final TIntSet unpropagateDownStates = currInfo.getUnpropagateDownStates();
		if(unpropagateDownStates == null) return ;
		
		for(final Integer succ : iterable(currInfo.getInternalSuccessors())) {
			final StateInfo succInfo = getStateInfo(succ);
			addNewDownStates(currInfo, succInfo, unpropagateDownStates);
		}
		
		for(final Integer succ : iterable(getSummarySuccessors(currInfo.getState()))) {
			final StateInfo succInfo = getStateInfo(succ);
			addNewDownStates(currInfo, succInfo, unpropagateDownStates);
		}

		if(allowReturnTransitions()) {
			TIntSet newDownStatesLoops = traverseReturnTransitionsWithHier(currInfo
					                                       , unpropagateDownStates);
			currInfo.clearUnpropagateDownStates();
			// must first clear its used down states
			// in order to add new propagate down states
			addPropagateNewDownStates(currInfo, newDownStatesLoops);
		}else {
			currInfo.clearUnpropagateDownStates();
		}
	}

	private void addInitialStates() {
		for(final Integer state : mOperand.getInitialStates().iterable()) {
			final TIntByteMap downStates = new TIntByteHashMap();
			addState(state, downStates);
		}
	}

	private StateInfo addState(final int state, final TIntByteMap downStates) {
		assert ! mStateInfoMap.containsKey(state);
		final StateInfo stateInfo = new StateInfo(state, downStates);
		mStateInfoMap.put(state, stateInfo);
		mWorkList.add(stateInfo);
		return stateInfo;
	}
	
	public int getNumTrans() {
		return numTrans;
	}
	
	private Iterable<Integer> iterable(final TIntSet set) {
		return () -> new Iterator<Integer>() {

			TIntIterator iter = set.iterator();
			@Override
			public boolean hasNext() {
				return iter.hasNext();
			}

			@Override
			public Integer next() {
				return iter.next();
			}
			
		};
	}

	//----------------------------------------------------------------
	private static final byte REACH_NORMAL = 0; //normal reachability 
	private static final byte REACH_FINAL  = 1; //reachability to final
	//----------------------------------------------------------------
	private class StateInfo {
		
		private final int mState;
		// downStates with its reach property
		private final TIntByteMap mDownStates;
		private TIntSet mUnPropagateDownStates;
		private final TIntSet mInternalSuccs; // cache the internal successors
		
		
		public StateInfo(final int state, final TIntByteMap downStates) {
			mState = state;
			mDownStates = downStates;
			mInternalSuccs = new TIntHashSet();
		}
		
		int getState() {
			return mState;
		}
		
		TIntSet getDownStates() {
			return mDownStates.keySet();
		}
		
		TIntByteMap getDownStatesMap() {
			return mDownStates;
		}
		
		void clearUnpropagateDownStates() {
			mUnPropagateDownStates = null;
		}
		
		TIntSet getUnpropagateDownStates() {
			return mUnPropagateDownStates;
		}
		
		boolean addDownState(final int down) {
			return addDownProp(down, REACH_NORMAL);
		}
		
		boolean addReachFinalDownState(final int down) {
			return addDownProp(down, REACH_FINAL);
		}
		
		boolean hasDownProp(final int down, byte prop) {
			if(! mDownStates.containsKey(down)) return false;
			final byte val = mDownStates.get(down);
			return (val & prop) != 0;
		}
		
		boolean addDownProp(final int down, byte prop) {
			// already in the down state property
			if(hasDownProp(down, prop)) return false;
			// there is no such property
			mDownStates.put(down, prop);
			if(mUnPropagateDownStates == null) {
				mUnPropagateDownStates = new TIntHashSet();
			}
			mUnPropagateDownStates.add(down);
			return true;
		}
		
		void addInternalSuccessors(final int succ) {
			mInternalSuccs.add(succ);
		}
		
		TIntSet getInternalSuccessors() {
			return mInternalSuccs;
		}
		
		public String toString() {
			return "<state: " + mState + ", downs: " + mDownStates.toString() 
			     + ", unpropDowns: " + mUnPropagateDownStates + ", inSucc:" + mInternalSuccs + ">";
		}
		
	}
	
	//----------------------------------------------------------------
	private class StateInfoQueue extends LinkedList<StateInfo> {
		private static final long serialVersionUID = 1L;
		private final TIntSet mInList;
		
		public StateInfoQueue() {
			super();
			mInList = new TIntHashSet();
		}
		
		@Override
		public StateInfo removeFirst() {
			StateInfo result = super.removeFirst();
			mInList.remove(result.getState());
			return result;
		}
		
		public boolean hasStateInfo(StateInfo state) {
			return mInList.contains(state.getState());
		}
		
		@Override
		public boolean add(StateInfo state) {
			if(! mInList.contains(state.getState())) {
				mInList.add(state.getState());
				return super.add(state);
			}
			return false;
		}
		
	}
	
	private AccetpingSummariesComputation mAcceptingSummariesComputation;
	
	public TIntObjectMap<TIntSet> getAcceptingSummaries() {
		assert mExplored == true;
		if(mAcceptingSummariesComputation == null) {
			mAcceptingSummariesComputation = new AccetpingSummariesComputation();
		}
	
		return mAcceptingSummariesComputation.mAcceptingSummaryMap;
	}
	
	//----------------------------------------------------------------
	// computing accepting summaries
	protected class AccetpingSummariesComputation {
		
		private final StateInfoQueue mAccWorkList;
		private final TIntObjectMap<TIntSet> mAcceptingSummaryMap;
		
		AccetpingSummariesComputation() {
			mAccWorkList = new StateInfoQueue();
			mAcceptingSummaryMap = new TIntObjectHashMap<>();
			initWorkList();
			while(! mAccWorkList.isEmpty()) {
				final StateInfo currInfo = mAccWorkList.removeFirst();
				propagateReachFinalDownStates(currInfo);
			}
		}

		private void propagateReachFinalDownStates(StateInfo currInfo) {
			final TIntSet unpropagateDownStates = currInfo.getUnpropagateDownStates();
			if(unpropagateDownStates == null) return ;
			
			// if (q, q') contains an accepting state, and we have q'* a -> q'' 
			// then (q, q'') also contains an accepting state
			for(final Integer succ : iterable(currInfo.getInternalSuccessors())) {
				final StateInfo succInfo = getStateInfo(succ);
				addReachFinalDownStates(currInfo, succInfo, unpropagateDownStates);
			}
			
			// if (q, q') contains an accepting state, and we have p * q' * r- > q'' 
		    // then (q, q'') also contains an accepting state since there is well-matched
			// nested word from q' to q''
			for(final Integer succ : iterable(getSummarySuccessors(currInfo.getState()))) {
				final StateInfo succInfo = getStateInfo(succ);
				addReachFinalDownStates(currInfo, succInfo, unpropagateDownStates);
			}

			if(allowReturnTransitions()) {
				currInfo.clearUnpropagateDownStates();
				findAcceptingSummaries(currInfo);
			}
			
		}
		
		private void findAcceptingSummaries(StateInfo currInfo) {
	
			final IStateNwa state = mOperand.getState(currInfo.getState());
			for (final Integer letter : state.getEnabledLettersReturn()) {
				for(final Integer hier : state.getEnabledHiersReturn(letter)) {
					for(final Integer succ : state.getSuccessorsReturn(hier, letter).iterable()) {
						final StateInfo hierInfo = getStateInfo(hier);
						final StateInfo succInfo = getStateInfo(succ);
						// if (q, q') contains an accepting state, then q' * q * r- > q''
						// (q, q'') is an accepting summary and we also need to add (p, q'')
						// in propagation list where p is down state of q
						if (currInfo.hasDownProp(hier, REACH_FINAL)) {
							addReachFinalDownStates(null, succInfo, hierInfo.getDownStates());
							addAcceptingSummary(hier, succ);
						}	
					}
				}
			}
			
		}

		private void addAcceptingSummary(int hier, int succ) {
			addSummaryWithMap(mAcceptingSummaryMap, hier, succ);
		}

		private void initWorkList() {
			// collect all DoubleDecker (q, q') with q' being accepting state
			for(final Integer fin : mOperand.getFinalStates().iterable()) {
				StateInfo succInfo = getStateInfo(fin);
				addReachFinalDownStates(null, succInfo, succInfo.getDownStates());
			}
		}
		
		//
		private void addReachFinalDownStates(final StateInfo currInfo, final StateInfo succInfo
				, final TIntSet downStates) {
			
			// will be handled at other place, avoid multiple calls for itself
			if(stateInfoEqual(currInfo, succInfo)) return ;
			
			boolean needPropagation = false;
			for(final Integer down : iterable(downStates)) {
				// add down state which can reach final states
				final boolean newlyAdded = succInfo.addReachFinalDownState(down);
				if (newlyAdded) {
					needPropagation = true;
				}
			}

			if (needPropagation) {
				mAccWorkList.add(succInfo);
			}
		}
		
		@Override
		public String toString() {
			return mAcceptingSummaryMap.toString();
		}
		
	}
	
	//----------------------------------------------------------------

	@Override
	public String getOperationName() {
		return "NwaExploration";
	}

}
