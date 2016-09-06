/*
 * Copyright (C) 2012-2015 Fabian Reiter
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Automaton that is returned as the result of the {@code BuchiComplementSVW}
 * operation. States and transitions are built on the fly. <br>
 * <p>
 * The implementation follows the notation introduced in “Improved Ramsey-Based
 * Büchi Complementation” by Breuers, Löding and Olschewski (Springer, 2012).
 * 
 * @author Fabian Reiter
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class BuchiComplementAutomatonSVW<LETTER, STATE>
		implements INestedWordAutomatonOldApi<LETTER, STATE> {
	private final AutomataLibraryServices mServices;
	private final TransitionMonoidAutomaton mTMA;
	private final Set<LETTER> mAlphabet;
	private SizeInfoContainer mSizeInfo = null;
	// not all transitions have been computed
	private boolean mBuildCompleted = false;
	protected final IStateFactory<STATE> mStateFactory;
	protected final STATE mEmptyStackState;
	private final STATE mInitialState;
	// only one
	private final Set<STATE> mInitialStateSet = new HashSet<STATE>(1);
	private final Set<STATE> mFinalStateSet = null;
	private final Map<STATE, Map<LETTER, Set<STATE>>> mTransitionsOut =
			new HashMap<>();
	private final Map<STATE, Map<LETTER, Set<STATE>>> mTransitionsIn =
			new HashMap<>();
	private final Map<STATE, MetaState> mMapState2MS = new HashMap<>();
	
	private final ILogger mLogger;
	private final String mUnsupportedOperationMessage =
			"Transform to NestedWordAutomaton to get full support.";
			
	public BuchiComplementAutomatonSVW(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> origAutomaton)
					throws AutomataOperationCanceledException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mTMA = new TransitionMonoidAutomaton(origAutomaton);
		mAlphabet = origAutomaton.getInternalAlphabet();
		if (!origAutomaton.getCallAlphabet().isEmpty() || !origAutomaton.getReturnAlphabet().isEmpty()) {
			throw new IllegalArgumentException("only applicable to Buchi automata (not BuchiNWA)");
		}
		mStateFactory = origAutomaton.getStateFactory();
		mEmptyStackState = mStateFactory.createEmptyStackState();
		final MetaState metaInitialState = getMetaState(mTMA.mInitialState, mTMA.mInitialTMA);
		mInitialState = metaInitialState.mOutputState;
		mInitialStateSet.add(mInitialState);
	}
	
	/**
	 * @return an equivalent {@code NestedWordAutomaton} object <br>
	 *         <b>Use with caution!</b> The automaton has to be computed
	 *         entirely.
	 */
	public INestedWordAutomaton<LETTER, STATE> toNestedWordAutomaton() throws AutomataOperationCanceledException {
		final NestedWordAutomaton<LETTER, STATE> result =
				new NestedWordAutomaton<LETTER, STATE>(mServices, mAlphabet, null, null,
						mStateFactory);
		final int size = getSizeInfo().mTotalSize;
		// Breadth-first traversal of the state space.
		final Set<STATE> alreadySeen = new HashSet<STATE>(size);
		final Queue<STATE> queue = new LinkedList<STATE>();
		alreadySeen.add(mInitialState);
		queue.add(mInitialState);
		result.addState(true, false, mInitialState);
		while (!queue.isEmpty()) {
			final STATE state = queue.remove();
			for (final LETTER letter : mAlphabet) {
				final Collection<STATE> succSet = succInternal(state, letter);
				for (final STATE succState : succSet) {
					if (!alreadySeen.contains(succState)) {
						alreadySeen.add(succState);
						queue.add(succState);
						if (isFinal(succState)) {
							result.addState(false, true, succState);
						} else {
							result.addState(false, false, succState);
						}
					}
					result.addInternalTransition(state, letter, succState);
				}
			}
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		mBuildCompleted = true; // side effect of the BF traversal
		return result;
	}
	
	private class SizeInfoContainer {
		public int mTotalSize;
		public int mTmaSize;
		public int mNumOfReachableTMAs;
	}
	
	private SizeInfoContainer getSizeInfo() {
		if (mSizeInfo == null) {
			mSizeInfo = new SizeInfoContainer();
			// Number of states per TMA:
			final int m = mSizeInfo.mTmaSize = mTMA.size();
			// Number of reachable TMAs (initial + looping part):
			final int r = mSizeInfo.mNumOfReachableTMAs = mTMA.statesWithLeftRejectingPartners().size() + 1;
			// Total number of states:
			mSizeInfo.mTotalSize = r * m;
		}
		return mSizeInfo;
	}
	
	@Override
	public int size() {
		return getSizeInfo().mTotalSize;
	}
	
	@Override
	public Set<LETTER> getAlphabet() {
		return mAlphabet;
	}
	
	@Override
	public String sizeInformation() {
		final SizeInfoContainer sizeInfo = getSizeInfo();
		final StringBuilder sb = new StringBuilder();
		sb.append("has ");
		sb.append(sizeInfo.mTotalSize);
		sb.append(" states.");
		sb.append(" Size of a transition monoid automaton (TMA): ");
		sb.append(sizeInfo.mTmaSize);
		sb.append(".");
		sb.append(" Number of reachable TMAs: ");
		sb.append(sizeInfo.mNumOfReachableTMAs);
		sb.append(".");
		return sb.toString();
	}
	
	@Override
	public Set<LETTER> getInternalAlphabet() {
		return mAlphabet;
	}
	
	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}
	
	@Override
	public Set<STATE> getStates() {
		if (!mBuildCompleted) {
			final int size = getSizeInfo().mTotalSize;
			// Breadth-first traversal of the state space.
			final Set<STATE> alreadySeen = new HashSet<STATE>(size);
			final Queue<STATE> queue = new LinkedList<STATE>();
			alreadySeen.add(mInitialState);
			queue.add(mInitialState);
			while (!queue.isEmpty()) {
				final STATE state = queue.remove();
				for (final LETTER letter : mAlphabet) {
					final Collection<STATE> succSet = succInternal(state, letter);
					for (final STATE succState : succSet) {
						if (!alreadySeen.contains(succState)) {
							alreadySeen.add(succState);
							queue.add(succState);
						}
					}
				}
				// TODO: Uncomment the following, once getStates() in
				// INestedWordAutomaton has "throws OperationCanceledException"
				// ————————————————————————————————————————————————————————————
				// if (!mUltiServ.continueProcessing()) {
				// throw new OperationCanceledException();
				// }
				// ————————————————————————————————————————————————————————————
			}
			mBuildCompleted = true;
		}
		return mTransitionsOut.keySet();
	}
	
	@Override
	public Set<STATE> getInitialStates() {
		return mInitialStateSet;
	}
	
	@Override
	public Collection<STATE> getFinalStates() {
		if (mFinalStateSet == null) {
			final Set<Integer> reachableTMAs = mTMA.statesWithLeftRejectingPartners();
			for (final Integer tmaNb : reachableTMAs) {
				final MetaState metaState = getMetaState(mTMA.mInitialState, tmaNb);
				/**
				 * Christian 2016-08-16: BUG: mFinalStateSet is null here.
				 */
				mFinalStateSet.add(metaState.mOutputState);
			}
		}
		return mFinalStateSet;
	}
	
	@Override
	public boolean isInitial(final STATE state) {
		if (!knows(state)) {
			throw new IllegalArgumentException("State " + state + " is not (yet) known.");
		}
		return state.equals(mInitialState);
	}
	
	@Override
	public boolean isFinal(final STATE state) {
		final MetaState metaState = getMetaState(state);
		if (metaState == null) {
			throw new IllegalArgumentException("State " + state + " is not (yet) known.");
		}
		return metaState.mStateNb.equals(mTMA.mInitialState) && !metaState.mTmaNb.equals(mTMA.mInitialTMA);
	}
	
	@Override
	public STATE getEmptyStackState() {
		return this.mEmptyStackState;
	}
	
	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		if (!knows(state)) {
			throw new IllegalArgumentException("State " + state + " is not (yet) known.");
		}
		return mAlphabet;
	}
	
	@Override
	public Set<LETTER> lettersInternalIncoming(final STATE state) {
		if (!knows(state)) {
			throw new IllegalArgumentException("State " + state + " is not (yet) known.");
		}
		final Set<LETTER> result = new HashSet<LETTER>();
		for (final LETTER letter : mAlphabet) {
			final Collection<STATE> predStateSet = predInternal(state, letter);
			if (!predStateSet.isEmpty()) {
				result.add(letter);
			}
		}
		return result;
	}
	
	@Override
	public Collection<STATE> succInternal(final STATE state, final LETTER letter) {
		Map<LETTER, Set<STATE>> map = mTransitionsOut.get(state);
		if (map == null) {
			map = new HashMap<LETTER, Set<STATE>>();
			mTransitionsOut.put(state, map);
		}
		Set<STATE> result = map.get(letter);
		// If the result is not in the map, compute it.
		if (result == null) {
			if (!mAlphabet.contains(letter)) {
				throw new IllegalArgumentException("Letter " + letter + " is not in the alphabet.");
			}
			final MetaState mState = getMetaState(state);
			if (mState == null) {
				throw new IllegalArgumentException("State " + state + " is not (yet) known.");
			}
			result = new HashSet<STATE>();
			map.put(letter, result);
			final Set<MetaState> mResult = new HashSet<MetaState>();
			// Add the (unique) successor that is in the same TMA.
			final Integer succStateNb = mTMA.successor(mState.mStateNb, letter);
			mResult.add(getMetaState(succStateNb, mState.mTmaNb));
			// If we are in the initial TMA, we have to add transitions to the
			// initial states of some of the TMAs in the looping part of the
			// complement automaton.
			if (mState.mTmaNb.equals(mTMA.mInitialTMA)) {
				for (final Integer otherTMA_Nb : mTMA.rightRejectingPartners(succStateNb)) {
					mResult.add(getMetaState(mTMA.mInitialState, otherTMA_Nb));
				}
			} else {
				// Otherwise we are in a TMA in the looping part. If we can reach
				// the final state (of this TMA), we have to add a transition that
				// loops back to the initial state.
				if (succStateNb.equals(mState.mTmaNb)) {
					mResult.add(getMetaState(mTMA.mInitialState, mState.mTmaNb));
				}
			}
			// Convert set of MetaStates to set of STATEs.
			for (final MetaState succState : mResult) {
				result.add(succState.mOutputState);
			}
		}
		return result;
	}
	
	@Override
	public Collection<STATE> predInternal(final STATE state, final LETTER letter) {
		Map<LETTER, Set<STATE>> map = mTransitionsIn.get(state);
		if (map == null) {
			map = new HashMap<LETTER, Set<STATE>>();
			mTransitionsIn.put(state, map);
		}
		Set<STATE> result = map.get(letter);
		// If the result is not in the map, compute it.
		if (result == null) {
			if (!mAlphabet.contains(letter)) {
				throw new IllegalArgumentException("Letter " + letter + " is not in the alphabet.");
			}
			final MetaState mState = getMetaState(state);
			if (mState == null) {
				throw new IllegalArgumentException("State " + state + " is not (yet) known.");
			}
			result = new HashSet<STATE>();
			map.put(letter, result);
			final Set<MetaState> mResult = new HashSet<MetaState>();
			// Add the predecessors inherited from the TMA.
			final Set<Integer> predStateNbSet = mTMA.predecessors(mState.mStateNb, letter);
			if (predStateNbSet == null) {
				throw new NullPointerException("20160830 Matthias: This NPE is a known and old bug. I will fix it only when I revise the Ramsey-based complementation.");
			}
			for (final Integer predStateNb : predStateNbSet) {
				mResult.add(getMetaState(predStateNb, mState.mTmaNb));
			}
			// If state is the initial state of a TMA in the looping part of the
			// complement automaton, we have to add the transitions from the
			// initial part and those from within the same TMA that loop back to
			// the initial state.
			if (mState.mStateNb.equals(mTMA.mInitialState) && !mState.mTmaNb.equals(mTMA.mInitialTMA)) {
				// Transitions from the initial part
				final Set<Integer> leftRejectingPartnerSet = mTMA.leftRejectingPartners(mState.mTmaNb);
				for (final Integer leftRejectingPartner : leftRejectingPartnerSet) {
					final Set<Integer> predOfLRPSet = mTMA.predecessors(leftRejectingPartner, letter);
					for (final Integer predOfLRP : predOfLRPSet) {
						mResult.add(getMetaState(predOfLRP, mTMA.mInitialTMA));
					}
				}
				// Back loops from within the same TMA
				final Set<Integer> predOfTerminalSet = mTMA.predecessors(mState.mTmaNb, letter);
				for (final Integer predOfTerminal : predOfTerminalSet) {
					mResult.add(getMetaState(predOfTerminal, mState.mTmaNb));
				}
			}
			// Convert set of MetaStates to set of STATEs.
			for (final MetaState predState : mResult) {
				result.add(predState.mOutputState);
			}
		}
		return result;
	}
	
	@Override
	public boolean finalIsTrap() {
		throw new UnsupportedOperationException(mUnsupportedOperationMessage);
		// This method can be implemented very easily. There is exactly one
		// final state in each TMA in the looping part (and none in the TMA in
		// the initial part). Such a final state is the initial state of the TMA
		// in which it is contained. If we do not consider the additional
		// transitions from the complementation construction, the initial state
		// does not have any incoming transitions (since it is a copy of τ(ε)),
		// which means that it cannot be its own successor. Furthermore, the
		// initial state has at least one successor per symbol in the alphabet
		// (since the TMA is total). Thus it has non-final successors (they
		// cannot be final because the initial state is the only final state),
		// which means that from any final state a non-final state is reachable.
		//
		// — IMPLEMENTATION ————————————————————————————————————————————————————
		// return false;
		// —————————————————————————————————————————————————————————————————————
	}
	
	@Override
	public boolean isDeterministic() {
		throw new UnsupportedOperationException(mUnsupportedOperationMessage);
		// This method can be implemented very easily. By construction the TMA
		// is always deterministic and total. Thus the complement automaton is
		// deterministic iff none of the TMAs in the looping part are reachable
		// (this also means that the language accepted by the complement
		// automaton is empty).
		//
		// — IMPLEMENTATION ————————————————————————————————————————————————————
		// return mTMA.statesWithLeftRejectingPartners().isEmpty();
		// —————————————————————————————————————————————————————————————————————
	}
	
	@Override
	public boolean isTotal() {
		throw new UnsupportedOperationException(mUnsupportedOperationMessage);
		// This method can be implemented very easily. Since the TMA is always
		// total (by construction), the same holds for the complement automaton.
		//
		// — IMPLEMENTATION ————————————————————————————————————————————————————
		// return true;
		// —————————————————————————————————————————————————————————————————————
	}
	
	@Override
	public Set<LETTER> getCallAlphabet() {
		mLogger.warn("No nwa. Has no call alphabet.");
		return new HashSet<LETTER>(0);
	}
	
	@Override
	public Set<LETTER> getReturnAlphabet() {
		mLogger.warn("No nwa. Has no return alphabet.");
		return new HashSet<LETTER>(0);
	}
	
	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		// mLogger.warn("No nwa. Has no call alphabet.");
		return new HashSet<LETTER>(0);
	}
	
	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		// mLogger.warn("No nwa. Has no return alphabet.");
		return new HashSet<LETTER>(0);
	}
	
	@Override
	public Set<LETTER> lettersCallIncoming(final STATE state) {
		return new HashSet<LETTER>(0);
	}
	
	@Override
	public Set<LETTER> lettersReturnIncoming(final STATE state) {
		return new HashSet<LETTER>(0);
	}
	
	@Override
	public Set<LETTER> lettersSummary(final STATE state) {
		return new HashSet<LETTER>(0);
	}
	
	@Override
	public Collection<STATE> succCall(final STATE state, final LETTER letter) {
		throw new UnsupportedOperationException(mUnsupportedOperationMessage);
	}
	
	@Override
	public Collection<STATE> hierarchicalPredecessorsOutgoing(final STATE state, final LETTER letter) {
		throw new UnsupportedOperationException(mUnsupportedOperationMessage);
	}
	
	@Override
	public Collection<STATE> succReturn(final STATE state, final STATE hier, final LETTER letter) {
		throw new UnsupportedOperationException(mUnsupportedOperationMessage);
	}
	
	@Override
	public Collection<STATE> predCall(final STATE state, final LETTER letter) {
		throw new UnsupportedOperationException(mUnsupportedOperationMessage);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier,
			final LETTER letter) {
		throw new UnsupportedOperationException(mUnsupportedOperationMessage);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(
			final STATE hier) {
		// TODO Auto-generated method stub
		return null;
	}
	
	/**
	 * @return whether {@code state} is known, i.e. if it has already been seen
	 *         by the automaton
	 */
	private boolean knows(final STATE state) {
		return mMapState2MS.containsKey(state);
	}
	
	private MetaState getMetaState(final Integer stateNb, final Integer tmaNb) {
		MetaState metaState = new MetaState(stateNb, tmaNb);
		// If there is already a MetaState object equal to the computed
		// MetaState, use that object instead.
		if (mMapState2MS.containsKey(metaState.mOutputState)) {
			metaState = mMapState2MS.get(metaState.mOutputState);
		} else {
			// Otherwise add this new MetaState to the map.
			mMapState2MS.put(metaState.mOutputState, metaState);
		}
		return metaState;
	}
	
	private MetaState getMetaState(final STATE state) {
		return mMapState2MS.get(state);
	}
	
	/**
	 * Copy of a TMA state indexed by the number of the TMA instance.
	 */
	private final class MetaState {
		// state number inside the TMA
		private final Integer mStateNb;
		// number of the TMA instance
		private final Integer mTmaNb;
		private final STATE mOutputState;
		
		public MetaState(final Integer stateNb, final Integer tmaNb) {
			this.mStateNb = stateNb;
			this.mTmaNb = tmaNb;
			this.mOutputState = mStateFactory.constructBuchiSVWState(stateNb, tmaNb);
		}
		
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((mStateNb == null) ? 0 : mStateNb.hashCode());
			result = prime * result + ((mTmaNb == null) ? 0 : mTmaNb.hashCode());
			return result;
		}
		
		@Override
		@SuppressWarnings("unchecked")
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if ((obj == null) || (this.getClass() != obj.getClass())) {
				return false;
			}
			final MetaState other = (MetaState) obj;
			if ((mStateNb == null) && (other.mStateNb != null)) {
				return false;
			}
			if ((mTmaNb == null) && (other.mTmaNb != null)) {
				return false;
			}
			return mStateNb.equals(other.mStateNb) && mTmaNb.equals(other.mTmaNb);
		}
	}
	
	// ═════════════════════════════════════════════════════════════════════════
	//
	private class TransitionMonoidAutomaton {
		
		// number assigned to copy of τ(ε)
		public Integer mInitialState = 0;
		public Integer mInitialTMA = mInitialState;
		
		private final INestedWordAutomaton<LETTER, STATE> mOrigAutomaton;
		
		// Transitions
		private final Map<Integer, Map<LETTER, Integer>> mTransitionsOut =
				new HashMap<>();
		private final Map<Integer, Map<LETTER, Set<Integer>>> mTransitionsIn =
				new HashMap<>();
				
		// Rejecting s-t pairs
		private final Map<Integer, Set<Integer>> mRejectingPairsL2R;
		private final Map<Integer, Set<Integer>> mRejectingPairsR2L;
		
		private Set<Integer> mStatesWithLeftRejectingPartners = null;
		
		/**
		 * Precomputes all the transitions and rejecting s-t-pairs and then
		 * forgets about the underlying transition profiles. After that, states
		 * are simply represented by Integer objects.
		 */
		public TransitionMonoidAutomaton(final INestedWordAutomaton<LETTER, STATE> origAutomaton)
				throws AutomataOperationCanceledException {
			mOrigAutomaton = origAutomaton;
			final Collection<LETTER> alphabet = origAutomaton.getInternalAlphabet();
			
			// Map from numbers to corresponding transition profiles
			final Map<Integer, TransitionProfile> mapNum2TP = new HashMap<Integer, TransitionProfile>();
			// Map for the reverse direction
			final Map<TransitionProfile, Integer> mapTP2Num = new HashMap<TransitionProfile, Integer>();
			
			// Map from letters to their corresponding transition profiles
			// (to avoid recomputing them many times)
			final Map<LETTER, TransitionProfile> mapLetter2TP = new HashMap<LETTER, TransitionProfile>();
			for (final LETTER a : alphabet) {
				mapLetter2TP.put(a, new TransitionProfile(a));
			}
			// Build the automaton (i.e. compute the transitions)
			final int i_init = mInitialState; // i.e. i_init = 0
			final TransitionProfile t_init = new TransitionProfile(); // τ(ε)-copy
			mapNum2TP.put(i_init, t_init);
			mapTP2Num.put(t_init, i_init);
			mTransitionsOut.put(i_init, new HashMap<LETTER, Integer>());
			mTransitionsIn.put(i_init, new HashMap<LETTER, Set<Integer>>());
			int numOfStates = 1;
			for (int i_curr = i_init; i_curr < numOfStates; ++i_curr) {
				final TransitionProfile t_curr = mapNum2TP.get(i_curr);
				for (final LETTER a : alphabet) {
					// t_next = t_curr·τ(a)
					final TransitionProfile t_next = new TransitionProfile(t_curr, mapLetter2TP.get(a));
					Integer i_next = mapTP2Num.get(t_next);
					// If i_next not yet known, add new entries for it.
					if (i_next == null) {
						i_next = numOfStates;
						++numOfStates;
						mapNum2TP.put(i_next, t_next);
						mapTP2Num.put(t_next, i_next);
						mTransitionsOut.put(i_next, new HashMap<LETTER, Integer>());
						mTransitionsIn.put(i_next, new HashMap<LETTER, Set<Integer>>());
					}
					// δ(i_curr, a) = i_next
					mTransitionsOut.get(i_curr).put(a, i_next);
					// i_curr ∈ δ⁻¹(i_next, a)
					Set<Integer> preds = mTransitionsIn.get(i_next).get(a);
					if (preds == null) {
						preds = new HashSet<Integer>();
						mTransitionsIn.get(i_next).put(a, preds);
					}
					preds.add(i_curr);
				}
			}
			
			// Compute rejecting s-t pairs
			final List<TransitionProfile> idempotents = new ArrayList<TransitionProfile>();
			for (final TransitionProfile t : mapTP2Num.keySet()) {
				if (t.isIdempotent()) {
					idempotents.add(t);
				}
			}
			mRejectingPairsL2R = new HashMap<Integer, Set<Integer>>(numOfStates);
			mRejectingPairsR2L = new HashMap<Integer, Set<Integer>>(numOfStates);
			for (int i_s = i_init; i_s < numOfStates; ++i_s) {
				mRejectingPairsL2R.put(i_s, new HashSet<Integer>(0));
				mRejectingPairsR2L.put(i_s, new HashSet<Integer>(0));
			}
			for (int i_s = i_init; i_s < numOfStates; ++i_s) {
				if (!mServices.getProgressMonitorService().continueProcessing()) {
					throw new AutomataOperationCanceledException(this.getClass());
				}
				
				final TransitionProfile s = mapNum2TP.get(i_s);
				final Set<Integer> rightRejectingPartners_s = mRejectingPairsL2R.get(i_s);
				for (final TransitionProfile t : idempotents) {
					// If ⟨s,t⟩ ∈ s-t-Pairs ∧ L(⟨s,t⟩) ∩ L_ω(A) = ∅
					if (s.isInvariantUnder(t) && !s.hasAcceptingLasso(t)) {
						final Integer i_t = mapTP2Num.get(t);
						final Set<Integer> leftRejectingPartners_t = mRejectingPairsR2L.get(i_t);
						rightRejectingPartners_s.add(i_t);
						leftRejectingPartners_t.add(i_s);
					}
				}
			}
		}
		
		/**
		 * @return The total number of states.
		 */
		public int size() {
			return mTransitionsOut.size();
		}
		
		/**
		 * @return the (unique) successor of {@code state} under letter
		 *         {@code a}, i.e. δ(state, a)
		 */
		public Integer successor(final Integer state, final LETTER a) {
			return mTransitionsOut.get(state).get(a);
		}
		
		/**
		 * @return the set of predecessors of {@code state} under letter
		 *         {@code a}, i.e. δ⁻¹(state, a)
		 */
		public Set<Integer> predecessors(final Integer state, final LETTER a) {
			return mTransitionsIn.get(state).get(a);
		}
		
		/**
		 * @return the largest set of states such that for any included state qₜ
		 *         it holds that ⟨s,t⟩ is a rejecting s-t-pair, where
		 *         <ul>
		 *         <li>
		 *         s is the TP corresponding to {@code state}</li>
		 *         <li>
		 *         t is the TP corresponding to qₜ</li>
		 *         </ul>
		 */
		public Set<Integer> rightRejectingPartners(final Integer state) {
			return mRejectingPairsL2R.get(state);
		}
		
		/**
		 * @return the largest set of states such that for any included state qₛ
		 *         it holds that ⟨s,t⟩ is a rejecting s-t-pair, where
		 *         <ul>
		 *         <li>
		 *         s is the TP corresponding to qₛ</li>
		 *         <li>
		 *         t is the TP corresponding to {@code state}</li>
		 *         </ul>
		 */
		public Set<Integer> leftRejectingPartners(final Integer state) {
			return mRejectingPairsR2L.get(state);
		}
		
		/**
		 * @return the set of states for which {@code leftRejectingPartners()}
		 *         would return a nonempty set
		 */
		public Set<Integer> statesWithLeftRejectingPartners() {
			if (mStatesWithLeftRejectingPartners == null) {
				mStatesWithLeftRejectingPartners = new HashSet<Integer>();
				for (final Entry<Integer, Set<Integer>> e : mRejectingPairsR2L.entrySet()) {
					if (!e.getValue().isEmpty()) {
						mStatesWithLeftRejectingPartners.add(e.getKey());
					}
				}
			}
			return mStatesWithLeftRejectingPartners;
		}
		
		private class TransitionProfile {
			private boolean mIsInitial = false; // only true for the copy of τ(ε)
			private final Map<Transition, Boolean> mTransitions =
					new HashMap<Transition, Boolean>();
					
			/**
			 * @return The copy of the transition profile τ(ε), i.e. the initial
			 *         state of the TMA.
			 */
			public TransitionProfile() {
				mIsInitial = true;
				for (final STATE q : mOrigAutomaton.getStates()) {
					if (mOrigAutomaton.isFinal(q)) {
						mTransitions.put(new Transition(q, q), true);
					} else {
						mTransitions.put(new Transition(q, q), false);
					}
				}
			}
			
			/**
			 * @return The transition profile τ(a) for letter {@code a}.
			 */
			public TransitionProfile(final LETTER a) {
				for (final STATE p : mOrigAutomaton.getStates()) {
					final boolean p_isFinal = mOrigAutomaton.isFinal(p);
					for (final OutgoingInternalTransition<LETTER, STATE> trans : mOrigAutomaton.internalSuccessors(p,
							a)) {
						final STATE q = trans.getSucc();
						if (p_isFinal || mOrigAutomaton.isFinal(q)) {
							mTransitions.put(new Transition(p, q), true);
						} else {
							mTransitions.put(new Transition(p, q), false);
						}
					}
				}
			}
			
			/**
			 * @return The transition profile for the concatenation s·t.
			 */
			public TransitionProfile(final TransitionProfile s, final TransitionProfile t) {
				for (final Transition trans1 : s.mTransitions.keySet()) {
					for (final Transition trans2 : t.mTransitions.keySet()) {
						if (trans1.mQ2.equals(trans2.mQ1)) {
							final Transition trans1x2 = new Transition(trans1.mQ1, trans2.mQ2);
							if (s.mTransitions.get(trans1) || t.mTransitions.get(trans2)) {
								mTransitions.put(trans1x2, true);
							} else if (!this.mTransitions.containsKey(trans1x2)) {
								mTransitions.put(trans1x2, false);
							}
						}
					}
				}
			}
			
			/**
			 * @return Whether s·t = s, where s = {@code this}.
			 */
			public boolean isInvariantUnder(final TransitionProfile t) {
				return (new TransitionProfile(this, t).equals(this));
			}
			
			/**
			 * @return Whether t·t = t, where t = {@code this}.
			 */
			public boolean isIdempotent() {
				return (new TransitionProfile(this, this).equals(this));
			}
			
			/**
			 * @return whether L(⟨s,t⟩) ⊆ L_ω(A), where s = {@code this} <br>
			 *         Assumes that ⟨s,t⟩ is an s-t-pair, i.e. that L(⟨s,t⟩) is
			 *         “proper”.
			 */
			public boolean hasAcceptingLasso(final TransitionProfile t) {
				for (final Transition trans1 : this.mTransitions.keySet()) {
					if (mOrigAutomaton.isInitial(trans1.mQ1)) {
						final Transition trans2 = new Transition(trans1.mQ2, trans1.mQ2);
						if (t.mTransitions.containsKey(trans2) && t.mTransitions.get(trans2)) {
							return true;
						}
					}
				}
				return false;
			}
			
			@Override
			public int hashCode() {
				final int prime = 31;
				int result = 1;
				result = prime * result + ((mTransitions == null) ? 0 : mTransitions.hashCode());
				return result;
			}
			
			@Override
			@SuppressWarnings("unchecked")
			public boolean equals(final Object obj) {
				if (this == obj) {
					return true;
				}
				if ((obj == null) || (this.getClass() != obj.getClass())) {
					return false;
				}
				final TransitionProfile other = (TransitionProfile) obj;
				if (mTransitions == null) {
					return (other.mTransitions == null);
				}
				return mTransitions.equals(other.mTransitions)
						&& mIsInitial == other.mIsInitial;
			}
		}
		
		/**
		 * Transitions are the basic building blocks of transition profiles.
		 * They are implemented as tuples of states.
		 */
		private final class Transition {
			private final STATE mQ1;
			private final STATE mQ2;
			
			public Transition(final STATE q1, final STATE q2) {
				this.mQ1 = q1;
				this.mQ2 = q2;
			}
			
			@Override
			public int hashCode() {
				final int prime = 31;
				int result = 1;
				result = prime * result + ((mQ1 == null) ? 0 : mQ1.hashCode());
				result = prime * result + ((mQ2 == null) ? 0 : mQ2.hashCode());
				return result;
			}
			
			@SuppressWarnings("unchecked")
			@Override
			public boolean equals(final Object obj) {
				if (this == obj) {
					return true;
				}
				if ((obj == null) || (this.getClass() != obj.getClass())) {
					return false;
				}
				final Transition other = (Transition) obj;
				if ((mQ1 == null) && (other.mQ1 != null)) {
					return false;
				}
				if ((mQ2 == null) && (other.mQ2 != null)) {
					return false;
				}
				return mQ1.equals(other.mQ1) && mQ2.equals(other.mQ2);
			}
		}
	}
	
	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final STATE succ, final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final STATE succ) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final STATE succ, final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final STATE succ) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state, final LETTER letter) {
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result =
				new ArrayList<OutgoingInternalTransition<LETTER, STATE>>();
		for (final STATE succ : succInternal(state, letter)) {
			result.add(new OutgoingInternalTransition<LETTER, STATE>(letter, succ));
		}
		return result;
	}
	
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state) {
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result =
				new ArrayList<OutgoingInternalTransition<LETTER, STATE>>();
		for (final LETTER letter : lettersInternal(state)) {
			for (final STATE succ : succInternal(state, letter)) {
				result.add(new OutgoingInternalTransition<LETTER, STATE>(letter, succ));
			}
		}
		return result;
	}
	
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state, final LETTER letter) {
		return new ArrayList<OutgoingCallTransition<LETTER, STATE>>();
	}
	
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state) {
		return new ArrayList<OutgoingCallTransition<LETTER, STATE>>();
	}
	
	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ, final STATE hier, final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ, final LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final STATE hier, final LETTER letter) {
		return new ArrayList<OutgoingReturnTransition<LETTER, STATE>>();
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final LETTER letter) {
		return new ArrayList<OutgoingReturnTransition<LETTER, STATE>>();
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state) {
		return new ArrayList<OutgoingReturnTransition<LETTER, STATE>>();
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			final STATE state, final STATE hier) {
		return new ArrayList<OutgoingReturnTransition<LETTER, STATE>>();
	}
}
