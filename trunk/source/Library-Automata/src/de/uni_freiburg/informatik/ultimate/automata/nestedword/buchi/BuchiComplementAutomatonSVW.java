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
import java.util.Collections;
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
 * Automaton that is returned as the result of the {@link BuchiComplementSVW}
 * operation. States and transitions are built on the fly.
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
public class BuchiComplementAutomatonSVW<LETTER, STATE> implements INestedWordAutomaton<LETTER, STATE> {
	private static final String IS_NOT_YET_KNOWN = " is not (yet) known.";
	private static final String STATE_STRING = "State ";
	private static final String UNSUPPORTED_OPERATION_MESSAGE = "Transform to NestedWordAutomaton to get full support.";
	protected final IStateFactory<STATE> mStateFactory;
	protected final STATE mEmptyStackState;
	protected final AutomataLibraryServices mServices;
	private final TransitionMonoidAutomaton mTma;
	private final Set<LETTER> mAlphabet;
	private SizeInfoContainer mSizeInfo;
	// not all transitions have been computed
	private boolean mBuildCompleted;
	private final STATE mInitialState;
	// only one
	private final Set<STATE> mInitialStateSet = new HashSet<>(1);
	private final Set<STATE> mFinalStateSet = null;
	private final Map<STATE, Map<LETTER, Set<STATE>>> mTransitionsOut = new HashMap<>();
	private final Map<STATE, Map<LETTER, Set<STATE>>> mTransitionsIn = new HashMap<>();
	private final Map<STATE, MetaState> mMapState2Ms = new HashMap<>();
	
	private final ILogger mLogger;
	
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public BuchiComplementAutomatonSVW(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mTma = new TransitionMonoidAutomaton(operand);
		mAlphabet = operand.getInternalAlphabet();
		if (!operand.getCallAlphabet().isEmpty() || !operand.getReturnAlphabet().isEmpty()) {
			throw new IllegalArgumentException("only applicable to Buchi automata (not BuchiNWA)");
		}
		mStateFactory = operand.getStateFactory();
		mEmptyStackState = mStateFactory.createEmptyStackState();
		final MetaState metaInitialState = getMetaState1(mTma.getInitialState(), mTma.getInitialTma());
		mInitialState = metaInitialState.getOutputState();
		mInitialStateSet.add(mInitialState);
	}
	
	/**
	 * @return an equivalent {@code NestedWordAutomaton} object <br>
	 *         <b>Use with caution!</b> The automaton has to be computed
	 *         entirely.
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public INestedWordAutomaton<LETTER, STATE> toNestedWordAutomaton() throws AutomataOperationCanceledException {
		final NestedWordAutomaton<LETTER, STATE> result =
				new NestedWordAutomaton<>(mServices, mAlphabet, null, null, mStateFactory);
		final int size = getSizeInfo().mTotalSize;
		// Breadth-first traversal of the state space.
		final Set<STATE> alreadySeen = new HashSet<>(size);
		final Queue<STATE> queue = new LinkedList<>();
		alreadySeen.add(mInitialState);
		queue.add(mInitialState);
		result.addState(true, false, mInitialState);
		while (!queue.isEmpty()) {
			final STATE state = queue.remove();
			for (final LETTER letter : mAlphabet) {
				final Collection<STATE> succSet = succInternal(state, letter);
				for (final STATE succState : succSet) {
					addIfNotContained1(result, alreadySeen, queue, succState);
					result.addInternalTransition(state, letter, succState);
				}
			}
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}
		}
		// side effect of the BF traversal
		mBuildCompleted = true;
		return result;
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
		// @formatter:off
		sb.append("has ")
			.append(sizeInfo.mTotalSize)
			.append(" states. Size of a transition monoid automaton (TMA): ")
			.append(sizeInfo.mTmaSize)
			.append(". Number of reachable TMAs: ")
			.append(sizeInfo.mNumOfReachableTmas)
			.append('.');
		// @formatter:on
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
		if (mBuildCompleted) {
			return mTransitionsOut.keySet();
		}
		final int size = getSizeInfo().mTotalSize;
		// Breadth-first traversal of the state space.
		final Set<STATE> alreadySeen = new HashSet<>(size);
		final Queue<STATE> queue = new LinkedList<>();
		alreadySeen.add(mInitialState);
		queue.add(mInitialState);
		while (!queue.isEmpty()) {
			final STATE state = queue.remove();
			for (final LETTER letter : mAlphabet) {
				final Collection<STATE> succSet = succInternal(state, letter);
				for (final STATE succState : succSet) {
					addIfNotContained2(alreadySeen, queue, succState);
				}
			}
			// TODO: Uncomment the following, once getStates() in
			// INestedWordAutomaton has "throws OperationCanceledException"
			// ------------------------------------------------------------
			// if (!mUltiServ.continueProcessing()) {
			// throw new OperationCanceledException();
			// }
			// ------------------------------------------------------------
		}
		mBuildCompleted = true;
		return mTransitionsOut.keySet();
	}
	
	@Override
	public Set<STATE> getInitialStates() {
		return mInitialStateSet;
	}
	
	@Override
	public Collection<STATE> getFinalStates() {
		if (mFinalStateSet == null) {
			final Set<Integer> reachableTmas = mTma.statesWithLeftRejectingPartners();
			for (final Integer tmaNb : reachableTmas) {
				final MetaState metaState = getMetaState1(mTma.getInitialState(), tmaNb);
				/**
				 * Christian 2016-08-16: BUG: mFinalStateSet is null here because it is ALWAYS null.
				 */
				mFinalStateSet.add(metaState.getOutputState());
			}
		}
		return mFinalStateSet;
	}
	
	@Override
	public boolean isInitial(final STATE state) {
		if (!knows(state)) {
			throw new IllegalArgumentException(STATE_STRING + state + IS_NOT_YET_KNOWN);
		}
		return state.equals(mInitialState);
	}
	
	@Override
	public boolean isFinal(final STATE state) {
		final MetaState metaState = getMetaState2(state);
		if (metaState == null) {
			throw new IllegalArgumentException(STATE_STRING + state + IS_NOT_YET_KNOWN);
		}
		return metaState.getStateNb().equals(mTma.getInitialState())
				&& !metaState.getTmaNb().equals(mTma.getInitialTma());
	}
	
	@Override
	public STATE getEmptyStackState() {
		return this.mEmptyStackState;
	}
	
	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		if (!knows(state)) {
			throw new IllegalArgumentException(STATE_STRING + state + IS_NOT_YET_KNOWN);
		}
		return mAlphabet;
	}
	
	@Override
	public Set<LETTER> lettersInternalIncoming(final STATE state) {
		if (!knows(state)) {
			throw new IllegalArgumentException(STATE_STRING + state + IS_NOT_YET_KNOWN);
		}
		final Set<LETTER> result = new HashSet<>();
		for (final LETTER letter : mAlphabet) {
			final Collection<STATE> predStateSet = predInternal(state, letter);
			if (!predStateSet.isEmpty()) {
				result.add(letter);
			}
		}
		return result;
	}
	
	private Collection<STATE> succInternal(final STATE state, final LETTER letter) {
		Map<LETTER, Set<STATE>> map = mTransitionsOut.get(state);
		if (map == null) {
			map = new HashMap<>();
			mTransitionsOut.put(state, map);
		}
		Set<STATE> result = map.get(letter);
		// If the result is not in the map, compute it.
		if (result == null) {
			if (!mAlphabet.contains(letter)) {
				throw new IllegalArgumentException("Letter " + letter + " is not in the alphabet.");
			}
			final MetaState mState = getMetaState2(state);
			if (mState == null) {
				throw new IllegalArgumentException(STATE_STRING + state + IS_NOT_YET_KNOWN);
			}
			result = new HashSet<>();
			map.put(letter, result);
			final Set<MetaState> mResult = new HashSet<>();
			// Add the (unique) successor that is in the same TMA.
			final Integer succStateNb = mTma.successor(mState.getStateNb(), letter);
			mResult.add(getMetaState1(succStateNb, mState.getTmaNb()));
			// If we are in the initial TMA, we have to add transitions to the
			// initial states of some of the TMAs in the looping part of the
			// complement automaton.
			if (mState.getTmaNb().equals(mTma.getInitialTma())) {
				for (final Integer otherTmaNb : mTma.rightRejectingPartners(succStateNb)) {
					mResult.add(getMetaState1(mTma.getInitialState(), otherTmaNb));
				}
			} else {
				// Otherwise we are in a TMA in the looping part. If we can reach
				// the final state (of this TMA), we have to add a transition that
				// loops back to the initial state.
				if (succStateNb.equals(mState.getTmaNb())) {
					mResult.add(getMetaState1(mTma.getInitialState(), mState.getTmaNb()));
				}
			}
			// Convert set of MetaStates to set of STATEs.
			for (final MetaState succState : mResult) {
				result.add(succState.getOutputState());
			}
		}
		return result;
	}
	
	private Collection<STATE> predInternal(final STATE state, final LETTER letter) {
		Map<LETTER, Set<STATE>> map = mTransitionsIn.get(state);
		if (map == null) {
			map = new HashMap<>();
			mTransitionsIn.put(state, map);
		}
		Set<STATE> result = map.get(letter);
		// If the result is not in the map, compute it.
		if (result != null) {
			return result;
		}
		if (!mAlphabet.contains(letter)) {
			throw new IllegalArgumentException("Letter " + letter + " is not in the alphabet.");
		}
		final MetaState mState = getMetaState2(state);
		if (mState == null) {
			throw new IllegalArgumentException(STATE_STRING + state + IS_NOT_YET_KNOWN);
		}
		result = new HashSet<>();
		map.put(letter, result);
		// Add the predecessors inherited from the TMA.
		final Set<Integer> predStateNbSet = mTma.predecessors(mState.getStateNb(), letter);
		if (predStateNbSet == null) {
			throw new AssertionError(
					"20160830 Matthias: This NPE is a known and old bug."
							+ " I will fix it only when I revise the Ramsey-based complementation.");
		}
		final Set<MetaState> mResult = new HashSet<>();
		for (final Integer predStateNb : predStateNbSet) {
			mResult.add(getMetaState1(predStateNb, mState.getTmaNb()));
		}
		// If state is the initial state of a TMA in the looping part of the
		// complement automaton, we have to add the transitions from the
		// initial part and those from within the same TMA that loop back to
		// the initial state.
		if (mState.getStateNb().equals(mTma.getInitialState()) && !mState.getTmaNb().equals(mTma.getInitialTma())) {
			// Transitions from the initial part
			final Set<Integer> leftRejectingPartnerSet = mTma.leftRejectingPartners(mState.getTmaNb());
			for (final Integer leftRejectingPartner : leftRejectingPartnerSet) {
				final Set<Integer> predOfLrpSet = mTma.predecessors(leftRejectingPartner, letter);
				for (final Integer predOfLrp : predOfLrpSet) {
					mResult.add(getMetaState1(predOfLrp, mTma.mInitialTma));
				}
			}
			// Back loops from within the same TMA
			final Set<Integer> predOfTerminalSet = mTma.predecessors(mState.getTmaNb(), letter);
			for (final Integer predOfTerminal : predOfTerminalSet) {
				mResult.add(getMetaState1(predOfTerminal, mState.getTmaNb()));
			}
		}
		// Convert set of MetaStates to set of STATEs.
		for (final MetaState predState : mResult) {
			result.add(predState.getOutputState());
		}
		return result;
	}
	
	private static boolean finalIsTrap() {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
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
		// - IMPLEMENTATION ----------------------------------------------------
		// return false;
		// ---------------------------------------------------------------------
	}
	
	private static boolean isDeterministic() {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
		// This method can be implemented very easily. By construction the TMA
		// is always deterministic and total. Thus the complement automaton is
		// deterministic iff none of the TMAs in the looping part are reachable
		// (this also means that the language accepted by the complement
		// automaton is empty).
		//
		// - IMPLEMENTATION ----------------------------------------------------
		// return mTMA.statesWithLeftRejectingPartners().isEmpty();
		// ---------------------------------------------------------------------
	}
	
	private static boolean isTotal() {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
		// This method can be implemented very easily. Since the TMA is always
		// total (by construction), the same holds for the complement automaton.
		//
		// - IMPLEMENTATION ----------------------------------------------------
		// return true;
		// ---------------------------------------------------------------------
	}
	
	@Override
	public Set<LETTER> getCallAlphabet() {
		if (mLogger.isWarnEnabled()) {
			mLogger.warn("No nwa. Has no call alphabet.");
		}
		return Collections.emptySet();
	}
	
	@Override
	public Set<LETTER> getReturnAlphabet() {
		if (mLogger.isWarnEnabled()) {
			mLogger.warn("No nwa. Has no return alphabet.");
		}
		return Collections.emptySet();
	}
	
	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		// mLogger.warn("No nwa. Has no call alphabet.");
		return Collections.emptySet();
	}
	
	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		// mLogger.warn("No nwa. Has no return alphabet.");
		return Collections.emptySet();
	}
	
	@Override
	public Set<LETTER> lettersCallIncoming(final STATE state) {
		return Collections.emptySet();
	}
	
	@Override
	public Set<LETTER> lettersReturnIncoming(final STATE state) {
		return Collections.emptySet();
	}
	
	@Override
	public Set<LETTER> lettersSummary(final STATE state) {
		return Collections.emptySet();
	}
	
	@Override
	public Collection<STATE> hierarchicalPredecessorsOutgoing(final STATE state, final LETTER letter) {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier, final LETTER letter) {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier) {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
	}
	
	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ,
			final LETTER letter) {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
	}
	
	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ) {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
	}
	
	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ, final LETTER letter) {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
	}
	
	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ) {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
	}
	
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final STATE succ : succInternal(state, letter)) {
			result.add(new OutgoingInternalTransition<>(letter, succ));
		}
		return result;
	}
	
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final LETTER letter : lettersInternal(state)) {
			for (final STATE succ : succInternal(state, letter)) {
				result.add(new OutgoingInternalTransition<>(letter, succ));
			}
		}
		return result;
	}
	
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		return Collections.emptyList();
	}
	
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		return Collections.emptyList();
	}
	
	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final STATE hier,
			final LETTER letter) {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
	}
	
	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final LETTER letter) {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
	}
	
	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ) {
		throw new UnsupportedOperationException(UNSUPPORTED_OPERATION_MESSAGE);
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		return Collections.emptyList();
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final LETTER letter) {
		return Collections.emptyList();
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state) {
		return Collections.emptyList();
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		return Collections.emptyList();
	}
	
	private SizeInfoContainer getSizeInfo() {
		if (mSizeInfo == null) {
			// Number of states per TMA:
			final int m = mTma.size();
			// Number of reachable TMAs (initial + looping part):
			final int r = mTma.statesWithLeftRejectingPartners().size() + 1;
			// Total number of states:
			final int totalSize = r * m;
			
			mSizeInfo = new SizeInfoContainer(m, r, totalSize);
		}
		return mSizeInfo;
	}
	
	/**
	 * @return whether {@code state} is known, i.e. if it has already been seen
	 *         by the automaton
	 */
	private boolean knows(final STATE state) {
		return mMapState2Ms.containsKey(state);
	}
	
	private MetaState getMetaState1(final Integer stateNb, final Integer tmaNb) {
		MetaState metaState = new MetaState(stateNb, tmaNb);
		// If there is already a MetaState object equal to the computed
		// MetaState, use that object instead.
		if (mMapState2Ms.containsKey(metaState.getOutputState())) {
			metaState = mMapState2Ms.get(metaState.getOutputState());
		} else {
			// Otherwise add this new MetaState to the map.
			mMapState2Ms.put(metaState.getOutputState(), metaState);
		}
		return metaState;
	}
	
	private MetaState getMetaState2(final STATE state) {
		return mMapState2Ms.get(state);
	}
	
	private void addIfNotContained1(final NestedWordAutomaton<LETTER, STATE> result, final Set<STATE> alreadySeen,
			final Queue<STATE> queue, final STATE succState) {
		if (!alreadySeen.contains(succState)) {
			alreadySeen.add(succState);
			queue.add(succState);
			if (isFinal(succState)) {
				result.addState(false, true, succState);
			} else {
				result.addState(false, false, succState);
			}
		}
	}
	
	private void addIfNotContained2(final Set<STATE> alreadySeen, final Queue<STATE> queue, final STATE succState) {
		if (!alreadySeen.contains(succState)) {
			alreadySeen.add(succState);
			queue.add(succState);
		}
	}
	
	/**
	 * Container for size info.
	 * 
	 * @author Fabian Reiter
	 */
	private static class SizeInfoContainer {
		protected final int mTotalSize;
		protected final int mTmaSize;
		protected final int mNumOfReachableTmas;
		
		public SizeInfoContainer(final int tmaSize, final int numOfReachableTmas, final int totalSize) {
			mTmaSize = tmaSize;
			mNumOfReachableTmas = numOfReachableTmas;
			mTotalSize = totalSize;
		}
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
			mStateNb = stateNb;
			mTmaNb = tmaNb;
			mOutputState = mStateFactory.constructBuchiSVWState(stateNb, tmaNb);
		}
		
		Integer getStateNb() {
			return mStateNb;
		}
		
		Integer getTmaNb() {
			return mTmaNb;
		}
		
		STATE getOutputState() {
			return mOutputState;
		}
		
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = prime + ((mStateNb == null) ? 0 : mStateNb.hashCode());
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
			if (mStateNb == null) {
				if (other.mStateNb != null) {
					return false;
				}
			} else if (!mStateNb.equals(other.mStateNb)) {
				return false;
			}
			if (mTmaNb == null) {
				if (other.mTmaNb != null) {
					return false;
				}
			} else if (!mTmaNb.equals(other.mTmaNb)) {
				return false;
			}
			return true;
		}
	}
	
	// =========================================================================
	//
	/**
	 * Transition monoid automaton.
	 * 
	 * @author Fabian Reiter
	 */
	private class TransitionMonoidAutomaton {
		// number assigned to copy of τ(ε)
		private final Integer mInitialStateTma = Integer.valueOf(0);
		
		private final Integer mInitialTma = mInitialStateTma;
		
		private final INestedWordAutomaton<LETTER, STATE> mOrigAutomaton;
		
		// Transitions
		private final Map<Integer, Map<LETTER, Integer>> mTransitionsOutTma = new HashMap<>();
		private final Map<Integer, Map<LETTER, Set<Integer>>> mTransitionsInTma = new HashMap<>();
		
		// Rejecting s-t pairs
		private final Map<Integer, Set<Integer>> mRejectingPairsL2R;
		private final Map<Integer, Set<Integer>> mRejectingPairsR2L;
		
		private Set<Integer> mStatesWithLeftRejectingPartners;
		
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
			final Map<Integer, TransitionProfile> mapNum2Tp = new HashMap<>();
			// Map for the reverse direction
			final Map<TransitionProfile, Integer> mapTp2Num = new HashMap<>();
			
			// Map from letters to their corresponding transition profiles
			// (to avoid recomputing them many times)
			final Map<LETTER, TransitionProfile> mapLetter2Tp = new HashMap<>();
			for (final LETTER a : alphabet) {
				mapLetter2Tp.put(a, new TransitionProfile(a));
			}
			/* Build the automaton (i.e. compute the transitions) */
			// i.e. i_init = 0
			final Integer iInit = mInitialStateTma;
			final TransitionProfile tInit = new TransitionProfile(); // τ(ε)-copy
			mapNum2Tp.put(iInit, tInit);
			mapTp2Num.put(tInit, iInit);
			mTransitionsOutTma.put(iInit, new HashMap<LETTER, Integer>());
			mTransitionsInTma.put(iInit, new HashMap<LETTER, Set<Integer>>());
			int numOfStates = 1;
			for (Integer iCurr = iInit; iCurr < numOfStates; ++iCurr) {
				final TransitionProfile tCurr = mapNum2Tp.get(iCurr);
				for (final LETTER a : alphabet) {
					// t_next = t_curr·τ(a)
					final TransitionProfile tNext = new TransitionProfile(tCurr, mapLetter2Tp.get(a));
					Integer iNext = mapTp2Num.get(tNext);
					// If i_next not yet known, add new entries for it.
					if (iNext == null) {
						iNext = numOfStates;
						++numOfStates;
						mapNum2Tp.put(iNext, tNext);
						mapTp2Num.put(tNext, iNext);
						mTransitionsOutTma.put(iNext, new HashMap<LETTER, Integer>());
						mTransitionsInTma.put(iNext, new HashMap<LETTER, Set<Integer>>());
					}
					// δ(i_curr, a) = i_next
					mTransitionsOutTma.get(iCurr).put(a, iNext);
					// i_curr ∈ δ⁻¹(i_next, a)
					Set<Integer> preds = mTransitionsInTma.get(iNext).get(a);
					if (preds == null) {
						preds = new HashSet<>();
						mTransitionsInTma.get(iNext).put(a, preds);
					}
					preds.add(iCurr);
				}
			}
			
			// Compute rejecting s-t pairs
			final List<TransitionProfile> idempotents = new ArrayList<>();
			for (final TransitionProfile t : mapTp2Num.keySet()) {
				if (t.isIdempotent()) {
					idempotents.add(t);
				}
			}
			mRejectingPairsL2R = new HashMap<>(numOfStates);
			mRejectingPairsR2L = new HashMap<>(numOfStates);
			for (int iState = iInit; iState < numOfStates; ++iState) {
				mRejectingPairsL2R.put(iState, new HashSet<>(0));
				mRejectingPairsR2L.put(iState, new HashSet<>(0));
			}
			for (Integer iState = iInit; iState < numOfStates; ++iState) {
				if (!mServices.getProgressAwareTimer().continueProcessing()) {
					throw new AutomataOperationCanceledException(this.getClass());
				}
				
				final TransitionProfile s = mapNum2Tp.get(iState);
				final Set<Integer> rightRejectingPartnersS = mRejectingPairsL2R.get(iState);
				for (final TransitionProfile t : idempotents) {
					// If ⟨s,t⟩ ∈ s-t-Pairs ∧ L(⟨s,t⟩) ∩ L_ω(A) = ∅
					if (s.isInvariantUnder(t) && !s.hasAcceptingLasso(t)) {
						final Integer iTp = mapTp2Num.get(t);
						final Set<Integer> leftRejectingPartnersT = mRejectingPairsR2L.get(iTp);
						rightRejectingPartnersS.add(iTp);
						leftRejectingPartnersT.add(iState);
					}
				}
			}
		}
		
		public Integer getInitialState() {
			return mInitialStateTma;
		}
		
		public Integer getInitialTma() {
			return mInitialTma;
		}
		
		protected INestedWordAutomaton<LETTER, STATE> getOrigAutomaton() {
			return mOrigAutomaton;
		}
		
		/**
		 * @return The total number of states.
		 */
		public int size() {
			return mTransitionsOutTma.size();
		}
		
		/**
		 * @param state state
		 * @param letter letter
		 * @return the (unique) successor of {@code state} under letter
		 *         {@code letter}, i.e. δ(state, letter)
		 */
		public Integer successor(final Integer state, final LETTER letter) {
			return mTransitionsOutTma.get(state).get(letter);
		}
		
		/**
		 * @param state state
		 * @param letter letter
		 * @return the set of predecessors of {@code state} under letter
		 *         {@code letter}, i.e. δ⁻¹(state, letter)
		 */
		public Set<Integer> predecessors(final Integer state, final LETTER letter) {
			return mTransitionsInTma.get(state).get(letter);
		}
		
		/**
		 * @param state state
		 * @return The largest set of states such that for any included state qₜ
		 *         it holds that ⟨s,t⟩ is a rejecting s-t-pair, where
		 *         <ul>
		 *         <li>
		 *         s is the TP corresponding to {@code state}</li>
		 *         <li>
		 *         t is the TP corresponding to qₜ.</li>
		 *         </ul>
		 */
		public Set<Integer> rightRejectingPartners(final Integer state) {
			return mRejectingPairsL2R.get(state);
		}
		
		/**
		 * @param state state
		 * @return The largest set of states such that for any included state qₛ
		 *         it holds that ⟨s,t⟩ is a rejecting s-t-pair, where
		 *         <ul>
		 *         <li>
		 *         s is the TP corresponding to qₛ</li>
		 *         <li>
		 *         t is the TP corresponding to {@code state}.</li>
		 *         </ul>
		 */
		public Set<Integer> leftRejectingPartners(final Integer state) {
			return mRejectingPairsR2L.get(state);
		}
		
		/**
		 * @return The set of states for which {@code leftRejectingPartners()}
		 *         would return a nonempty set.
		 */
		public Set<Integer> statesWithLeftRejectingPartners() {
			if (mStatesWithLeftRejectingPartners == null) {
				mStatesWithLeftRejectingPartners = new HashSet<>();
				for (final Entry<Integer, Set<Integer>> e : mRejectingPairsR2L.entrySet()) {
					if (!e.getValue().isEmpty()) {
						mStatesWithLeftRejectingPartners.add(e.getKey());
					}
				}
			}
			return mStatesWithLeftRejectingPartners;
		}
		
		/**
		 * Transition profile.
		 * 
		 * @author Fabian Reiter
		 */
		private class TransitionProfile {
			// only true for the copy of τ(ε)
			private boolean mIsInitial;
			
			private final Map<Transition, Boolean> mTransitions = new HashMap<>();
			
			/**
			 * @return The copy of the transition profile τ(ε), i.e. the initial
			 *         state of the TMA.
			 */
			public TransitionProfile() {
				mIsInitial = true;
				for (final STATE q : getOrigAutomaton().getStates()) {
					if (getOrigAutomaton().isFinal(q)) {
						mTransitions.put(new Transition(q, q), Boolean.TRUE);
					} else {
						mTransitions.put(new Transition(q, q), Boolean.FALSE);
					}
				}
			}
			
			/**
			 * @return The transition profile τ(a) for letter {@code a}.
			 */
			public TransitionProfile(final LETTER letter) {
				for (final STATE p : getOrigAutomaton().getStates()) {
					final boolean pIsFinal = getOrigAutomaton().isFinal(p);
					for (final OutgoingInternalTransition<LETTER, STATE> trans : getOrigAutomaton().internalSuccessors(
							p,
							letter)) {
						final STATE q = trans.getSucc();
						if (pIsFinal || getOrigAutomaton().isFinal(q)) {
							mTransitions.put(new Transition(p, q), Boolean.TRUE);
						} else {
							mTransitions.put(new Transition(p, q), Boolean.FALSE);
						}
					}
				}
			}
			
			/**
			 * @return The transition profile for the concatenation s·t.
			 */
			public TransitionProfile(final TransitionProfile transProfileS, final TransitionProfile transProfileT) {
				for (final Transition trans1 : transProfileS.mTransitions.keySet()) {
					for (final Transition trans2 : transProfileT.mTransitions.keySet()) {
						if (!trans1.getQ2().equals(trans2.getQ1())) {
							continue;
						}
						final Transition trans1x2 = new Transition(trans1.getQ1(), trans2.getQ2());
						if (transProfileS.getTransitions().get(trans1) || transProfileT.getTransitions().get(trans2)) {
							mTransitions.put(trans1x2, Boolean.TRUE);
						} else if (!this.mTransitions.containsKey(trans1x2)) {
							mTransitions.put(trans1x2, Boolean.FALSE);
						}
					}
				}
			}
			
			protected Map<Transition, Boolean> getTransitions() {
				return mTransitions;
			}
			
			/**
			 * @param transProfile
			 *            Transition profile.
			 * @return Whether s·t = s, where s = {@code this}.
			 */
			public boolean isInvariantUnder(final TransitionProfile transProfile) {
				return new TransitionProfile(this, transProfile).equals(this);
			}
			
			/**
			 * @return Whether t·t = t, where t = {@code this}.
			 */
			public boolean isIdempotent() {
				return new TransitionProfile(this, this).equals(this);
			}
			
			/**
			 * @param transProfile
			 *            Transition profile.
			 * @return whether L(⟨s,t⟩) ⊆ L_ω(A), where s = {@code this} <br>
			 *         Assumes that ⟨s,t⟩ is an s-t-pair, i.e. that L(⟨s,t⟩) is
			 *         “proper”.
			 */
			public boolean hasAcceptingLasso(final TransitionProfile transProfile) {
				for (final Transition trans1 : this.mTransitions.keySet()) {
					if (getOrigAutomaton().isInitial(trans1.getQ1())) {
						final Transition trans2 = new Transition(trans1.getQ2(), trans1.getQ2());
						if (transProfile.getTransitions().containsKey(trans2)
								&& transProfile.getTransitions().get(trans2)) {
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
				result = prime * result + mTransitions.hashCode();
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
				return mTransitions.equals(other.mTransitions) && mIsInitial == other.mIsInitial;
			}
		}
		
		/**
		 * Transitions are the basic building blocks of transition profiles.
		 * They are implemented as tuples of states.
		 */
		private final class Transition {
			private final STATE mQ1;
			
			private final STATE mQ2;
			
			public Transition(final STATE state1, final STATE state2) {
				this.mQ1 = state1;
				this.mQ2 = state2;
			}
			
			STATE getQ1() {
				return mQ1;
			}
			
			STATE getQ2() {
				return mQ2;
			}
			
			@Override
			public int hashCode() {
				final int prime = 31;
				int result = 1;
				result = prime * result + ((mQ1 == null) ? 0 : mQ1.hashCode());
				result = prime * result + ((mQ2 == null) ? 0 : mQ2.hashCode());
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
				final Transition other = (Transition) obj;
				if (mQ1 == null) {
					if (other.mQ1 != null) {
						return false;
					}
				} else if (!mQ1.equals(other.mQ1)) {
					return false;
				}
				if (mQ2 == null) {
					if (other.mQ2 != null) {
						return false;
					}
				} else if (!mQ2.equals(other.mQ2)) {
					return false;
				}
				return true;
			}
		}
	}
}
