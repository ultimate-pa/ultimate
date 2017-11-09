package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.inclusion;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.SetOfStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

public class GeneralizedBuchiToBuchi<LETTER, STATE> implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {

	private final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final IBuchiIntersectStateFactory<STATE> mStateFactory;
	private final STATE mEmptyStackState;
	private final SetOfStates<STATE> mSetOfStates;
    private final int mAcceptanceSize;
    private final Map<STATE, TrackState<STATE>> mTrackStateMap;
	private final Map<TrackState<STATE>, STATE> mStateMap;
	
	public <SF extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> GeneralizedBuchiToBuchi(
			final SF stateFactory,
			final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand){
		mOperand = operand;
		mStateFactory = stateFactory;
		mEmptyStackState = stateFactory.createEmptyStackState();
		mSetOfStates = new SetOfStates<>(mEmptyStackState);
		mAcceptanceSize = operand.getAcceptanceSize();
		mTrackStateMap = new HashMap<>();
		mStateMap = new HashMap<>();
		constructInitialStates();
	}
	
	public <SF extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> GeneralizedBuchiToBuchi(
			final SF stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand){
		if(! (operand instanceof IGeneralizedNestedWordAutomaton)) {
			throw new UnsupportedOperationException("Input automaton is not GBA");
		}
		mOperand = (IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE>)operand;;
		mStateFactory = stateFactory;
		mEmptyStackState = stateFactory.createEmptyStackState();
		mSetOfStates = new SetOfStates<>(mEmptyStackState);
		mAcceptanceSize = mOperand.getAcceptanceSize();
		mTrackStateMap = new HashMap<>();
		mStateMap = new HashMap<>();
		constructInitialStates();
	}
	
	public <SF extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> GeneralizedBuchiToBuchi(
			final SF stateFactory,
			final IGeneralizedNestedWordAutomaton<LETTER, STATE> operand){
		if(! (operand instanceof IGeneralizedNestedWordAutomaton)) {
			throw new UnsupportedOperationException("Input automaton is not GBA");
		}
		mOperand = (IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE>)operand;;
		mStateFactory = stateFactory;
		mEmptyStackState = stateFactory.createEmptyStackState();
		mSetOfStates = new SetOfStates<>(mEmptyStackState);
		mAcceptanceSize = mOperand.getAcceptanceSize();
		mTrackStateMap = new HashMap<>();
		mStateMap = new HashMap<>();
		constructInitialStates();
	}
	
	private void constructInitialStates() {
		for (final STATE st : mOperand.getInitialStates()) {
			final int track = 0;
			getOrConstructState(st, true, track);
		}
	}
	
	private TrackState<STATE> getOrConstructState(STATE state, boolean isInitial, final int track) {
		TrackState<STATE> trackState = new TrackState<>(state, track);
		STATE res = mStateMap.get(trackState);
		if(res == null) {
			res = mStateFactory.intersectBuchi(state, state, track);
			trackState.setBuchiState(res);
			mTrackStateMap.put(res, trackState);
			mStateMap.put(trackState, res);
			final boolean isAccepting = (track == 0) && (mOperand.getAcceptanceLabels(state).contains(0));
			mSetOfStates.addState(isInitial, isAccepting, res);
		}
		return mTrackStateMap.get(res);
	}
	
	private int getSuccTrack(TrackState<STATE> state, STATE succ) {
		final int succTrack = (state.mTrack + 1) % mAcceptanceSize;
		if(mOperand.isFinal(succ, state.mTrack)) {
			return succTrack;
		}else {
			return state.mTrack;
		}
	}
	
	private class TrackState<STATE> {
		STATE mState;
		int mTrack;
		STATE mRes;
		TrackState(final STATE state, final int track) {
			mState = state;
			mTrack = track;
		}
		
		void setBuchiState(STATE state) {
			mRes = state;
		}
		
		@Override
		public boolean equals(Object obj) {
			if(obj == null) return false;
			if(this == obj) return true;
			if(!(obj instanceof TrackState)) {
				return false;
			}
			@SuppressWarnings("unchecked")
			TrackState<STATE> other = (TrackState<STATE>)obj;
			return mState.equals(other.mState)
				&& mTrack == other.mTrack;
		}
		
		@Override
		public int hashCode() {
			int result = mState.hashCode();
			result = result * 31 + mTrack;
			return result;
		}
		
		@Override
		public String toString() {
			return mState + "," + mTrack;
		}
	}
	
	@Override
	public Set<LETTER> getAlphabet() {
		return mOperand.getAlphabet();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public int size() {
		return mSetOfStates.getStates().size();
	}

	@Override
	public String sizeInformation() {
		return mSetOfStates.getStates().size() + " states";
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public STATE getEmptyStackState() {
		return mEmptyStackState;
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		return mSetOfStates.getInitialStates();
	}

	@Override
	public boolean isInitial(STATE state) {
		return mSetOfStates.isInitial(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return mSetOfStates.isAccepting(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(STATE state, LETTER letter) {
		TrackState<STATE> trackState = mTrackStateMap.get(state);
		List<OutgoingInternalTransition<LETTER, STATE>> succs = new ArrayList<>();
		for(final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(trackState.mState, letter)) {
			final STATE succ = trans.getSucc();
			final int succTrack = getSuccTrack(trackState, succ);
			TrackState<STATE> succTrackState = getOrConstructState(succ, false, succTrack);
			succs.add(new OutgoingInternalTransition<LETTER, STATE>(letter, succTrackState.mRes));
		}
		return succs;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(STATE state, LETTER letter) {
		return new ArrayList<>();
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(STATE state, STATE hier, LETTER letter) {
		return new ArrayList<>();
	} 
	
}
