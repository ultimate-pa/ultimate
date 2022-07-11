package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;


import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;


public class ParameterizedOrderAutomaton<L extends IIcfgTransition<?>>
implements INwaOutgoingLetterAndTransitionProvider<L, ParameterizedOrderAutomaton.State>{
	private final Map<String, Map<Integer, State>> mCreatedStates = new HashMap<>();
	private final List<String> mThreads;
	private static Integer mMaxStep;
	private String mInitialThread;
	private java.util.function.Predicate<L> mIsStep;
	private VpAlphabet<L> mAlphabet;

	
	public ParameterizedOrderAutomaton(final Integer parameter, final List<String> threads, VpAlphabet<L> alphabet,  java.util.function.Predicate<L> isStep) {
		mMaxStep = parameter;
		mThreads=threads;
		mIsStep = isStep;
		mAlphabet = alphabet;
		for (String thread : mThreads) {
			mCreatedStates.put(thread, new HashMap<>());
		}
		mInitialThread = threads.get(0);
		
	}

	@Override
	public IStateFactory<State> getStateFactory() {
		throw new UnsupportedOperationException();
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		return mAlphabet;
	}

	@Override
	public State getEmptyStackState() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<State> getInitialStates() {
		Set<State> initialSet = new HashSet<>();
		initialSet.add(getOrCreateState(mInitialThread,0));
		return initialSet;
	}


	private State getOrCreateState(String thread, Integer counter) {
		Map<Integer, State> counterMap = mCreatedStates.get(thread);
		if (counterMap.get(counter)==null) {
			State state = new State(thread, counter);
			counterMap.put(counter, state);
			mCreatedStates.put(thread, counterMap);
		}
		return counterMap.get(counter);
		
	}

	@Override
	public boolean isInitial(State state) {
		return (state.getThread()==mInitialThread && state.getCounter()==0);
	}

	@Override
	public boolean isFinal(State state) {
		return true;
	}

	@Override
	public int size() {
		return -1;
	}

	@Override
	public String sizeInformation() {
		return "<unknown>";
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, State>> internalSuccessors(State state, L letter) {
		if (mIsStep.test(letter)) {
			if(letter.getPrecedingProcedure() != state.getThread()) {
				return Set.of(new OutgoingInternalTransition<>(letter, getOrCreateState(letter.getPrecedingProcedure(),0)));
			}
			else if (state.getCounter()==mMaxStep-1) {
				return Set.of(new OutgoingInternalTransition<>(letter, getOrCreateState(nextThread(state.getThread()),0)));
			}
			else {
				return Set.of(new OutgoingInternalTransition<>(letter, getOrCreateState(state.getThread(),state.getCounter()+1)));
			}
		}
		else {
			return Set.of(new OutgoingInternalTransition<>(letter, state));
		}
	}

	private String nextThread(String thread) {
		
		return mThreads.get((mThreads.indexOf(thread)+1) % mThreads.size());
	}

	@Override
	public Iterable<OutgoingCallTransition<L, State>> callSuccessors(State state, L letter) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, State>> returnSuccessors(State state, State hier,
			L letter) {
		throw new UnsupportedOperationException();
	}
	
	public static final class State{
		private final String mThread;
		private final Integer mCounter;
		
		public State(final String thread, final Integer counter) {
			mThread = thread;
			mCounter = counter;
		}
		
		public String getThread() {
			return mThread;
		}
		
		public Integer getCounter() {
			return mCounter;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final State other = (State) obj;
			return Objects.equals(mThread, other.mThread) && Objects.equals(mCounter, other.mCounter);
		}
		
		@Override
		public int hashCode() {
			return Objects.hash(mThread, mCounter);
		}
	}

}
