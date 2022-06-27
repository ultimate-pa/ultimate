package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.HashMap;
import java.util.HashSet;
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


public class ParameterizedOrderAutomaton<L extends IIcfgTransition<?>,S>
implements INwaOutgoingLetterAndTransitionProvider<L, S>{
	private final Map<String, Map<Integer, State>> mCreatedStates = new HashMap<>();
	private final Set<String> mThreads = new HashSet<>();
	private static Integer mParameter;
	private String mInitialThread;
	private java.util.function.Predicate<L> mIsStep;

	
	public ParameterizedOrderAutomaton(final Integer parameter, final Set<String> threads, java.util.function.Predicate<L> isStep) {
		mParameter = parameter;
		mThreads.addAll(threads);
		mIsStep = isStep;
		for (String thread : mThreads) {
			mCreatedStates.put(thread, new HashMap<>());
		}
		
	}

	@Override
	public IStateFactory<S> getStateFactory() {
		throw new UnsupportedOperationException();
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public S getEmptyStackState() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<S> getInitialStates() {
		Set<S> initialSet = new HashSet<>();
		initialSet.add(getOrCreateState(mInitialThread,0));
		return initialSet;
	}


	private S getOrCreateState(String thread, Integer counter) {
		Map<Integer, State> counterMap = mCreatedStates.get(thread);
		if (counterMap.get(counter)==null) {
			State state = new State(thread, counter);
			counterMap.put(counter, state);
			mCreatedStates.put(thread, counterMap);
		}
		return (S) counterMap.get(counter);
		
	}

	@Override
	public boolean isInitial(S state) {
		State pState = (State) state;
		return (pState.getThread()==mInitialThread && pState.getCounter()==0);
	}

	@Override
	public boolean isFinal(S state) {
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
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(S state, L letter) {
		State pState = (State) state;
		HashSet<OutgoingInternalTransition<L, S>> transitionSet = new HashSet<>();
		if (mIsStep.test(letter)) {
			if(letter.getPrecedingProcedure() != pState.getThread()) {
				transitionSet.add(new OutgoingInternalTransition<>(letter, getOrCreateState(letter.getPrecedingProcedure(),0)));
			}
			else if (pState.getCounter()==mParameter) {
				transitionSet.add(new OutgoingInternalTransition<>(letter, getOrCreateState(nextThread(pState.getThread()),0)));
			}
			else {
				transitionSet.add(new OutgoingInternalTransition<>(letter, getOrCreateState(nextThread(pState.getThread()),pState.getCounter()+1)));
			}
		}
		else {
			transitionSet.add(new OutgoingInternalTransition<>(letter, state));
		}
		return transitionSet;
	}

	private String nextThread(String thread) {
		// Welcher Thread kommt als nächstes?
		// Sollte das überhaupt im Automaten ermittelt werden oder in ParameterizedOrder?
		// Sollte der Automat überhaupt die Order kennen?
		return null;
	}

	@Override
	public Iterable<OutgoingCallTransition<L, S>> callSuccessors(S state, L letter) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, S>> returnSuccessors(S state, S hier,
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
