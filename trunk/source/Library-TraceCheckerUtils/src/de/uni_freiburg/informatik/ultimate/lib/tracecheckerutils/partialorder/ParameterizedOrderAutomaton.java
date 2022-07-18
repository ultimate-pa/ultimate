/*
 * Copyright (C) 2022 Marcel Ebbinghaus
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
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
	private static Integer sMaxStep;
	private final Map<String, Map<Integer, State>> mCreatedStates = new HashMap<>();
	private final List<String> mThreads;
	private String mInitialThread;
	private java.util.function.Predicate<L> mIsStep;
	private VpAlphabet<L> mAlphabet;

	
	public ParameterizedOrderAutomaton(final Integer parameter, final List<String> threads, VpAlphabet<L> alphabet,  java.util.function.Predicate<L> isStep) {
		sMaxStep = parameter;
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
			else if (state.getCounter()==sMaxStep-1) {
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
