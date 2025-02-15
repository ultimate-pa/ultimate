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
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ParameterizedPreferenceOrder.State;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

class ParameterizedOrderAutomaton<L extends IAction> implements INwaOutgoingLetterAndTransitionProvider<L, State> {
	private final List<Integer> mMaxSteps;
	private final List<String> mThreads;
	private final VpAlphabet<L> mAlphabet;
	private final Predicate<L> mIsStep;

	private final Map<Integer, Map<Integer, State>> mCreatedStates;
	private final State mInitialState;

	public ParameterizedOrderAutomaton(final List<Integer> maxSteps, final List<String> threads,
			final VpAlphabet<L> alphabet, final Predicate<L> isStep) {
		mMaxSteps = maxSteps;
		mThreads = threads;
		mIsStep = isStep;
		mAlphabet = alphabet;

		mCreatedStates = IntStream.range(0, mThreads.size()).mapToObj(Integer::valueOf)
				.collect(Collectors.toMap(Function.identity(), i -> new HashMap<>()));
		mInitialState = getOrCreateState(threads.get(0), 0, 0);
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
		return null;
	}

	@Override
	public Iterable<State> getInitialStates() {
		return Set.of(mInitialState);
	}

	private State getOrCreateState(final String thread, final int index, final int counter) {
		final Map<Integer, State> counterMap = mCreatedStates.get(index);
		return counterMap.computeIfAbsent(counter, x -> new State(thread, index, counter));
	}

	@Override
	public boolean isInitial(final State state) {
		return state.index() == 0 && state.counter() == 0;
	}

	@Override
	public boolean isFinal(final State state) {
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
	public Iterable<OutgoingInternalTransition<L, State>> internalSuccessors(final State state, final L letter) {
		if (mIsStep.test(letter)) {
			if (letter.getPrecedingProcedure() != state.thread()) {
				// return Set.of(new OutgoingInternalTransition<>(letter,
				// getOrCreateState(mThreads.get(mThreads.size()-1), mThreads.size()-1 , 0)));

				// return Set.of(new OutgoingInternalTransition<>(letter, state));

				final String nextThread = letter.getPrecedingProcedure();
				int nextIndex = DataStructureUtils.indexOf(mThreads, nextThread, state.index());
				assert nextIndex != -1 : "Unknown thread " + nextThread + " not in " + mThreads;

				if (mMaxSteps.get(nextIndex) == 1) {
					nextIndex = (nextIndex + 1) % mThreads.size();
					return Set.of(new OutgoingInternalTransition<>(letter,
							getOrCreateState(mThreads.get(nextIndex), nextIndex, 0)));
				}
				return Set.of(new OutgoingInternalTransition<>(letter, getOrCreateState(nextThread, nextIndex, 1)));

			}
			if (state.counter() == mMaxSteps.get(state.index()) - 1) {
				final int nextThreadIndex = (state.index() + 1) % mThreads.size();
				return Set.of(new OutgoingInternalTransition<>(letter,
						getOrCreateState(mThreads.get(nextThreadIndex), nextThreadIndex, 0)));
			}
			return Set.of(new OutgoingInternalTransition<>(letter,
					getOrCreateState(state.thread(), state.index(), state.counter() + 1)));
		}
		return Set.of(new OutgoingInternalTransition<>(letter, state));
	}

	@Override
	public Iterable<OutgoingCallTransition<L, State>> callSuccessors(final State state, final L letter) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, State>> returnSuccessors(final State state, final State hier,
			final L letter) {
		throw new UnsupportedOperationException();
	}
}
