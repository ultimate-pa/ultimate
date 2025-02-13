/*
 * Copyright (C) 2022 Marcel Ebbinghaus
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
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

import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPreferenceOrder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ParameterizedOrderAutomaton.State;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Implementation of the Parameterized Preference Order.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters
 * @param <S1>
 *            The type of states
 */
public class ParameterizedPreferenceOrder<L extends IAction, S1> implements IPreferenceOrder<L, S1, State> {
	private final List<Integer> mMaxSteps;
	private final List<String> mThreads;
	private final INwaOutgoingLetterAndTransitionProvider<L, State> mMonitor;
	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);

	// TODO (Dominik 2025-02-13): This cache only makes sense if PreferenceOrderComparator caches information (see
	// comment there). Also, if we want to cache this, we could just make it a field of the State class and thus avoid
	// the HashMap overhead (memory overhead [when there are many entries], lookup overhead, code complication).
	private final HashMap<State, PreferenceOrderComparator<L>> mComparatorsCache = new HashMap<>();

	/**
	 * Construct a new Parameterized Preference Order.
	 *
	 * @param maxSteps
	 *            List representing the sequence of maximal steps
	 * @param threads
	 *            List representing the sequence of threads
	 * @param alphabet
	 *            The alphabet
	 * @param isStep
	 *            Function that determines the step type
	 */
	public ParameterizedPreferenceOrder(final List<Integer> maxSteps, final List<String> threads,
			final VpAlphabet<L> alphabet, final java.util.function.Predicate<L> isStep) {
		mMaxSteps = maxSteps;
		mThreads = threads;
		mMonitor = new ParameterizedOrderAutomaton<>(mMaxSteps, mThreads, alphabet, isStep);
	}

	@Override
	public Comparator<L> getOrder(final S1 stateProgram, final State stateMonitor) {
		if (mComparatorsCache.containsKey(stateMonitor)) {
			return mComparatorsCache.get(stateMonitor);
		}

		final String lastThread = stateMonitor.thread();
		final int lastIndex = stateMonitor.index();
		final var comparator = new PreferenceOrderComparator<>(lastThread, lastIndex, mDefaultComparator, mThreads);
		mComparatorsCache.put(stateMonitor, comparator);
		return comparator;
	}

	@Override
	public boolean isPositional() {
		return false;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, State> getMonitor() {
		return mMonitor;
	}

	/**
	 * Comparator for the Preference Order.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param <L>
	 *            The type of letters
	 */
	private static final class PreferenceOrderComparator<L extends IAction> implements Comparator<L> {
		private final String mLastThread;
		private final int mLastIndex;
		private final Comparator<L> mFallback;
		private final List<String> mThreads;

		// TODO (Dominik 2025-02-13): Does this cache bring performance benefits?
		// It seems not clear to me that a HashMap-lookup is significantly more efficient than the actual comparison.
		private final HashMap<Pair<L, L>, Integer> mComparisonsCache = new HashMap<>();

		/**
		 * Construct a new Comparator.
		 *
		 * @param lastThread
		 *            The previous thread
		 * @param lastIndex
		 *            The index of the previous thread
		 * @param fallback
		 *            A fallback comparator
		 * @param threads
		 *            List representing the sequence of threads
		 */
		public PreferenceOrderComparator(final String lastThread, final int lastIndex, final Comparator<L> fallback,
				final List<String> threads) {
			mLastThread = Objects.requireNonNull(lastThread);
			mLastIndex = lastIndex;
			mFallback = Objects.requireNonNull(fallback);
			mThreads = Objects.requireNonNull(threads);
		}

		@Override
		public int compare(final L x, final L y) {
			if (x.getPrecedingProcedure() == mLastThread) {
				return -1;
			}

			final Pair<L, L> pair = new Pair<>(x, y);
			if (mComparisonsCache.containsKey(pair)) {
				return mComparisonsCache.get(pair);
			}

			// start the comparison from the current index
			final int xThreadIndex = DataStructureUtils.indexOf(mThreads, x.getPrecedingProcedure(), mLastIndex);
			final int yThreadIndex = DataStructureUtils.indexOf(mThreads, y.getPrecedingProcedure(), mLastIndex);
			final boolean xBefore = xThreadIndex < mLastIndex;
			final boolean yBefore = yThreadIndex < mLastIndex;
			if (xBefore && !yBefore) {
				mComparisonsCache.put(pair, 1);
				return 1;
			}
			if (yBefore && !xBefore) {
				mComparisonsCache.put(pair, -1);
				return -1;
			}
			final int r = Integer.compare(xThreadIndex, yThreadIndex);
			mComparisonsCache.put(pair, r);
			return r;
		}

		@Override
		public int hashCode() {
			return Objects.hash(mFallback, mLastThread, mThreads, mLastIndex);
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			return obj instanceof final PreferenceOrderComparator<?> other && mLastIndex == other.mLastIndex
					&& mFallback.equals(other.mFallback) && mLastThread.equals(other.mLastThread)
					&& mThreads.equals(other.mThreads);
		}
	}
}
