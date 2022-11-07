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
import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ParameterizedOrderAutomaton.State;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class ParameterizedPreferenceOrder<L extends IAction, S1> implements IPreferenceOrder<L, S1, State> {
	private final List<Integer> mMaxSteps;
	private final List<String> mThreads;
	private final INwaOutgoingLetterAndTransitionProvider<L, State> mMonitor;
	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);

	public ParameterizedPreferenceOrder(final List<Integer> maxSteps, final List<String> threads,
			final VpAlphabet<L> alphabet, final java.util.function.Predicate<L> isStep) {
		mMaxSteps = maxSteps;
		mThreads = threads;
		mMonitor = new ParameterizedOrderAutomaton<>(mMaxSteps, mThreads, alphabet, isStep);
	}

	@Override
	public Comparator<L> getOrder(final S1 stateProgram, final State stateMonitor) {
		final String lastThread = stateMonitor.getThread();
		final int lastIndex = stateMonitor.getIndex();
		return new PreferenceOrderComparator<>(lastThread, lastIndex, mDefaultComparator, mThreads);
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, State> getMonitor() {
		return mMonitor;
	}

	public static final class PreferenceOrderComparator<L extends IAction> implements Comparator<L> {
		private final String mLastThread;
		private final Integer mLastIndex;
		private final Comparator<L> mFallback;
		private final List<String> mThreads;

		public PreferenceOrderComparator(final String lastThread, final Integer lastIndex, final Comparator<L> fallback,
				final List<String> threads) {
			mLastThread = Objects.requireNonNull(lastThread);
			mLastIndex = lastIndex;
			mFallback = fallback;
			mThreads = threads;
		}

		@Override
		public int compare(final L x, final L y) {

			if (x.getPrecedingProcedure() == mLastThread) {
				return -1;
			}
			
			//start the comparison from the current index
			final int xThreadIndex = DataStructureUtils.indexOf(mThreads, x.getPrecedingProcedure(), mLastIndex);
			final int yThreadIndex = DataStructureUtils.indexOf(mThreads, y.getPrecedingProcedure(), mLastIndex);
			final boolean xBefore = xThreadIndex < mLastIndex;
			final boolean yBefore = yThreadIndex < mLastIndex;
			if (xBefore && !yBefore) {
				return 1;
			}
			if (yBefore && !xBefore) {
				return -1;
			}
			return Integer.compare(xThreadIndex, yThreadIndex);
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
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final PreferenceOrderComparator<L> other = (PreferenceOrderComparator<L>) obj;
			return Objects.equals(mFallback, other.mFallback) && Objects.equals(mLastThread, other.mLastThread)
					&& Objects.equals(mThreads, other.mThreads) && Objects.equals(mLastIndex, other.mLastIndex);
		}
	}
}
