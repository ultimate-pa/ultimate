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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.ParameterizedOrderAutomaton.State;

public class ParameterizedPreferenceOrder<L extends IIcfgTransition<?>, S1> implements IPreferenceOrder<L, S1, State> {
	private final List<Integer> mMaxSteps;
	private final List<String> mThreads;
	private final ShiftedList<String> mShiftedThreads;
	private final INwaOutgoingLetterAndTransitionProvider<L, State> mMonitor;
	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);

	public ParameterizedPreferenceOrder(final List<Integer> maxSteps, final List<String> threads,
			final VpAlphabet<L> alphabet, final java.util.function.Predicate<L> isStep) {
		mMaxSteps = maxSteps;
		mThreads = threads;
		mShiftedThreads = new ShiftedList<>();
		mShiftedThreads.addAll(threads);
		mMonitor = new ParameterizedOrderAutomaton<>(mMaxSteps, mThreads, mShiftedThreads, alphabet, isStep);
	}

	@Override
	public Comparator<L> getOrder(final S1 stateProgram, final State stateMonitor) {
		final String lastThread = stateMonitor.getThread();
		final int lastIndex = stateMonitor.getIndex();
		return new PreferenceOrderComparator<>(lastThread, lastIndex, mDefaultComparator, mThreads, mShiftedThreads);
	}

	public static final class PreferenceOrderComparator<L extends IAction> implements Comparator<L> {
		private final String mLastThread;
		private final Integer mLastIndex;
		private final Comparator<L> mFallback;
		private final List<String> mThreads;
		private final ShiftedList<String> mShiftedThreads;

		public PreferenceOrderComparator(final String lastThread, final Integer lastIndex, final Comparator<L> fallback,
				final List<String> threads, final ShiftedList<String> shiftedThreads) {
			mLastThread = Objects.requireNonNull(lastThread);
			mLastIndex = lastIndex;
			mFallback = fallback;
			mThreads = threads;
			mShiftedThreads = shiftedThreads;
		}

		@Override
		public int compare(final L x, final L y) {

			/*
			 * String xThread = x.getPrecedingProcedure(); String yThread = y.getPrecedingProcedure(); List<String>
			 * shiftedThreadList = new ArrayList<>(); shiftedThreadList.addAll(mThreads.subList(mLastIndex,
			 * mThreads.size())); shiftedThreadList.addAll(mThreads.subList(0, mLastIndex)); if (xThread == yThread) {
			 * return 0; } else if (xThread == mLastThread) { return -1; } else if (yThread == mLastThread) { return 1;
			 * } else if (shiftedThreadList.indexOf(xThread) < shiftedThreadList.indexOf(yThread)) { return -1; } else {
			 * return 1; }
			 */

			// idee ist hier die Liste vom aktuellen index ausgehend zu betrachten und falls ein thread mehrfach
			// vorkommt,
			// ist der relevante index der erste auf den aktuellen thread folgende

			if (x.getPrecedingProcedure() == mLastThread) {
				return -1;
			}
			/*
			 * List<String> shiftedThreadList = new ArrayList<>(); shiftedThreadList.addAll(mThreads.subList(mLastIndex,
			 * mThreads.size())); shiftedThreadList.addAll(mThreads.subList(0, mLastIndex));
			 * 
			 * final int xThreadIndex = shiftedThreadList.indexOf(x.getPrecedingProcedure()); final int yThreadIndex =
			 * shiftedThreadList.indexOf(y.getPrecedingProcedure()); return Integer.compare(xThreadIndex, yThreadIndex);
			 */

			final int xThreadIndex = mShiftedThreads.indexOf(x.getPrecedingProcedure(), mLastIndex);
			final int yThreadIndex = mShiftedThreads.indexOf(y.getPrecedingProcedure(), mLastIndex);
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

	@Override
	public boolean isPositional() {
		return true;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, State> getMonitor() {
		return mMonitor;
	}
	/*
	 * public class ShiftedList<String> extends ArrayList<String>{
	 * 
	 * public int indexOf(String s, int i) {
	 * 
	 * int index = indexOfRange(s, i, this.size()); if (index != -1) { return index; } return indexOfRange(s, 0, i); }
	 * 
	 * int indexOfRange(Object o, int start, int end) { //Object[] es = this.elementData; if (o == null) { for (int i =
	 * start; i < end; i++) { if (this.get(i) == null) { return i; } } } else { for (int i = start; i < end; i++) { if
	 * (o.equals(this.get(i))) { return i; } } } return -1; } }
	 */

}
