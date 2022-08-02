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

public class ParameterizedPreferenceOrder<L extends IIcfgTransition<?>, S1> implements IPreferenceOrder<L, S1, State>{
	private Integer mMaxStep;
	private List<String> mThreads;
	private INwaOutgoingLetterAndTransitionProvider<L, State> mMonitor;
	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);

	public ParameterizedPreferenceOrder(int parameter, List<String> threads, VpAlphabet<L> alphabet,
			java.util.function.Predicate<L> isStep) {
		mMaxStep = parameter;
		mThreads = threads;
		mMonitor = new ParameterizedOrderAutomaton<L>(mMaxStep, threads,alphabet , isStep);
	}

	@Override
	public Comparator<L> getOrder(S1 stateProgram, State stateMonitor) {
		final String lastThread = ((State) stateMonitor).getThread();
		return new PreferenceOrderComparator<>(lastThread, mDefaultComparator, mThreads);
	}
	
	public static final class PreferenceOrderComparator<L extends IAction> implements Comparator<L> {
		private final String mLastThread;
		private final Comparator<L> mFallback;
		private List<String> mThreads;

		public PreferenceOrderComparator(final String lastThread, final Comparator<L> fallback, final List<String> threads) {
			mLastThread = Objects.requireNonNull(lastThread);
			mFallback = fallback;
			mThreads = threads;
		}

		@Override
		public int compare(final L x, final L y) {
			final int lastThreadIndex = mThreads.indexOf(mLastThread);
			final int xThreadIndex = mThreads.indexOf(x.getPrecedingProcedure());
			final boolean xBefore = lastThreadIndex >= xThreadIndex;
			final int yThreadIndex = mThreads.indexOf(y.getPrecedingProcedure());
			final boolean yBefore = lastThreadIndex >= yThreadIndex;
			
			if (xBefore && !yBefore) {
				return 1;
			}
			if (yBefore && !xBefore) {
				return -1;
			}
			return Integer.compare(xThreadIndex, yThreadIndex);
			//return mFallback.compare(x, y);
		}

		@Override
		public int hashCode() {
			return Objects.hash(mFallback, mLastThread);
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
					&& Objects.equals(mThreads, other.mThreads);
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

}
