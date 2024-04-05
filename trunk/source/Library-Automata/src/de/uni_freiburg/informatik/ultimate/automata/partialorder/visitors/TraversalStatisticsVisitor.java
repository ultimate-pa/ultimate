/*
 * Copyright (C) 2022 Aly Mohsen
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors;

import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;

/**
 * A wrapper visitor that records statistics about a DFS traversal.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * @author Aly Mohsen
 *
 * @param <L>
 *            the type of letters in the traversed automaton
 * @param <S>
 *            the type of states
 * @param <V>
 *            the type of the underlying (wrapped) visitor
 */
public class TraversalStatisticsVisitor<L, S, V extends IDfsVisitor<L, S>> extends WrapperVisitor<L, S, V> {

	private final Statistics mStatistics;

	/**
	 * Creates a new statistics wrapper visitor.
	 *
	 * @param underlying
	 *            The underlying visitor to wrap
	 */
	public TraversalStatisticsVisitor(final V underlying) {
		super(underlying);
		mStatistics = new Statistics();
	}

	public IStatisticsDataProvider getStatistics() {
		mStatistics.finish();
		return mStatistics;
	}

	@Override
	public boolean addStartState(final S state) {
		mStatistics.start();
		mStatistics.incStates();
		return super.addStartState(state);
	}

	@Override
	public boolean discoverState(final S state) {
		mStatistics.incStates();
		return super.discoverState(state);
	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		mStatistics.incTransitions();
		return super.discoverTransition(source, letter, target);
	}

	@Override
	public boolean isFinished() {
		final boolean result = super.isFinished();
		if (result) {
			mStatistics.finish();
		}
		return result;
	}

	private static final class Statistics extends AbstractStatisticsDataProvider {
		public static final String STATES = "States";
		public static final String TRANSITIONS = "Transitions";
		public static final String TIME = "Traversal time";

		private static final String TIMER_NOT_RUNNING = "Computation timer has not been started";

		private long mStartTime = -1;
		private long mEndTime = -1;
		private int mStates;
		private int mTransitions;

		private Statistics() {
			declare(STATES, () -> mStates, KeyType.COUNTER);
			declare(TRANSITIONS, () -> mTransitions, KeyType.COUNTER);
			declare(TIME, this::getTime, KeyType.TIMER);
		}

		private void start() {
			assert mStartTime == -1 : "Computation timer already started";
			mStartTime = System.nanoTime();
		}

		private void incStates() {
			assert mStartTime != -1 : TIMER_NOT_RUNNING;
			mStates++;
		}

		private void incTransitions() {
			assert mStartTime != -1 : TIMER_NOT_RUNNING;
			mTransitions++;
		}

		private void finish() {
			// assert mStartTime != -1 : TIMER_NOT_RUNNING;
			if (mEndTime == -1) {
				mEndTime = System.nanoTime();
			}
		}

		private long getTime() {
			// assert mStartTime != -1 : TIMER_NOT_RUNNING;
			assert mEndTime != -1 : "Computation timer has not been stopped";
			return mEndTime - mStartTime;
		}

		@Override
		public String toString() {
			return "States: " + mStates + ", Transitions: " + mTransitions + ", Elapsed Time (ns): "
					+ (mEndTime - mStartTime);
		}
	}
}
