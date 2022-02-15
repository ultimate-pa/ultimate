/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.statistics.measures;

import java.util.concurrent.TimeUnit;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Simple stopwatch that tracks one time.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class TimeTracker {

	private long mStartTime;
	private long mElapsedTimeNs;
	private long mLastDeltaNs;
	private boolean mIsRunning;

	public TimeTracker() {
		mStartTime = -1;
		mElapsedTimeNs = 0;
		mLastDeltaNs = -1;
		mIsRunning = false;
	}

	/**
	 * Start this {@link TimeTracker}, execute <tt>fun</tt>, stop this {@link TimeTracker}, return the result of
	 * <tt>fun</tt>
	 *
	 * @param <T>
	 *            The return type of <tt>fun</tt>
	 * @param fun
	 *            A function that computes something.
	 * @return The result of the computation.
	 */
	public <T> T measure(final Supplier<T> fun) {
		start();
		final T rtr = fun.get();
		stop();
		return rtr;
	}

	public void start() {
		mStartTime = System.nanoTime();
		mIsRunning = true;
	}

	public void stop() {
		mLastDeltaNs = System.nanoTime() - mStartTime;
		mElapsedTimeNs = mLastDeltaNs + mElapsedTimeNs;
		mIsRunning = false;
	}

	public boolean isRunning() {
		return mIsRunning;
	}

	@Override
	public String toString() {
		if (mStartTime == -1) {
			return "N/A";
		}
		return String.format("%s [isRunning=%s]", CoreUtil.humanReadableTime(mElapsedTimeNs, TimeUnit.NANOSECONDS, 2),
				isRunning());
	}

	/**
	 * Adds elapsed time as nanos to this {@link TimeTracker}.
	 */
	public void addElapsedTime(final long nanos) {
		if (isRunning()) {
			throw new IllegalTimeTrackerState("TimeTracker is running");
		}
		mElapsedTimeNs += nanos;
	}

	/**
	 * Return the time between the last start and the last stop of this {@link TimeTracker}.
	 *
	 * @param unit
	 *            The time unit of the return value.
	 * @return The time between the last start and the last stop.
	 */
	public long lastDelta(final TimeUnit unit) {
		if (mLastDeltaNs == -1) {
			throw new IllegalTimeTrackerState("TimeTracker was not started");
		}
		if (mIsRunning) {
			throw new IllegalTimeTrackerState("TimeTracker is running");
		}
		return unit.convert(mLastDeltaNs, TimeUnit.NANOSECONDS);
	}

	/**
	 * Return the total elapsed time over all start/stop sequences of this {@link TimeTracker}.
	 *
	 * @param unit
	 *            The time unit of the return value.
	 * @return The time between the first start and the last stop.
	 */
	public long elapsedTime(final TimeUnit unit) {
		if (mIsRunning) {
			throw new IllegalStateException("TimeTracker is running");
		}
		return unit.convert(mElapsedTimeNs, TimeUnit.NANOSECONDS);
	}

	private static final class IllegalTimeTrackerState extends RuntimeException {

		public IllegalTimeTrackerState(final String msg) {
			super(msg);
		}

		private static final long serialVersionUID = 4174168684311854088L;

	}
}