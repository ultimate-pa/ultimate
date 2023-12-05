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
package de.uni_freiburg.informatik.ultimate.util.statistics;

import java.util.concurrent.TimeUnit;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class TimeTracker {

	private long mStartTime;
	private long mElapsedTimeNs;
	private long mLastDeltaNs;

	public TimeTracker() {
		reset();
	}

	public <T> T measure(final Supplier<T> fun) {
		start();
		try {
			return fun.get();
		} finally {
			stop();
		}
	}

	public void measure(final Runnable fun) {
		measure(() -> {
			fun.run();
			return null;
		});
	}

	public void start() {
		mStartTime = System.nanoTime();
	}

	public void stop() {
		mLastDeltaNs = System.nanoTime() - mStartTime;
		mElapsedTimeNs = mLastDeltaNs + mElapsedTimeNs;
	}

	public void reset() {
		mStartTime = -1;
		mElapsedTimeNs = 0;
		mLastDeltaNs = -1;
	}

	@Override
	public String toString() {
		if (mStartTime == -1) {
			return "N/A";
		}
		return CoreUtil.humanReadableTime(mElapsedTimeNs, TimeUnit.NANOSECONDS, 2);
	}

	public long lastDelta(final TimeUnit unit) {
		if (mLastDeltaNs == -1) {
			throw new IllegalStateException("Clock was not started");
		}
		return unit.convert(mLastDeltaNs, TimeUnit.NANOSECONDS);
	}

	public long elapsedTime(final TimeUnit unit) {
		return unit.convert(mElapsedTimeNs, TimeUnit.NANOSECONDS);
	}
}