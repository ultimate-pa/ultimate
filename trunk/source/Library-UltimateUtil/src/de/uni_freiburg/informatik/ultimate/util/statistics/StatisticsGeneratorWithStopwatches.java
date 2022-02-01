/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.TimeUnit;

/**
 * Superclass for benchmark generators that use stopwatches. Takes care that
 * <li>no unregistered stopwatches are used
 * <li>we only take the time of stopwatches that have been stopped.
 *
 * @author Matthias Heizmann
 */
public abstract class StatisticsGeneratorWithStopwatches {

	private final Map<String, Boolean> mRunningStopwatches;
	private final Benchmark mBenchmark;

	public abstract String[] getStopwatches();

	public StatisticsGeneratorWithStopwatches() {
		mRunningStopwatches = new HashMap<>(getStopwatches().length);
		mBenchmark = new Benchmark();
		for (final String name : getStopwatches()) {
			mRunningStopwatches.put(name, false);
			mBenchmark.register(name);
		}
	}

	public void start(final Object stopwatchName) {
		start(stopwatchName.toString());
	}

	public void start(final String stopwatchName) {
		assert mRunningStopwatches.containsKey(stopwatchName) : "no such stopwatch " + stopwatchName;
		assert !mRunningStopwatches.get(stopwatchName).booleanValue() : "already started " + stopwatchName;
		mRunningStopwatches.put(stopwatchName, true);
		mBenchmark.unpause(stopwatchName);
	}

	public void stop(final Object stopwatchName) {
		stop(stopwatchName.toString());
	}

	public void stop(final String stopwatchName) {
		assert mRunningStopwatches.containsKey(stopwatchName) : "no such stopwatch " + stopwatchName;
		assert mRunningStopwatches.get(stopwatchName).booleanValue() : "not running " + stopwatchName;
		mRunningStopwatches.put(stopwatchName, false);
		mBenchmark.pause(stopwatchName);
	}

	public void stopAllStopwatches() {
		mRunningStopwatches.entrySet().stream().filter(a -> a.getValue()).map(a -> a.getKey()).forEach(a -> stop(a));
	}

	protected long getElapsedTime(final String stopwatchName) throws StopwatchStillRunningException {
		assert mRunningStopwatches.containsKey(stopwatchName) : "no such stopwatch " + stopwatchName;
		if (mRunningStopwatches.get(stopwatchName)) {
			throw new StopwatchStillRunningException();
		}
		return (long) mBenchmark.getElapsedTime(stopwatchName, TimeUnit.NANOSECONDS);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		for (final String name : getStopwatches()) {
			sb.append(name);
			sb.append(": ");
			try {
				sb.append(prettyprintNanoseconds(getElapsedTime(name)));
			} catch (final StopwatchStillRunningException e) {
				sb.append("clockStillRunning!");
			}
			if (mRunningStopwatches.get(name)) {
				sb.append("stopwatch still running!!!");
			}
			sb.append(" ");
		}
		return sb.toString();
	}

	public static String prettyprintNanoseconds(final long time) {
		final long seconds = time / 1000000000;
		final long tenthDigit = time / 100000000 % 10;
		return seconds + "." + tenthDigit + "s";
	}

	public class StopwatchStillRunningException extends Exception {

		private static final long serialVersionUID = 47519007262609785L;

	}

}
