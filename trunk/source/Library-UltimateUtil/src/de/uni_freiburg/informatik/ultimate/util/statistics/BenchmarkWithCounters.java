/*
 * Copyright (C) 2017-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 University of Freiburg
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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

/**
 * Combines an instance of {@link Benchmark} with counters. Whenever a watch is unpaused, the counter of the same name
 * is incremented.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class BenchmarkWithCounters implements ICsvProviderProvider<Number> {

	private final Benchmark mWatchBenchmark = new Benchmark();
	private final Map<String, Integer> mCounters = new HashMap<>();

	final protected List<String> mColumnTitles = new ArrayList<>();
	final protected List<Number> mResults = new ArrayList<>();

	protected boolean mAlreadyGeneratedColumnTitlesAndResults = false;

	public void registerWatch(final String watchName) {
		mWatchBenchmark.register(watchName);
	}

	public void unpauseWatch(final String watchName) {
		mWatchBenchmark.unpause(watchName);
	}

	public void pauseWatch(final String watchName) {
		mWatchBenchmark.pause(watchName);
	}

	public void registerCounter(final String counterName) {
		if (mCounters.containsKey(counterName)) {
			throw new IllegalArgumentException("registering the same counter twice is forbidden: " + counterName);
		}
		mCounters.put(counterName, 0);
	}

	public void resetCounter(final String counterName) {
		if (!mCounters.containsKey(counterName)) {
			throw new IllegalArgumentException("register this counter before resetting it: " + counterName);
		}
		mCounters.put(counterName, 0);
	}

	public void incrementCounter(final String counterName) {
		final Integer ctr = mCounters.get(counterName);
		if (ctr == null) {
			throw new IllegalArgumentException("register this counter before using it: " + counterName);
		}
		mCounters.put(counterName, ctr + 1);
	}

	public void registerCountersAndWatches(final String[] names) {
		for (final String name : names) {
			registerCounter(name);
			registerWatch(name);
		}
	}

	protected void generateColumnTitlesAndResults() {
		if (mAlreadyGeneratedColumnTitlesAndResults) {
			return;
		}
		final TimeUnit timeUnit = TimeUnit.MILLISECONDS;
//		final TimeUnit timeUnit = TimeUnit.SECONDS;
		for (final String watchName : mWatchBenchmark.getTitles()) {
			mColumnTitles.add(watchName + "(" + timeUnit + ")");
			mResults.add(mWatchBenchmark.getElapsedTime(watchName, timeUnit));
		}
		for (final Entry<String, Integer> en : mCounters.entrySet()) {
			mColumnTitles.add("#" + en.getKey());
			mResults.add(en.getValue());
		}
		mAlreadyGeneratedColumnTitlesAndResults = true;
	}

	@Override
	public String toString() {
		generateColumnTitlesAndResults();
		final StringBuilder sb = new StringBuilder();

		sb.append("\n");



		for (int i = 0; i < mColumnTitles.size(); i++) {
			final Number result = mResults.get(i);
			final String formatString;
			if (result instanceof Double) {
				formatString = "%-40s : %15.2f %n";
//				formatString = "%-40s : %s %n";
			} else if (result instanceof Integer) {
				formatString = "%-40s : %15d %n";
			} else {
				throw new AssertionError("missed benchmark result case?");
			}
			sb.append(String.format(formatString, mColumnTitles.get(i), result));
		}
		return sb.toString();
	}

	@Override
	public ICsvProvider<Number> createCsvProvider() {
		generateColumnTitlesAndResults();

		final ICsvProvider<Number> result = new SimpleCsvProvider<>(mColumnTitles);
		result.addRow(mResults);

		return result;
	}
}
