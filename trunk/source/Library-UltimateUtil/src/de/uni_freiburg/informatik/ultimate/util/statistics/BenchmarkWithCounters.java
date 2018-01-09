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
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
//public class BenchmarkWithCounters extends Benchmark {
public class BenchmarkWithCounters implements ICsvProviderProvider<Number> {

	private final Benchmark mWatchBenchmark = new Benchmark();
	private final Map<String, Integer> mCounters = new HashMap<>();

	final private List<String> mColumnTitles = new ArrayList<>();
	final private List<Number> mResults = new ArrayList<>();

	private boolean mAlreadyGeneratedColumnTitlesAndResults = false;

	public void registerWatch(final String watchName) {
		mWatchBenchmark.register(watchName);
	}

	public void startWatch(final String watchName) {
		mWatchBenchmark.start(watchName);
	}

	public void stopWatch(final String watchName) {
		mWatchBenchmark.stop(watchName);
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
		final TimeUnit timeUnit = TimeUnit.SECONDS;
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
				formatString = "%-40s : %4f %n";
			} else if (result instanceof Integer) {
				formatString = "%-40s : %7d %n";
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
