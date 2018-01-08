package de.uni_freiburg.informatik.ultimate.util.statistics;

import java.util.HashMap;
import java.util.Map;

public class BenchmarkWithCounters extends Benchmark {

	Map<String, Integer> mCounters = new HashMap<>();

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
			register(name);
		}
	}

}
