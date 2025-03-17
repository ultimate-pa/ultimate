package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

// TODO: Replace Integer usage with value-abstraction, so we can call abstractions on this
// TODO: make immutable
public class ThreadInstanceCounter {
	private final Map<String, Integer> mThreadInstances;
	private final Set<String> mThreadNameSet;

	public ThreadInstanceCounter(final Map<String, Integer> threadMap) {
		mThreadNameSet = threadMap.keySet();
		mThreadInstances = new HashMap<>(threadMap);
	}

	public ThreadInstanceCounter(final ThreadInstanceCounter other) {
		mThreadInstances = new HashMap<>(other.getThreadInstances());
		mThreadNameSet = new HashSet<>();
		getThreadNameSet().addAll(getThreadInstances().keySet());
	}

	public Set<String> getThreadNameSet() {
		return mThreadNameSet;
	}

	public Map<String, Integer> getThreadInstances() {
		return new HashMap<>(mThreadInstances);
	}

	public ThreadInstanceCounter incrementThread(final String threadName) {
		if (mThreadInstances.get(threadName) == null) {
			throw new IllegalArgumentException("Trying to increment thread which does not exist: " + threadName);
		}
		final var newInstances = new HashMap<>(mThreadInstances);
		final int newCount = Math.min(2, mThreadInstances.get(threadName) + 1);
		newInstances.put(threadName, newCount);
		return new ThreadInstanceCounter(newInstances);
	}

	public ThreadInstanceCounter setActive(final Collection<String> threadName) {
		final var newInstanceMap = new HashMap<>(mThreadInstances);
		threadName.stream().filter(p -> newInstanceMap.get(p) != null).filter(p -> newInstanceMap.get(p) < 1)
				.forEach(p -> newInstanceMap.put(p, 1));
		return new ThreadInstanceCounter(newInstanceMap);
	}

	public ThreadInstanceCounter setInf(final Collection<String> threadName) {
		final var newInstanceMap = new HashMap<>(mThreadInstances);
		threadName.stream().filter(p -> newInstanceMap.get(p) != null).forEach(p -> newInstanceMap.put(p, 2));
		return new ThreadInstanceCounter(newInstanceMap);
	}

	public ThreadInstanceCounter union(final ThreadInstanceCounter other) {
		final Map<String, Integer> newThreadMap = new HashMap<>();
		for (final String thread : mThreadNameSet) {
			newThreadMap.put(thread,
					Math.max(getThreadInstances().get(thread), other.getThreadInstances().get(thread)));
		}
		return new ThreadInstanceCounter(newThreadMap);
	}

	public ThreadInstanceCounter intersect(final ThreadInstanceCounter other) {
		final Map<String, Integer> newThreadMap = new HashMap<>();
		for (final String thread : mThreadNameSet) {
			newThreadMap.put(thread,
					Math.min(getThreadInstances().get(thread), other.getThreadInstances().get(thread)));
		}
		return new ThreadInstanceCounter(newThreadMap);
	}

	public boolean isEqual(final ThreadInstanceCounter other) {
		for (final String thread : other.getThreadInstances().keySet()) {
			final Integer count = mThreadInstances.get(thread);
			final Integer otherCount = other.getThreadInstances().get(thread);
			if (count != otherCount && !(count > 0 && otherCount > 0)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public String toString() {
		final StringBuilder resulString = new StringBuilder();
		for (final String thread : mThreadNameSet) {
			resulString.append(", ").append(thread).append("=").append(mThreadInstances.get(thread));
		}
		return resulString.toString();
	}
}
