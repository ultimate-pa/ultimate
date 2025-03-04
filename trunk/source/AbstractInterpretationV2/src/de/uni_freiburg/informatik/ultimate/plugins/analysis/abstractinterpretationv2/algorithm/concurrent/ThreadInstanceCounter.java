package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

// TODO: Replace Integer usage with value-abstraction, so we can call abstractions on this
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

	public void reset() {
		for (final String string : mThreadNameSet) {
			mThreadInstances.put(string, 0);
		}
	}

	public void incrementThread(final String threadName) {
		if (mThreadInstances.get(threadName) == null) {
			throw new IllegalArgumentException("Trying to increment thread which does not exist: " + threadName);
		}
		final int newCount = Math.min(2, mThreadInstances.get(threadName) + 1);
		mThreadInstances.put(threadName, newCount);
	}

	public void setThread(final String threadName, final int newNum) {
		mThreadInstances.put(threadName, newNum);
	}

	public void setActive(final String threadName) {
		if (mThreadInstances.get(threadName) == null) {
			throw new IllegalArgumentException("Trying to increment thread which does not exist: " + threadName);
		}
		if (mThreadInstances.get(threadName) <= 1) {
			mThreadInstances.put(threadName, 1);
		}
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

	@Override
	public String toString() {
		final StringBuilder resulString = new StringBuilder();
		for (final String thread : mThreadNameSet) {
			resulString.append(", ").append(thread).append("=").append(mThreadInstances.get(thread));
		}
		return resulString.toString();
	}
}
