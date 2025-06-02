package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;

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
			if (getThreadInstances().get(thread) != other.getThreadInstances().get(thread)
					&& (getThreadInstances().get(thread) == 0 || other.getThreadInstances().get(thread) == 0)) {
				return null;
			}
			if ((getThreadInstances().get(thread) == 0 || other.getThreadInstances().get(thread) == 0)) {
				newThreadMap.put(thread,
						Math.min(getThreadInstances().get(thread), other.getThreadInstances().get(thread)));
				// edge case, for observing thread 1==2, so an interference of an observer could shrink us from 2->1
			} else {
				newThreadMap.put(thread,
						Math.max(getThreadInstances().get(thread), other.getThreadInstances().get(thread)));
			}
		}
		return new ThreadInstanceCounter(newThreadMap);
	}

	public boolean isEqualTo(final ThreadInstanceCounter other) {
		for (final String thread : other.getThreadInstances().keySet()) {
			final Integer count = mThreadInstances.get(thread);
			final Integer otherCount = other.getThreadInstances().get(thread);
			if (count != otherCount) {
				return false;
			}
		}
		return true;
	}

	public SubsetResult isSubsetOf(final ThreadInstanceCounter other) {
		final SubsetResult result = SubsetResult.EQUAL;
		for (final String thread : mThreadNameSet) {
			final int leftCount = mThreadInstances.get(thread);
			final int rightCount = other.getThreadInstances().get(thread);
			// We say anything above 0 is equal for now, since seeing another thread as being forked 1 or 2 times
			// does not change anything for our current model.
			// TODO:
			if (!(leftCount == rightCount)) {
				return SubsetResult.NONE;
			}
		}
		return result;
	}

	@Override
	public String toString() {
		final StringBuilder resulString = new StringBuilder();
		for (final String thread : mThreadNameSet) {
			if (resulString.isEmpty()) {
				resulString.append(thread).append("=").append(mThreadInstances.get(thread));

			} else {
				resulString.append(" ").append(thread).append("=").append(mThreadInstances.get(thread));

			}
		}
		return resulString.toString();
	}

	@Override
	public boolean equals(final Object o) {
		if (this == o) {
			return true;
		}
		if (!(o instanceof final ThreadInstanceCounter other)) {
			return false;
		}
		return mThreadInstances.equals(other.mThreadInstances);
	}

	@Override
	public int hashCode() {
		return mThreadInstances.hashCode();
	}
}
