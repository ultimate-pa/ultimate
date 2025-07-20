package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

// TODO: Replace Integer usage with value-abstraction, so we can call abstractions on this
// TODO: make immutable
public class ThreadInstanceCounter<LOC extends IcfgLocation> {
	private final Map<String, Integer> mThreadInstances;
	private final Set<String> mThreadNameSet;
	private final Map<String, List<Integer>> mForkIds;
	private final Set<LOC> mSeenForks;

	public ThreadInstanceCounter(final ThreadInstanceCounter<LOC> counter, final Map<String, List<Integer>> map,
			final Set<LOC> set) {
		mThreadNameSet = counter.mThreadNameSet;
		mThreadInstances = counter.mThreadInstances;
		mForkIds = map;
		mSeenForks = set;
	}

	public ThreadInstanceCounter(final Map<String, Integer> threadMap, final Map<String, List<Integer>> map,
			final Set<LOC> set) {
		mThreadNameSet = threadMap.keySet();
		mThreadInstances = new HashMap<>(threadMap);
		mForkIds = map;
		mSeenForks = set;
	}

	public ThreadInstanceCounter(final Map<String, Integer> threadMap) {
		mThreadNameSet = threadMap.keySet();
		mThreadInstances = new HashMap<>(threadMap);
		mForkIds = new HashMap<>();
		mSeenForks = new HashSet<>();
	}

	public ThreadInstanceCounter(final ThreadInstanceCounter<LOC> other) {
		mThreadInstances = new HashMap<>(other.getThreadInstances());
		mThreadNameSet = new HashSet<>();
		getThreadNameSet().addAll(getThreadInstances().keySet());
		mForkIds = other.mForkIds;
		mSeenForks = other.mSeenForks;
	}

	public ThreadInstanceCounter<LOC> assignForkId(final String threadName, final int forkId, final LOC forkLoc,
			final boolean inLoop) {
		// special case: null used for bottom first state of main thread.
		if (forkLoc == null) {
			return setThreadsActive(Set.of(threadName));
		}

		if (!inLoop && mSeenForks.contains(forkLoc)) {
			return new ThreadInstanceCounter<>(this);
		}
		final var mapCopy = new HashMap<>(mForkIds);
		final var setCopy = new HashSet<>(mSeenForks);
		mapCopy.computeIfAbsent(threadName, k -> new ArrayList<>()).add(forkId);
		setCopy.add(forkLoc);

		ThreadInstanceCounter<LOC> oldCounter;
		if (inLoop || mapCopy.get(threadName).size() > 1) {
			oldCounter = setThreadsInf(Set.of(threadName));
		} else {
			oldCounter = setThreadsActive(Set.of(threadName));
		}
		return new ThreadInstanceCounter<>(oldCounter, mapCopy, setCopy);
	}

	public ThreadInstanceCounter<LOC> unassignForkId(final String threadName, final int forkId, final LOC forkLoc) {

		final var mapCopy = new HashMap<>(mForkIds);
		final var setCopy = new HashSet<>(mSeenForks);
		final List<Integer> list = mapCopy.get(threadName);
		if (list != null) {
			list.remove(Integer.valueOf(forkId));
		}
		setCopy.remove(forkLoc);

		// sets threads inactive only if theyre forked count is 1 (We abstract away anything aobve 1 to inf, so we
		// cannot know how many joins it would take to get it to 0).
		final var oldCounter = setThreadsInActive(Set.of(threadName));

		return new ThreadInstanceCounter<>(oldCounter, mapCopy, setCopy);
	}

	public List<Integer> getForkIds(final String threadId) {
		final List<Integer> forkList = mForkIds.get(threadId);
		return forkList == null ? List.of() : Collections.unmodifiableList(forkList);
	}

	public Map<String, List<Integer>> getAllForkIds() {
		final Map<String, List<Integer>> copy = new HashMap<>();
		for (final Map.Entry<String, List<Integer>> entry : mForkIds.entrySet()) {
			copy.put(entry.getKey(), List.copyOf(entry.getValue()));
		}
		return Collections.unmodifiableMap(copy);
	}

	public void reset() {
		mForkIds.clear();
	}

	public Set<String> getThreadNameSet() {
		return mThreadNameSet;
	}

	public Map<String, Integer> getThreadInstances() {
		return new HashMap<>(mThreadInstances);
	}

	public ThreadInstanceCounter<LOC> setThreadsActive(final Collection<String> threadName) {
		final var newInstanceMap = new HashMap<>(mThreadInstances);
		threadName.stream().filter(p -> newInstanceMap.get(p) != null).filter(p -> newInstanceMap.get(p) < 1)
				.forEach(p -> newInstanceMap.put(p, 1));
		return new ThreadInstanceCounter<>(newInstanceMap, mForkIds, mSeenForks);
	}

	public ThreadInstanceCounter<LOC> setThreadsInActive(final Collection<String> threadName) {
		final var newInstanceMap = new HashMap<>(mThreadInstances);
		threadName.stream().filter(p -> newInstanceMap.get(p) != null).filter(p -> newInstanceMap.get(p) == 1)
				.forEach(p -> newInstanceMap.put(p, 0));
		return new ThreadInstanceCounter<>(newInstanceMap, mForkIds, mSeenForks);
	}

	public ThreadInstanceCounter<LOC> setThreadsInf(final Collection<String> threadName) {
		final var newInstanceMap = new HashMap<>(mThreadInstances);
		threadName.stream().filter(p -> newInstanceMap.get(p) != null).forEach(p -> newInstanceMap.put(p, 2));
		return new ThreadInstanceCounter<>(newInstanceMap, mForkIds, mSeenForks);
	}

	public ThreadInstanceCounter<LOC> union(final ThreadInstanceCounter<LOC> other) {
		final Map<String, Integer> newThreadMap = new HashMap<>();
		final var mapCopy = new HashMap<>(mForkIds);
		final var setCopy = new HashSet<>(mSeenForks);
		for (final String thread : mThreadNameSet) {
			newThreadMap.put(thread,
					Math.max(getThreadInstances().get(thread), other.getThreadInstances().get(thread)));
		}
		final Map<String, List<Integer>> mapUnion = Stream.of(mForkIds, other.mForkIds)
				.flatMap(map -> map.entrySet().stream())
				.collect(Collectors.toMap(Map.Entry::getKey, e -> new ArrayList<>(e.getValue()), (l1, l2) -> {
					final List<Integer> merged = new ArrayList<>(l1);
					final Set<Integer> seen = new HashSet<>(l1);
					l2.stream().filter(i -> !seen.contains(i)).forEach(merged::add);
					return merged;
				}));
		setCopy.addAll(other.mSeenForks);

		return new ThreadInstanceCounter<>(newThreadMap, mapUnion, setCopy);
	}

	public ThreadInstanceCounter<LOC> intersect(final ThreadInstanceCounter<LOC> other) {
		final Map<String, Integer> newThreadMap = new HashMap<>();
		for (final String thread : mThreadNameSet) {
			newThreadMap.put(thread,
					Math.max(getThreadInstances().get(thread), other.getThreadInstances().get(thread)));
			// intersection would be none for the ghost variables -> we need to make state false
			if (getThreadInstances().get(thread) != other.getThreadInstances().get(thread)
					&& (getThreadInstances().get(thread) == 0 || other.getThreadInstances().get(thread) == 0)) {
				return null;
			}
			if ((getThreadInstances().get(thread) == other.getThreadInstances().get(thread))) {
				newThreadMap.put(thread, getThreadInstances().get(thread));
				// edge case, for observing thread 1==2, so an interference of an observer could shrink us from 2->1
			} else if ((getThreadInstances().get(thread) == 2 || other.getThreadInstances().get(thread) == 2)) {
				newThreadMap.put(thread, 2);
			} else {
				return null;
			}
		}
		if (!mForkIds.equals(other.mForkIds)) {
			return null;
		}
		if (!mSeenForks.equals(other.mSeenForks)) {
			return null;
		}
		final Map<String, List<Integer>> mapCopy = mForkIds.entrySet().stream()
				.collect(Collectors.toMap(Map.Entry::getKey, e -> new ArrayList<>(e.getValue())));

		final var setCopy = new HashSet<>(mSeenForks);
		return new ThreadInstanceCounter<>(newThreadMap, mapCopy, setCopy);
	}

	public boolean isEqualTo(final ThreadInstanceCounter<LOC> other) {
		for (final String thread : other.getThreadInstances().keySet()) {
			final Integer count = mThreadInstances.get(thread);
			final Integer otherCount = other.getThreadInstances().get(thread);
			if (count != otherCount) {
				return false;
			}
		}
		return true;
	}

	public SubsetResult isSubsetOf(final ThreadInstanceCounter<LOC> other) {
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
				resulString.append(", forkids: ").append(mForkIds.get(thread));
			} else {
				resulString.append(" ").append(thread).append("=").append(mThreadInstances.get(thread));
				resulString.append(", forkids: ").append(mForkIds.get(thread));
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
