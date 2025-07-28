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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalValue;

public class ThreadInstanceCounter<LOC extends IcfgLocation> {
	private final Map<String, IntervalDomainValue> mThreadCounts;
	private final Set<String> mThreadNameSet;
	private final Map<String, List<Integer>> mForkIds;
	private final Set<LOC> mSeenForks;

	public ThreadInstanceCounter(final ThreadInstanceCounter<LOC> other) {
		mThreadCounts = new HashMap<>(other.mThreadCounts);
		mThreadNameSet = new HashSet<>(other.mThreadNameSet);
		mForkIds = new HashMap<>();
		for (final Map.Entry<String, List<Integer>> entry : other.mForkIds.entrySet()) {
			mForkIds.put(entry.getKey(), new ArrayList<>(entry.getValue()));
		}
		mSeenForks = new HashSet<>(other.mSeenForks);
	}

	public ThreadInstanceCounter(final Map<String, IntervalDomainValue> threadMap,
			final Map<String, List<Integer>> forkMap, final Set<LOC> seenForks) {
		mThreadCounts = new HashMap<>(threadMap);
		mThreadNameSet = new HashSet<>(threadMap.keySet());
		mForkIds = new HashMap<>();
		for (final Map.Entry<String, List<Integer>> entry : forkMap.entrySet()) {
			mForkIds.put(entry.getKey(), new ArrayList<>(entry.getValue()));
		}
		mSeenForks = new HashSet<>(seenForks);
	}

	public ThreadInstanceCounter(final Map<String, IntervalDomainValue> threadMap) {
		this(threadMap, threadMap.keySet().stream().collect(Collectors.toMap(t -> t, t -> new ArrayList<>())),
				Collections.emptySet());
	}

	public ThreadInstanceCounter(final ThreadInstanceCounter<LOC> other, final Map<String, List<Integer>> forkMap,
			final Set<LOC> seenForks) {
		this(other.getThreadInstances(), forkMap, seenForks);
	}

	public Map<String, IntervalDomainValue> getThreadInstances() {
		return Collections.unmodifiableMap(mThreadCounts);
	}

	public Set<String> getThreadNameSet() {
		return Collections.unmodifiableSet(mThreadNameSet);
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
		mapCopy.get(threadName).add(forkId);
		setCopy.add(forkLoc);

		final ThreadInstanceCounter<LOC> oldCounter;
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

		// sets threads inactive only if theyre forked count is 1 (We abstract away anything aobve 1 to inf, so we
		// cannot know how many joins it would take to get it to 0).
		var newCounter = new ThreadInstanceCounter<>(this);
		if (list.isEmpty()) {
			newCounter = newCounter.setThreadsInActive(Set.of(threadName));
		}

		return new ThreadInstanceCounter<>(newCounter, mapCopy, setCopy);
	}

	public Map<String, List<Integer>> getAllForkIds() {
		final Map<String, List<Integer>> copy = new HashMap<>();
		for (final Map.Entry<String, List<Integer>> entry : mForkIds.entrySet()) {
			copy.put(entry.getKey(), List.copyOf(entry.getValue()));
		}
		return Collections.unmodifiableMap(copy);
	}

	public ThreadInstanceCounter<LOC> setThreadsActive(final Collection<String> threadName) {
		final var newInstanceMap = new HashMap<>(mThreadCounts);
		final IntervalDomainValue one = new IntervalDomainValue(1, 1);
		threadName.stream().filter(p -> newInstanceMap.get(p) != null)
				.filter(p -> newInstanceMap.get(p).getUpper().getValue() != null)
				.filter(p -> newInstanceMap.get(p).getUpper().getValue().intValue() < 1)
				.forEach(p -> newInstanceMap.put(p, one));
		return new ThreadInstanceCounter<>(newInstanceMap, mForkIds, mSeenForks);
	}

	public ThreadInstanceCounter<LOC> setThreadsInActive(final Collection<String> threadName) {
		final var newInstanceMap = new HashMap<>(mThreadCounts);
		final IntervalDomainValue zero = new IntervalDomainValue(0, 0);
		threadName.stream().filter(p -> newInstanceMap.get(p) != null)
				.filter(p -> newInstanceMap.get(p).getUpper().getValue() != null)
				.filter(p -> newInstanceMap.get(p).getUpper().getValue().intValue() > 0)
				.forEach(p -> newInstanceMap.put(p, zero));
		return new ThreadInstanceCounter<>(newInstanceMap, mForkIds, mSeenForks);
	}

	// make threadcounter [x, inf] from [x,y]
	public ThreadInstanceCounter<LOC> setThreadsInf(final Collection<String> threadName) {
		final var newInstanceMap = new HashMap<>(mThreadCounts);
		threadName.stream().filter(p -> newInstanceMap.get(p) != null).forEach(p -> newInstanceMap.put(p,
				new IntervalDomainValue(newInstanceMap.get(p).getLower(), new IntervalValue())));
		return new ThreadInstanceCounter<>(newInstanceMap, mForkIds, mSeenForks);
	}

	public ThreadInstanceCounter<LOC> union(final ThreadInstanceCounter<LOC> other) {
		final Map<String, IntervalDomainValue> newThreadMap = new HashMap<>();
		final var mapCopy = new HashMap<>(mForkIds);
		final var setCopy = new HashSet<>(mSeenForks);
		for (final String thread : mThreadNameSet) {
			newThreadMap.put(thread, (getThreadInstances().get(thread).merge(other.getThreadInstances().get(thread))));
		}
		// Union of two lists, we dont want to duplicate. Would need unique identifier to properly union,
		// since pure Integer forkIDs not distinguishable. But matches current Ultimate fork translation
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
		final Map<String, IntervalDomainValue> newThreadMap = new HashMap<>();
		for (final String thread : mThreadNameSet) {
			final var intersection = getThreadInstances().get(thread).intersect(other.getThreadInstances().get(thread));
			if (intersection.isBottom()) {
				return null;
			}
			newThreadMap.put(thread, (intersection));
		}
		// TODO: this only works if we care about THIS, not other counter. Implement proper intersection if needed
		final var mapCopy = new HashMap<>(mForkIds);
		final var setCopy = new HashSet<>(mSeenForks);
		return new ThreadInstanceCounter<>(newThreadMap, mapCopy, setCopy);
	}

	public boolean isEqualTo(final ThreadInstanceCounter<LOC> other) {
		for (final String thread : other.getThreadInstances().keySet()) {
			final var count = mThreadCounts.get(thread);
			final var otherCount = other.getThreadInstances().get(thread);
			if (!count.isAbstractionEqual(otherCount)) {
				return false;
			}
		}
		return true;
	}

	public SubsetResult isSubsetOf(final ThreadInstanceCounter<LOC> other) {
		final SubsetResult result = SubsetResult.EQUAL;
		for (final String thread : mThreadNameSet) {
			final var leftCount = mThreadCounts.get(thread);
			final var rightCount = other.getThreadInstances().get(thread);
			if (!(leftCount.isContainedIn(rightCount))) {
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
				resulString.append(thread).append("=").append(mThreadCounts.get(thread));
				resulString.append(", forkids: ").append(mForkIds.get(thread));
			} else {
				resulString.append(" ").append(thread).append("=").append(mThreadCounts.get(thread));
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
		return mThreadCounts.equals(other.mThreadCounts);
	}

	@Override
	public int hashCode() {
		return mThreadCounts.hashCode();
	}
}
