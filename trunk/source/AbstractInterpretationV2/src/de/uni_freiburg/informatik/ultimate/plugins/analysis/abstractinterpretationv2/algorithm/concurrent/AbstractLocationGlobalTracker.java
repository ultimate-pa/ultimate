package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class AbstractLocationGlobalTracker {
	private final Map<String, Set<Integer>> mThreadLocationMap;

	public AbstractLocationGlobalTracker(final Set<String> threadNameSet, final AbstractLocationMap<?> globalMap) {
		// initially all threads at line/location = x as defined by globalMap
		mThreadLocationMap = threadNameSet.stream()
				.collect(Collectors.toMap(t -> t, t -> Set.of(globalMap.getAbstractEntryLoc(t))));
	}

	public AbstractLocationGlobalTracker(final Map<String, Set<Integer>> locMap) {
		mThreadLocationMap = new HashMap<>(locMap);
	}

	public AbstractLocationGlobalTracker(final AbstractLocationGlobalTracker other) {
		mThreadLocationMap = other.threadLocationMap();
	}

	public Set<Integer> getLocationForThread(final String thread) {
		return mThreadLocationMap.get(thread);
	}

	// TODO: do we care that caller could change lists? if not maybe dont waste time doing deep unmodifiable copies
	public Map<String, Set<Integer>> threadLocationMap() {
		// return new HashMap<>(mThreadLocationMap);
		return mThreadLocationMap.entrySet().stream()
				.collect(Collectors.toUnmodifiableMap(Map.Entry::getKey, entry -> Set.copyOf(entry.getValue())));
	}

	public AbstractLocationGlobalTracker movedTo(final String movingThread, final int newLocation) {
		final var newMap = new HashMap<>(mThreadLocationMap);
		newMap.put(movingThread, Set.of(newLocation));
		return new AbstractLocationGlobalTracker(newMap);
	}

	public AbstractLocationGlobalTracker union(final AbstractLocationGlobalTracker other) {
		final var newMap = new HashMap<>(mThreadLocationMap);
		other.threadLocationMap().forEach((key, value) -> newMap.merge(key, value, DataStructureUtils::union));
		return new AbstractLocationGlobalTracker(newMap);
	}

	public AbstractLocationGlobalTracker intersect(final AbstractLocationGlobalTracker other) {
		final var newMap = new HashMap<>(mThreadLocationMap);
		for (final var entry : other.threadLocationMap().entrySet()) {
			final var key = entry.getKey();
			final var otherValue = entry.getValue();
			final var thisValue = mThreadLocationMap.get(key);
			if (thisValue == null) {
				return null;
			}
			final var intersection = DataStructureUtils.intersection(thisValue, otherValue);
			if (intersection == null) {
				return null;
			}
			newMap.put(key, intersection);
		}
		return new AbstractLocationGlobalTracker(newMap);
	}

	public SubsetResult isSubsetOf(final AbstractLocationGlobalTracker other) {
		SubsetResult overall = SubsetResult.EQUAL;
		for (final String thread : mThreadLocationMap.keySet()) {
			final Set<Integer> leftSet = mThreadLocationMap.get(thread);
			final Set<Integer> rightSet = other.mThreadLocationMap.get(thread);
			if (!isSubsetOfSet(leftSet, rightSet)) {
				return SubsetResult.NONE;
			}
			if (!Objects.equals(leftSet, rightSet)) {
				overall = overall.min(SubsetResult.STRICT);
			}
		}
		return overall;
	}

	private boolean isSubsetOfSet(final Set<Integer> left, final Set<Integer> right) {
		if (left == null || right == null) {
			return false;
		}
		return right.containsAll(left);
	}

	public boolean isEqualTo(final AbstractLocationGlobalTracker other) {
		if (other == null) {
			return false;
		}
		if (mThreadLocationMap.size() != other.mThreadLocationMap.size()) {
			return false;
		}
		for (final String thread : mThreadLocationMap.keySet()) {
			final Set<Integer> left = mThreadLocationMap.get(thread);
			final Set<Integer> right = other.mThreadLocationMap.get(thread);
			if (!left.containsAll(right)) {
				return false;
			}
			if (!right.containsAll(left)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public boolean equals(final Object o) {
		if (this == o) {
			return true;
		}
		if (!(o instanceof AbstractLocationGlobalTracker)) {
			return false;
		}
		final AbstractLocationGlobalTracker other = (AbstractLocationGlobalTracker) o;
		return Objects.equals(mThreadLocationMap, other.mThreadLocationMap);
	}

	@Override
	public int hashCode() {
		return Objects.hash(mThreadLocationMap);
	}

}
