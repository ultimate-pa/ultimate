package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class AbstractLocationGlobalTracker {
	private final Map<String, Set<Integer>> mThreadLocationMap;
	private final Map<String, Set<Integer>> mSelfMap;

	public AbstractLocationGlobalTracker(final Set<String> threadNameSet, final AbstractLocationMap<?> globalMap) {
		// initially all threads at line/location = x as defined by globalMap
		mThreadLocationMap = threadNameSet.stream()
				.collect(Collectors.toMap(t -> t, t -> Set.of(globalMap.getAbstractEntryLoc(t))));
		mSelfMap = threadNameSet.stream()
				.collect(Collectors.toMap(t -> t, t -> Set.of(globalMap.getAbstractEntryLoc(t))));
	}

	public AbstractLocationGlobalTracker(final Map<String, Set<Integer>> locMap,
			final Map<String, Set<Integer>> selfMap) {
		mThreadLocationMap = new HashMap<>(locMap);
		mSelfMap = new HashMap<>(selfMap);
	}

	public AbstractLocationGlobalTracker(final AbstractLocationGlobalTracker other) {
		mThreadLocationMap = other.threadLocationMap();
		mSelfMap = other.selfMap();
	}

	public Set<Integer> getLocationForThread(final String thread) {
		return mThreadLocationMap.get(thread);
	}

	public Set<Integer> getLocationForSelfThread(final String thread) {
		return mSelfMap.get(thread);
	}

	// TODO: do we care that caller could change lists? if not maybe dont waste time doing deep unmodifiable copies
	public Map<String, Set<Integer>> threadLocationMap() {
		return mThreadLocationMap.entrySet().stream()
				.collect(Collectors.toUnmodifiableMap(Map.Entry::getKey, entry -> Set.copyOf(entry.getValue())));
	}

	public Map<String, Set<Integer>> selfMap() {
		return mSelfMap.entrySet().stream()
				.collect(Collectors.toUnmodifiableMap(Map.Entry::getKey, entry -> Set.copyOf(entry.getValue())));
	}

	public AbstractLocationGlobalTracker movedTo(final String movingThread, final int locationOrigin,
			final int locationTarget) {
		final var newMap = new HashMap<>(mThreadLocationMap);
		final var newSelfMap = new HashMap<>(mSelfMap);
		final var mainThreadLocations = newMap.get(movingThread);
		final var nonMainThreadLocations = newMap.get(movingThread);
		if (locationOrigin == -1 || mainThreadLocations.contains(locationOrigin)) {
			newMap.put(movingThread, Set.of(locationTarget));
		} else if (nonMainThreadLocations.contains(locationOrigin)) {
			newSelfMap.put(movingThread, Set.of(locationTarget));
		} else {
			throw new IllegalStateException("Trying to apply interference not backed by location.");
		}
		return new AbstractLocationGlobalTracker(newMap, newSelfMap);
	}

	public AbstractLocationGlobalTracker movedInf(final String movingThread, final int locationOrigin,
			final int locationTarget, final int abstractEntryLoc) {
		final var newMap = new HashMap<>(mThreadLocationMap);
		final var newSelfMap = new HashMap<>(mSelfMap);
		final var mainThreadLocations = newMap.get(movingThread);
		final var nonMainThreadLocations = newMap.get(movingThread);
		final var newSet = new HashSet<>(newMap.get(movingThread));
		if (mainThreadLocations.contains(locationOrigin)) {
			newSet.clear();
			newSet.add(locationTarget);
			newSet.add(abstractEntryLoc);
			newMap.put(movingThread, newSet);
		} else if (nonMainThreadLocations.contains(locationOrigin)) {
			newSet.clear();
			newSet.add(locationTarget);
			newSet.add(abstractEntryLoc);
			newSelfMap.put(movingThread, newSet);
		} else {
			throw new IllegalStateException("Trying to apply interference not backed by location.");
		}
		return new AbstractLocationGlobalTracker(newMap, newSelfMap);
	}

	public AbstractLocationGlobalTracker selfMoved(final String movingThread, final int newLocation) {
		final var newMap = new HashMap<>(mSelfMap);
		newMap.put(movingThread, Set.of(newLocation));
		return new AbstractLocationGlobalTracker(new HashMap<>(mThreadLocationMap), newMap);
	}

	public AbstractLocationGlobalTracker selfMovedInf(final String movingThread, final int newLocation,
			final int abstractEntryLoc) {
		final var newMap = new HashMap<>(mSelfMap);
		final var newSet = new HashSet<>(newMap.get(movingThread));
		newSet.clear();
		newSet.add(newLocation);
		newSet.add(abstractEntryLoc);
		newMap.put(movingThread, newSet);
		return new AbstractLocationGlobalTracker(mThreadLocationMap, newMap);
	}

	public AbstractLocationGlobalTracker union(final AbstractLocationGlobalTracker other) {
		final var newMap = new HashMap<>(mThreadLocationMap);
		other.threadLocationMap().forEach((key, value) -> newMap.merge(key, value, DataStructureUtils::union));
		final var newSelfMap = new HashMap<>(mSelfMap);
		other.selfMap().forEach((key, value) -> newSelfMap.merge(key, value, DataStructureUtils::union));
		return new AbstractLocationGlobalTracker(newMap, newSelfMap);
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
			if (intersection.isEmpty()) {
				return null;
			}
			newMap.put(key, intersection);
		}
		final var newSelfMap = new HashMap<>(mSelfMap);

		for (final var entry : other.selfMap().entrySet()) {
			final var key = entry.getKey();
			final var otherValue = entry.getValue();
			final var thisValue = mSelfMap.get(key);
			if (thisValue == null) {
				return null;
			}
			final var intersection = DataStructureUtils.intersection(thisValue, otherValue);
			if (intersection == null) {
				return null;
			}
			if (intersection.isEmpty()) {
				return null;
			}
			newSelfMap.put(key, intersection);
		}
		return new AbstractLocationGlobalTracker(newMap, newSelfMap);
	}

	public AbstractLocationGlobalTracker selfinterSect(final AbstractLocationGlobalTracker other) {
		final var newMap = new HashMap<>(mThreadLocationMap);
		final var newSelfMap = new HashMap<>(mSelfMap);
		return new AbstractLocationGlobalTracker(newMap, newSelfMap);
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
				overall = SubsetResult.STRICT;
			}
		}
		SubsetResult overallTwo = SubsetResult.EQUAL;
		for (final String thread : mSelfMap.keySet()) {
			final Set<Integer> leftSet = mSelfMap.get(thread);
			final Set<Integer> rightSet = other.mSelfMap.get(thread);
			if (!isSubsetOfSet(leftSet, rightSet)) {
				return SubsetResult.NONE;
			}
			if (!Objects.equals(leftSet, rightSet)) {
				overallTwo = SubsetResult.STRICT;
			}
		}
		return overall.min(overallTwo);
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
		if (mSelfMap.size() != other.mSelfMap.size()) {
			return false;
		}
		for (final String thread : mSelfMap.keySet()) {
			final Set<Integer> left = mSelfMap.get(thread);
			final Set<Integer> right = other.mSelfMap.get(thread);
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
		return Objects.equals(mThreadLocationMap, other.mThreadLocationMap) && Objects.equals(mSelfMap, other.mSelfMap);
	}

	@Override
	public int hashCode() {
		return Objects.hash(mThreadLocationMap);
	}

}
