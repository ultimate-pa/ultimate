package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;

public final class AbstractLocationMap<LOC extends IcfgLocation> {
	private final Map<LOC, Integer> mMap = new ConcurrentHashMap<>();
	private final Function<LOC, Integer> mMappingFunction;
	private final Map<String, ? extends LOC> mEntryLocs;
	// say we are thread 1, how many combinations of lcoations can thread 2 and thread 3 be in ?
	// assuming both have 2 abstract locations each -> 2*2 combinations
	// TOOD: just a heuristic upper limit(?) atm, make precise. (Need deterministic state reduction then too though)
	final Map<String, Integer> mLocationCountMap = new HashMap<>();
	private final Map<String, Integer> mMaxParallelLocationStates;
	private final Map<String, Set<LOC>> mFinalLocations = new HashMap<>();

	public AbstractLocationMap(final Function<LOC, Integer> mappingFunction,
			final Map<String, ? extends LOC> entryLocs) {
		mMappingFunction = mappingFunction;
		mEntryLocs = entryLocs;
		mMaxParallelLocationStates = new HashMap<>();
		computeMaxAndFinalLocs();
	}

	public int getAbstractEntryLoc(final String threadName) {
		return getAbstractLocation(mEntryLocs.get(threadName));
	}

	public Set<Integer> getAbstractFinalLoc(final String threadName) {
		return mFinalLocations.get(threadName).stream().map(l -> getAbstractLocation(l)).collect(Collectors.toSet());
	}

	public LOC getEntryLoc(final String threadName) {
		return mEntryLocs.get(threadName);
	}

	public int getAbstractLocation(final LOC loc) {
		return mMap.computeIfAbsent(loc, mMappingFunction);
	}

	public int abstractLocationCountOf(final String thread) {
		return mLocationCountMap.get(thread);
	}

	public int maxParallelOtherLocationsOf(final String thread) {
		return mMaxParallelLocationStates.get(thread);
	}

	public int maximumOfAll() {
		int max = 0;
		for (final String thread : mEntryLocs.keySet()) {
			if (thread.equals("ULTIMATE.start")) {
				continue;
			}
			max = Math.max(max, maxParallelOtherLocationsOf(thread));
		}
		return max;
	}

	private void computeMaxAndFinalLocs() {
		for (final LOC entryLoc : mEntryLocs.values()) {
			final String ownerThreadString = entryLoc.getProcedure();
			final Set<Integer> abstractLocationSet = new HashSet<>();
			int counter = 0;
			final IcfgLocationIterator<LOC> iter = new IcfgLocationIterator<>(entryLoc);
			while (iter.hasNext()) {
				final LOC loc = iter.next();
				final int abstraction = getAbstractLocation(loc);
				if (!abstractLocationSet.contains(abstraction)) {
					counter++;
				}
				abstractLocationSet.add(abstraction);
				if (!iter.hasNext()) {
					mFinalLocations.put(ownerThreadString, mFinalLocations.get(ownerThreadString));
				}
			}
			mLocationCountMap.put(ownerThreadString, counter);
		}
		for (final String thread : mEntryLocs.keySet()) {
			int maxCombinations = 1;
			for (final String otherThread : mEntryLocs.keySet()) {
				if (otherThread != thread) {
					maxCombinations = maxCombinations * mLocationCountMap.get(otherThread);
				}
			}
			// respecting Threadcounter combinations
			maxCombinations = maxCombinations * 2;
			mMaxParallelLocationStates.put(thread, maxCombinations);
		}
	}
}
