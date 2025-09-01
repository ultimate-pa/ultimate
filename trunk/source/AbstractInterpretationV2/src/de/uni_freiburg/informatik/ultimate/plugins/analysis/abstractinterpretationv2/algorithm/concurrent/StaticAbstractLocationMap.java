package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;

public final class StaticAbstractLocationMap<LOC extends IcfgLocation> {
	private final Map<LOC, Integer> mMap = new ConcurrentHashMap<>();
	private final Function<LOC, Integer> mMappingFunction;
	private final Map<String, LOC> mEntryLocs;
	// say we are thread 1, how many combinations of lcoations can thread 2 and thread 3 be in ?
	// assuming both have 2 abstract locations each -> 2*2 combinations
	// TOOD: just a heuristic upper limit(?) atm, make precise. (Need deterministic state reduction then too though)
	final Map<String, Integer> mLocationCountMap = new HashMap<>();
	private final Map<String, Integer> mMaxParallelLocationStates;
	private final Map<String, LOC> mFinalLocations = new HashMap<>();
	private final IIcfg<LOC> mCfg;

	public StaticAbstractLocationMap(final Function<LOC, Integer> mappingFunction, final IIcfg<?> cfg) {
		mMappingFunction = mappingFunction;
		mMaxParallelLocationStates = new HashMap<>();
		mCfg = (IIcfg<LOC>) cfg;
		mEntryLocs = mCfg.getProcedureEntryNodes();
		computeMaxAndFinalLocs();
	}

	public int getAbstractEntryLoc(final String threadName) {
		return getAbstractLocation(mEntryLocs.get(threadName));
	}

	// -1 bei exit locs, und hole sie manuell aus icfg
	// icfg.getgprocedureexitnodes
	public Integer getAbstractFinalLoc(final String threadName) {
		return getAbstractLocation(mCfg.getProcedureExitNodes().get(threadName));
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

	private void computeMaxAndFinalLocs() {
		mEntryLocs.keySet().forEach(t -> mFinalLocations.put(t, mCfg.getProcedureExitNodes().get(t)));
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
			}
			mLocationCountMap.put(ownerThreadString, counter);
		}
	}
}
