package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;

public class LocationAbstraction {
	private final Map<String, Integer> mPerThreadLocationCounterMap = new HashMap<>();
	private final Map<String, Map<String, Integer>> mPerThreadKeyIds = new HashMap<>();
	private final Map<IcfgLocation, Integer> mLocId = new HashMap<>();

	public Map<IcfgLocation, Integer> computeLocationAbstraction(final LocationAbstractionType type,
			final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg, final MustLocksetAnalysis locksetInfo) {
		final var heuristics = new ControlPartitioningHeuristics(services, icfg);
		return switch (type) {
		case SINGLETON -> evaluateAll(l -> 0, icfg);
		case SPLIT_AT_GUARD -> heuristics.guardSplitting();
		case SPLIT_AT_GUARDS_AND_WRITES -> heuristics.allVarOccurrencesSplit();
		case SPLIT_AT_LOCKSETS -> evaluateAll(l -> locksetLocationId(l, locksetInfo), icfg);
		case SPLIT_AT_GUARDS_WRITES_AND_LOCKSETS -> {
			final Map<IcfgLocation, Integer> base = heuristics.allVarOccurrencesSplit();
			yield evaluateAll(l -> refinedLocksetLocationId(l, base, locksetInfo), icfg);
		}
		case SPLIT_AT_NONLOCK_GUARDS_WRITES_AND_LOCKSETS -> {
			final Map<IcfgLocation, Integer> base = heuristics.allVarOccurrencesSplit(locksetInfo.getLockVars());
			yield evaluateAll(l -> refinedLocksetLocationId(l, base, locksetInfo), icfg);
		}
		case SPLIT_AT_EVERY_LOCATION -> evaluateAll(
				l -> mLocId.computeIfAbsent(l, __ -> getAndIncrementThreadLocationCounter(l.getProcedure())), icfg);
		};
	}

	private Map<IcfgLocation, Integer> evaluateAll(final Function<IcfgLocation, Integer> mappingFunction,
			final IIcfg<IcfgLocation> icfg) {
		final Map<IcfgLocation, Integer> result = new LinkedHashMap<>();
		for (final IcfgLocation entryLoc : icfg.getProcedureEntryNodes().values()) {
			final IcfgLocationIterator<IcfgLocation> iter = new IcfgLocationIterator<>(entryLoc);
			while (iter.hasNext()) {
				result.computeIfAbsent(iter.next(), mappingFunction);
			}
		}
		return result;
	}

	private int locksetLocationId(final IcfgLocation loc, final MustLocksetAnalysis locksetInfo) {
		return idForKey(loc.getProcedure(), locksetKey(locksetInfo.mustLocksetAt(loc)));
	}

	private int refinedLocksetLocationId(final IcfgLocation loc, final Map<IcfgLocation, Integer> base,
			final MustLocksetAnalysis locksetInfo) {
		return idForKey(loc.getProcedure(), base.getOrDefault(loc, 0) + ":" + locksetKey(locksetInfo.mustLocksetAt(loc)));
	}

	private int idForKey(final String procedure, final String key) {
		final Map<String, Integer> ids = mPerThreadKeyIds.computeIfAbsent(procedure, __ -> new HashMap<>());
		return ids.computeIfAbsent(key, __ -> getAndIncrementThreadLocationCounter(procedure));
	}

	private static String locksetKey(final Set<String> lockset) {
		if (lockset.isEmpty()) {
			return "";
		}
		return lockset.stream().sorted().collect(Collectors.joining(","));
	}

	private int getAndIncrementThreadLocationCounter(final String thread) {
		final int counter = mPerThreadLocationCounterMap.getOrDefault(thread, 1);
		mPerThreadLocationCounterMap.put(thread, counter + 1);
		return counter;
	}
}
