package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class LocationAbstraction<LOC extends IcfgLocation> {
	private final Map<String, Integer> mPerThreadLocationCounterMap = new HashMap<>();
	private final Map<LOC, Integer> mLocId = new HashMap<>();
	private HeuristicLocationAbstraction<LOC> mHeuristicLocationAbstraction;

	public LocationAbstraction() {
	}

	StaticAbstractLocationMap<LOC> computeLocationAbstraction(final LocationAbstractionType type,
			final IUltimateServiceProvider services, final IIcfg<? extends LOC> icfg) {
		mHeuristicLocationAbstraction = new HeuristicLocationAbstraction<>(services, icfg);
		return switch (type) {
		case SINGLETON -> new StaticAbstractLocationMap<>((l -> 0), icfg);
		case SPLIT_AT_GUARDS -> mHeuristicLocationAbstraction.entryExitSplitting();
		case SPLIT_AT_GUARDS_AND_WRITES -> mHeuristicLocationAbstraction.allVarOccurencesSplit();
		case SPLIT_AT_EVERY_LOCATION -> new StaticAbstractLocationMap<>(
				l -> mLocId.computeIfAbsent(l, __ -> getAndIncrementThreadLocationCounter(l.getProcedure())), icfg);
		};
	}

	private int getAndIncrementThreadLocationCounter(final String thread) {
		final int counter = mPerThreadLocationCounterMap.getOrDefault(thread, 0);
		mPerThreadLocationCounterMap.put(thread, counter + 1);
		return counter;
	}
}
