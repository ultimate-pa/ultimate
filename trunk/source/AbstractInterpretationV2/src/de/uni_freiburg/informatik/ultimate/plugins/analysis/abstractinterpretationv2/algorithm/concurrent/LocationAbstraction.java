package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class LocationAbstraction<LOC extends IcfgLocation> {
	private final Map<String, Integer> mPerThreadLocationCounterMap = new HashMap<>();
	private HeuristicLocationAbstraction<LOC> mHeuristicLocationAbstraction;

	public LocationAbstraction() {
	}

	public StaticAbstractLocationMap<LOC> computeLocationAbstraction(final String locationAbstraction,
			final IUltimateServiceProvider services, final IIcfg<? extends LOC> icfg) {
		// TODO: enum for setting strings
		// TODO: parametrize countervalues
		mHeuristicLocationAbstraction = new HeuristicLocationAbstraction<>(services, icfg);
		final StaticAbstractLocationMap<LOC> absMap = switch (locationAbstraction) {
		case "Singleton" -> new StaticAbstractLocationMap<>((l -> 1), icfg);
		case "Split at Guards and Exit" -> mHeuristicLocationAbstraction.mutexVarSplitting();
		default -> mHeuristicLocationAbstraction.mutexVarSplitting();
		};
		return absMap;
	}

	private int getAndIncrementThreadLocationCounter(final String thread) {
		final int counter = mPerThreadLocationCounterMap.getOrDefault(thread, 0);
		mPerThreadLocationCounterMap.put(thread, counter + 1);
		return counter;
	}
}
