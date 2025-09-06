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
		case "Singleton, Fast Widening", "Singleton, Slow Widening" -> new StaticAbstractLocationMap<>((l -> 0), icfg);
		case "Low Split, Fast Widening", "Low Split, Slow Widening" ->
			mHeuristicLocationAbstraction.entryExitSplitting();
		case "High Split, Fast Widening", "High Split, Slow Widening" ->
			mHeuristicLocationAbstraction.allVarOccurencesSplit();
		default -> new StaticAbstractLocationMap<>((l -> 0), icfg);
		};

		return absMap;
	}
}
