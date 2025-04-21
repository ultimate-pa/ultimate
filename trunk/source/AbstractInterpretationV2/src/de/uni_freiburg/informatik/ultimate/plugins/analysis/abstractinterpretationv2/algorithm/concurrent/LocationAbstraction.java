package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class LocationAbstraction<LOC extends IcfgLocation> {
	private final Map<String, ? extends LOC> mEntryLocs;
	private final Map<String, Integer> mPerThreadLocationCounterMap = new HashMap<>();

	public LocationAbstraction(final Map<String, ? extends LOC> entryLocs) {
		mEntryLocs = entryLocs;
	}

	public AbstractLocationMap<LOC> computeLocationAbstraction(final String locationAbstraction,
			final IUltimateServiceProvider services, final IIcfg<? extends LOC> icfg) {
		// TODO: enum for setting strings
		// TODO: parametrize countervalues
		final HeuristicLocationAbstraction<LOC> heuristicsAbstraction = new HeuristicLocationAbstraction<>(services,
				icfg);
		final AbstractLocationMap<LOC> absMap = switch (locationAbstraction) {
		case "Singleton" -> new AbstractLocationMap<>((l -> 1), mEntryLocs);
		case "Fully precise" ->
			new AbstractLocationMap<>((l -> getAndIncrementThreadLocationCounter(l.getProcedure())), mEntryLocs);
		case "Heuristic splitting" -> heuristicsAbstraction.computeLocationAbstraction();
		default -> new AbstractLocationMap<>((l -> 1), mEntryLocs);
		};
		return absMap;
	}

	private int getAndIncrementThreadLocationCounter(final String thread) {
		final int counter = mPerThreadLocationCounterMap.getOrDefault(thread, 0);
		mPerThreadLocationCounterMap.put(thread, counter + 1);
		return counter;
	}

}
