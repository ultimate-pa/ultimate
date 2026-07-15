package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping.AbstractLocationPair;

public record InterferenceGroupKey(String threadId, AbstractLocationPair abstractLocations, Set<String> lockset,
		String forkedThreadId, Set<IcfgLocation> sourceLocations) {
	public InterferenceGroupKey {
		lockset = Set.copyOf(lockset);
		sourceLocations = Set.copyOf(sourceLocations);
	}
}
