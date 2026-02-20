package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class LoiExpansion {

	public LoiExpansion() {
	}

	public Collection<IcfgLocation> getLocationsOfInterestForThread(final String threadId,
			final IIcfg<IcfgLocation> threadIcfg) {
		return allLocationsFromProgramPoints(threadIcfg);
	}

	private static Set<IcfgLocation> allLocationsFromProgramPoints(final IIcfg<IcfgLocation> icfg) {
		final Set<IcfgLocation> result = new LinkedHashSet<>();
		for (final var procedureLocs : icfg.getProgramPoints().values()) {
			result.addAll(procedureLocs.values());
		}
		return result;
	}
}
