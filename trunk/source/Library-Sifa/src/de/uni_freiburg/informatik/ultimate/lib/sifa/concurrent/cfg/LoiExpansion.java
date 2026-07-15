package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public final class LoiExpansion {

	private LoiExpansion() {
	}

	public static Collection<IcfgLocation> getLocationsOfInterestForThread(final String threadId,
			final IIcfg<IcfgLocation> threadIcfg, final Collection<IcfgLocation> requestedLois) {
		final Set<IcfgLocation> filtered = new LinkedHashSet<>();
		if (requestedLois != null) {
			for (final IcfgLocation loi : requestedLois) {
				if (loi != null && containsLocation(threadIcfg, loi)) {
					filtered.add(loi);
				}
			}
		}
		if (!filtered.isEmpty()) {
			return filtered;
		}
		final IcfgLocation entry = threadIcfg.getProcedureEntryNodes().get(threadId);
		if (entry != null) {
			filtered.add(entry);
		}
		final IcfgLocation exit = threadIcfg.getProcedureExitNodes().get(threadId);
		if (exit != null) {
			filtered.add(exit);
		}
		return filtered;
	}

	private static boolean containsLocation(final IIcfg<IcfgLocation> icfg, final IcfgLocation location) {
		return icfg.getProgramPoints().getOrDefault(location.getProcedure(), Map.of()).containsValue(location);
	}
}
