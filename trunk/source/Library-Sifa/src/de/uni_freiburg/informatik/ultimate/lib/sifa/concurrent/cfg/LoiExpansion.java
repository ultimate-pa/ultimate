package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.Collection;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;

/**
 * Helper class to handle the expansion of locations of interest (LOIs) for
 * thread-modular analysis.
 */
public class LoiExpansion {

    private final ILogger mLogger;

    public LoiExpansion(final ILogger logger) {
        mLogger = logger;
    }

    /**
     * Gets the locations of interest for a specific thread.
     *
     * For thread-modular analysis we always interpret the complete thread ICFG, i.e., all reachable locations.
     */
    public Collection<IcfgLocation> getLocationsOfInterestForThread(final String threadId,
            final IIcfg<IcfgLocation> threadIcfg) {
        final Set<IcfgLocation> expanded = allReachableLocations(threadIcfg);
        mLogger.debug("Thread " + threadId + " LOIs expanded to all reachable locations: " + expanded.size());
        return expanded;
    }

    private Set<IcfgLocation> allReachableLocations(final IIcfg<IcfgLocation> icfg) {
        return IcfgLocationIterator.asStream(icfg).collect(Collectors.toSet());
    }
}
