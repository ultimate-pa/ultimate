package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Helper class to handle the expansion of locations of interest (LOIs) for
 * thread-modular analysis.
 */
public class LoiExpansion {

    private final ILogger mLogger;
    private final Collection<IcfgLocation> mGlobalLois;
    private final IIcfg<IcfgLocation> mIcfg;
    private final LoiMode mLoiMode;

    public LoiExpansion(final ILogger logger, final Collection<IcfgLocation> globalLois,
            final IIcfg<IcfgLocation> icfg, final LoiMode loiMode) {
        mLogger = logger;
        mGlobalLois = globalLois;
        mIcfg = icfg;
        mLoiMode = loiMode;
    }

    /**
     * Gets locations of interest for a specific thread. If the thread contains LOIs
     * from the global set, those are
     * returned. Otherwise, the thread's exit node is used as a LOI to ensure the
     * thread is fully traversed for
     * interference collection.
     */
    public Collection<IcfgLocation> getLocationsOfInterestForThread(final String threadId,
            final IIcfg<IcfgLocation> threadIcfg) {
        // Filter global LOIs to those in this thread's procedure
        final Collection<IcfgLocation> threadLois = mGlobalLois.stream()
                .filter(loc -> threadId.equals(loc.getProcedure())).toList();

        final Collection<IcfgLocation> baseLois;
        if (!threadLois.isEmpty()) {
            baseLois = threadLois;
        } else {
            // No LOIs in this thread - use exit node to ensure full traversal for
            // interference collection
            final IcfgLocation exitNode = mIcfg.getProcedureExitNodes().get(threadId);
            if (exitNode != null) {
                mLogger.debug("Thread " + threadId + " has no LOIs, using exit node for traversal");
                baseLois = Set.of(exitNode);
            } else {
                // Fallback: use entry node
                final IcfgLocation entryNode = mIcfg.getProcedureEntryNodes().get(threadId);
                if (entryNode != null) {
                    mLogger.debug("Thread " + threadId + " has no LOIs or exit node, using entry node");
                    baseLois = Set.of(entryNode);
                } else {
                    mLogger.warn("Thread " + threadId + " has no entry or exit nodes");
                    baseLois = Set.of();
                }
            }
        }

        switch (mLoiMode) {
            case ALL_REACHABLE: {
                final Set<IcfgLocation> expanded = allReachableLocations(threadIcfg);
                mLogger.debug("Thread " + threadId + " LOIs expanded to all reachable locations: " + expanded.size());
                return expanded;
            }
            case PATH_TO_LOIS: {
                final Set<IcfgLocation> expanded = locationsOnPathsTo(threadIcfg, baseLois);
                if (expanded.isEmpty()) {
                    mLogger.debug("Thread " + threadId + " LOI expansion yielded empty set, falling back to base LOIs");
                    return baseLois;
                }
                mLogger.debug(
                        "Thread " + threadId + " LOIs expanded to locations on paths to base LOIs: " + expanded.size());
                return expanded;
            }
            case DEFAULT:
            default:
                return baseLois;
        }
    }

    private Set<IcfgLocation> allReachableLocations(final IIcfg<IcfgLocation> icfg) {
        final Set<IcfgLocation> visited = new HashSet<>();
        final Deque<IcfgLocation> work = new ArrayDeque<>();
        for (final IcfgLocation init : icfg.getInitialNodes()) {
            if (visited.add(init)) {
                work.add(init);
            }
        }
        while (!work.isEmpty()) {
            final IcfgLocation cur = work.removeFirst();
            for (final IcfgEdge e : cur.getOutgoingEdges()) {
                final IcfgLocation tgt = e.getTarget();
                if (tgt != null && visited.add(tgt)) {
                    work.add(tgt);
                }
            }
        }
        return visited;
    }

    private Set<IcfgLocation> locationsOnPathsTo(final IIcfg<IcfgLocation> icfg,
            final Collection<IcfgLocation> targets) {
        // Forward set: all locations reachable from entry
        // We use this as a 'universe' for the backward traversal to ensure we filter
        // out dead code
        // or code not reachable from entry.
        final Set<IcfgLocation> forward = allReachableLocations(icfg);

        // Backward set: all locations that can reach the targets (restricted to the
        // forward set)
        final Set<IcfgLocation> backward = backwardReachableWithin(forward, targets);

        // Intersection: locations on valid paths from entry to targets
        forward.retainAll(backward);
        return forward;
    }

    private Set<IcfgLocation> backwardReachableWithin(final Set<IcfgLocation> universe,
            final Collection<IcfgLocation> targets) {
        final Set<IcfgLocation> visited = new HashSet<>();
        final Deque<IcfgLocation> work = new ArrayDeque<>();
        for (final IcfgLocation t : targets) {
            if (t != null && universe.contains(t) && visited.add(t)) {
                work.add(t);
            }
        }
        while (!work.isEmpty()) {
            final IcfgLocation cur = work.removeFirst();
            for (final IcfgEdge e : cur.getIncomingEdges()) {
                final IcfgLocation src = e.getSource();
                // Filter: only traverse if source is in our relevant universe (forward
                // reachable)
                if (src != null && universe.contains(src) && visited.add(src)) {
                    work.add(src);
                }
            }
        }
        return visited;
    }
}
