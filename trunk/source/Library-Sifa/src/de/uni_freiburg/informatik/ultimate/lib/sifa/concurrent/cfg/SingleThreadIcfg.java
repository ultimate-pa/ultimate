package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;

/**
 * A delegating wrapper around an {@link IIcfg} that restricts {@link #getInitialNodes()} to a single thread's entry
 * point. Additionally, maps/sets keyed by procedure are filtered to the procedures reachable from that entry point.
 *
 * This allows using the standard {@link de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter} and
 * {@link de.uni_freiburg.informatik.ultimate.lib.sifa.CallGraph} for analyzing a single thread in isolation.
 */
public class SingleThreadIcfg implements IIcfg<IcfgLocation> {

	private static final long serialVersionUID = 1L;

	private final IIcfg<IcfgLocation> mDelegate;
	private final Set<IcfgLocation> mFilteredInitialNodes;
	private final Set<IcfgLocation> mReachableLocations;
	private final Set<String> mReachableProcedures;
	private final Map<String, Map<DebugIdentifier, IcfgLocation>> mFilteredProgramPoints;
	private final Map<String, IcfgLocation> mFilteredProcedureEntryNodes;
	private final Map<String, IcfgLocation> mFilteredProcedureExitNodes;
	private final Map<String, Set<IcfgLocation>> mFilteredProcedureErrorNodes;
	private final Set<IcfgLocation> mFilteredLocationsOfInterest;
	private final Set<IcfgLocation> mFilteredLoopLocations;

	/**
	 * Creates a wrapper that restricts initial nodes to the entry point of the specified thread.
	 *
	 * @param delegate             the underlying ICFG
	 * @param threadEntryProcedure the procedure name of the thread's entry point
	 */
	public SingleThreadIcfg(final IIcfg<IcfgLocation> delegate, final String threadEntryProcedure) {
		mDelegate = delegate;
		final IcfgLocation entryNode = delegate.getProcedureEntryNodes().get(threadEntryProcedure);
		if (entryNode == null) {
			throw new IllegalArgumentException("No entry node found for procedure: " + threadEntryProcedure);
		}
		mFilteredInitialNodes = Set.of(entryNode);

		mReachableLocations = Set.copyOf(IcfgLocationIterator.asStream(this).collect(Collectors.toSet()));
		mReachableProcedures = Set
				.copyOf(mReachableLocations.stream().map(IcfgLocation::getProcedure).collect(Collectors.toSet()));

		mFilteredProgramPoints = filterProgramPoints(delegate.getProgramPoints());
		mFilteredProcedureEntryNodes = filterLocationMap(delegate.getProcedureEntryNodes());
		mFilteredProcedureExitNodes = filterLocationMap(delegate.getProcedureExitNodes());
		mFilteredProcedureErrorNodes = filterLocationSetMap(delegate.getProcedureErrorNodes());
		mFilteredLocationsOfInterest = filterLocationSet(delegate.getLocationsOfInterest());
		mFilteredLoopLocations = filterLocationSet(delegate.getLoopLocations());
	}

	@Override
	public Set<IcfgLocation> getInitialNodes() {
		return mFilteredInitialNodes;
	}

	private Map<String, Map<DebugIdentifier, IcfgLocation>> filterProgramPoints(
			final Map<String, Map<DebugIdentifier, IcfgLocation>> programPoints) {
		final Map<String, Map<DebugIdentifier, IcfgLocation>> filtered = new HashMap<>();
		for (final var entry : programPoints.entrySet()) {
			final String procedure = entry.getKey();
			if (!mReachableProcedures.contains(procedure)) {
				continue;
			}
			final Map<DebugIdentifier, IcfgLocation> inner = new HashMap<>();
			for (final var innerEntry : entry.getValue().entrySet()) {
				final IcfgLocation loc = innerEntry.getValue();
				if (loc != null && mReachableLocations.contains(loc)) {
					inner.put(innerEntry.getKey(), loc);
				}
			}
			filtered.put(procedure, Map.copyOf(inner));
		}
		return Map.copyOf(filtered);
	}

	private Map<String, IcfgLocation> filterLocationMap(final Map<String, IcfgLocation> map) {
		final Map<String, IcfgLocation> filtered = new HashMap<>();
		for (final var entry : map.entrySet()) {
			final String procedure = entry.getKey();
			final IcfgLocation loc = entry.getValue();
			if (!mReachableProcedures.contains(procedure)) {
				continue;
			}
			if (loc != null && mReachableLocations.contains(loc)) {
				filtered.put(procedure, loc);
			}
		}
		return Map.copyOf(filtered);
	}

	private Map<String, Set<IcfgLocation>> filterLocationSetMap(final Map<String, Set<IcfgLocation>> map) {
		final Map<String, Set<IcfgLocation>> filtered = new HashMap<>();
		for (final var entry : map.entrySet()) {
			final String procedure = entry.getKey();
			if (!mReachableProcedures.contains(procedure)) {
				continue;
			}
			final Set<IcfgLocation> locs = new HashSet<>();
			for (final IcfgLocation loc : entry.getValue()) {
				if (loc != null && mReachableLocations.contains(loc)) {
					locs.add(loc);
				}
			}
			filtered.put(procedure, Set.copyOf(locs));
		}
		return Map.copyOf(filtered);
	}

	private Set<IcfgLocation> filterLocationSet(final Set<IcfgLocation> locs) {
		return locs.stream().filter(mReachableLocations::contains).collect(Collectors.toUnmodifiableSet());
	}

	@Override
	public Map<String, Map<DebugIdentifier, IcfgLocation>> getProgramPoints() {
		return mFilteredProgramPoints;
	}

	@Override
	public Map<String, IcfgLocation> getProcedureEntryNodes() {
		return mFilteredProcedureEntryNodes;
	}

	@Override
	public Map<String, IcfgLocation> getProcedureExitNodes() {
		return mFilteredProcedureExitNodes;
	}

	@Override
	public Map<String, Set<IcfgLocation>> getProcedureErrorNodes() {
		return mFilteredProcedureErrorNodes;
	}

	@Override
	public Set<IcfgLocation> getLocationsOfInterest() {
		return mFilteredLocationsOfInterest;
	}

	@Override
	public Set<IcfgLocation> getLoopLocations() {
		return mFilteredLoopLocations;
	}

	@Override
	public CfgSmtToolkit getCfgSmtToolkit() {
		return mDelegate.getCfgSmtToolkit();
	}

	@Override
	public String getIdentifier() {
		return mDelegate.getIdentifier();
	}

	@Override
	public Class<IcfgLocation> getLocationClass() {
		return mDelegate.getLocationClass();
	}

	@Override
	public VisualizationNode getVisualizationGraph() {
		throw new UnsupportedOperationException("getVisualizationGraph() not implemented for singleThreadIcfg");
	}

	@Override
	public IPayload getPayload() {
		return mDelegate.getPayload();
	}

	@Override
	public boolean hasPayload() {
		return mDelegate.hasPayload();
	}
}
