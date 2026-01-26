package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;

/**
 * A delegating wrapper around an {@link IIcfg} that restricts {@link #getInitialNodes()} to a single thread's entry
 * point. All other methods delegate directly to the wrapped ICFG.
 *
 * This allows using the standard {@link de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter} and
 * {@link de.uni_freiburg.informatik.ultimate.lib.sifa.CallGraph} for analyzing a single thread in isolation.
 */
public class SingleThreadIcfg implements IIcfg<IcfgLocation> {

	private static final long serialVersionUID = 1L;

	private final IIcfg<IcfgLocation> mDelegate;
	private final Set<IcfgLocation> mFilteredInitialNodes;

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
	}

	@Override
	public Set<IcfgLocation> getInitialNodes() {
		return mFilteredInitialNodes;
	}

	@Override
	public Map<String, Map<DebugIdentifier, IcfgLocation>> getProgramPoints() {
		return mDelegate.getProgramPoints();
	}

	@Override
	public Map<String, IcfgLocation> getProcedureEntryNodes() {
		return mDelegate.getProcedureEntryNodes();
	}

	@Override
	public Map<String, IcfgLocation> getProcedureExitNodes() {
		return mDelegate.getProcedureExitNodes();
	}

	@Override
	public Map<String, Set<IcfgLocation>> getProcedureErrorNodes() {
		return mDelegate.getProcedureErrorNodes();
	}

	@Override
	public Set<IcfgLocation> getLocationsOfInterest() {
		return mDelegate.getLocationsOfInterest();
	}

	@Override
	public Set<IcfgLocation> getLoopLocations() {
		return mDelegate.getLoopLocations();
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
		return mDelegate.getVisualizationGraph();
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
