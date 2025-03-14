package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

public class IcfgInterpreterObserver extends BaseObserver {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private IIcfg<? extends IcfgLocation> mIcfg;

	public IcfgInterpreterObserver(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (root instanceof final IIcfg<?> icfg) {
			if (mIcfg != null) {
				throw new UnsupportedOperationException("Multiple CFGs are not supported.");
			}
			mIcfg = icfg;
		}
		return false;
	}

	@Override
	public void finish() {
		// TODO: Extract executions from mIcfg (mServices will be also needed for some operations)
		// This should be probably moved to a separate class

		// Useful methods:
		// * mIcfg.getCfgSmtToolkit().getManagedScript()
		// (also .getScript() if the Script instead of the ManagedScript is needed)
		// * mIcfg.getInitialNodes()
		// * TransFormulaUtils.computeGuard
		// * SmtUtils.getConjuncts
		// * mLogger can be used for output (e.g., for debugging)
		final Set<? extends IcfgLocation> initialNodes = mIcfg.getInitialNodes();
		final ManagedScript script = mIcfg.getCfgSmtToolkit().getManagedScript();

		final HashSet<IcfgLocation> visited = new HashSet<>();
		final ArrayList<IcfgLocation> next = new ArrayList<>(initialNodes);

		final HashMap<IcfgLocation, ArrayList<ICFGExecutionEdge>> sourceEdges = new HashMap<>();

		while (next.size() > 0) {
			final IcfgLocation source = next.remove(0);

			if (visited.contains(source)) {
				continue;
			}
			visited.add(source);

			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				next.add(target);

				final ICFGExecutionEdge execEdge = new ICFGExecutionEdge(edge.getTransformula(), source, target, script,
						mServices);

				final ArrayList<ICFGExecutionEdge> sourceEdgeList = sourceEdges.getOrDefault(source, new ArrayList<>());
				sourceEdgeList.add(execEdge);
				sourceEdges.put(source, sourceEdgeList);
			}
		}
	}

	public IElement getRootOfNewModel() {
		// TODO: We want to return executions instead (for now we can also just log them, but e.g., to give the
		// execution to other plugins)
		return mIcfg;
	}
}
