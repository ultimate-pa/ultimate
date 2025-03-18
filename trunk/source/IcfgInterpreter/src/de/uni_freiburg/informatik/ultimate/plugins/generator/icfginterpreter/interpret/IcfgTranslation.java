package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.ICFGExecutionEdge;

public class IcfgTranslation {
	/**
	 * Translates the edges of the ICFG using breadth first search.
	 *
	 * @param icfg
	 * @param services
	 * @return A map that stores the translated edges by their source vertex.
	 */
	public static HashMap<IcfgLocation, ArrayList<ICFGExecutionEdge>> edgeBFS(final IIcfg<? extends IcfgLocation> icfg,
			final IUltimateServiceProvider services) {
		final Set<? extends IcfgLocation> initialNodes = icfg.getInitialNodes();
		final ManagedScript script = icfg.getCfgSmtToolkit().getManagedScript();

		final HashSet<IcfgLocation> visited = new HashSet<>();
		final ArrayList<IcfgLocation> next = new ArrayList<>(initialNodes);

		final HashMap<IcfgLocation, ArrayList<ICFGExecutionEdge>> sourceToEdges = new HashMap<>();

		while (next.size() > 0) {
			final IcfgLocation source = next.remove(0);

			if (visited.contains(source)) {
				continue;
			}
			visited.add(source);

			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				next.add(target);

				final ArrayList<ICFGExecutionEdge> execEdges = ICFGExecutionEdge.createEdges(edge.getTransformula(),
						source, target, script, services);

				final ArrayList<ICFGExecutionEdge> sourceEdgeList = sourceToEdges.getOrDefault(source,
						new ArrayList<>());

				for (final ICFGExecutionEdge execEdge : execEdges) {
					sourceEdgeList.add(execEdge);
					sourceToEdges.put(source, sourceEdgeList);
				}
			}
		}

		return sourceToEdges;
	}
}
