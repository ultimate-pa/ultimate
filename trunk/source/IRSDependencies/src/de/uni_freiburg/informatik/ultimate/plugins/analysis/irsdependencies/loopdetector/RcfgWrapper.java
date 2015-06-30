package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * Simple wrapper for RCFGs to the {@link IGraph} interface used by
 * {@link AStar}.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class RcfgWrapper implements IGraph<RCFGNode, RCFGEdge> {

	@Override
	public RCFGNode getTarget(RCFGEdge edge) {
		return edge.getTarget();
	}

	@Override
	public RCFGNode getSource(RCFGEdge edge) {
		return edge.getSource();
	}

	@Override
	public Collection<RCFGEdge> getOutgoingEdges(RCFGNode vertice) {
		return vertice.getOutgoingEdges();
	}
}