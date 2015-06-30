package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * Simple zero heuristic for {@link AStar}.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class ZeroHeuristic implements IHeuristic<RCFGNode, RCFGEdge> {
	@Override
	public int getHeuristicValue(RCFGNode from, RCFGEdge over, RCFGNode to) {
		return 0;
	}

	@Override
	public int getConcreteCost(RCFGEdge e) {
		return 1;
	}
}