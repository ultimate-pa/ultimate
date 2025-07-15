package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.dfg;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class Test {
	public static void test(final IIcfg<?> icfg, final ILogger logger) {
		for (final IcfgLocation initialNode : icfg.getInitialNodes()) {
			logger.info("Building Dfg for InitialNode: " + initialNode);
			final DfgContainer dfg = DfgBuilder.buildDfg(initialNode, logger);
			logger.info("Obtained Dfg");
			logger.debug("EdgeRelation: " + dfg.getEdgeRelation().toString());
			logger.debug("Length of Nodelist: " + dfg.getNodeList().size());
			final Set<IcfgEdge> fvsBrute = CycleRemover.computeFeedbackVertexBruteForce(dfg, logger);
			final Set<IcfgEdge> fvsHeuristic = CycleRemover.computeFeedbackVertexHeuristic(dfg, logger);
			logger.info("Obtained FVS");
			logger.debug("Comparing FVS BruteForce and Heuristic: Bruteforce Length=" + fvsBrute.size()
					+ " and Heuristic Length=" + fvsHeuristic.size());
			logger.debug("FVS BruteForce and Heuristic the same? " + fvsBrute.equals(fvsHeuristic));
			logger.debug("Ball Edges: " + CycleRemover.getBallEdges(dfg, logger));
			logger.debug("Non Ball Edges: " + CycleRemover.getOutsideBallEdges(dfg, logger));
			logger.debug("UseToUse Dfg: " + DfgBuilder.buildDfgUseToUse(initialNode, logger));
		}
	}

}
