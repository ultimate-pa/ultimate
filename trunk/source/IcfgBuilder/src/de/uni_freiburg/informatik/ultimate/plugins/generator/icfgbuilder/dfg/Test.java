package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.dfg;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

public class Test {
	public static void test(final BoogieIcfgContainer icfg, final ILogger logger) {
		for (final BoogieIcfgLocation initialNode : icfg.getInitialNodes()) {
			logger.info("Building Dfg for InitialNode: " + initialNode);
			final DfgContainer dfg = DfgBuilder.buildDfg(initialNode, logger);
			logger.info("Obtained Dfg");
			logger.debug("EdgeRelation: " + dfg.getEdgeRelation().toString());
			logger.debug("Length of Nodelist: " + dfg.getNodeList().size());
			CycleRemover.computeFeedbackVertexSet(dfg, logger);
		}
	}

}
