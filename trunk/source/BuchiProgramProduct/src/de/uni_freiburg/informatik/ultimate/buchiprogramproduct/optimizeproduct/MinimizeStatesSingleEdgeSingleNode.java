package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;

/**
 * Least aggressive minimization (besides no attempt). Tries to remove states
 * that have only one incoming and one outgoing edge.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class MinimizeStatesSingleEdgeSingleNode extends BaseMinimizeStates {

	public MinimizeStatesSingleEdgeSingleNode(RootNode product, IUltimateServiceProvider services) {
		super(product, services);
	}

	@Override
	protected List<RCFGEdge> processCandidate(RootNode root, ProgramPoint target) {

		if (target.getIncomingEdges().size() != 1 || target.getOutgoingEdges().size() != 1) {
			return target.getOutgoingEdges();
		}

		// this node has exactly one incoming and one outgoing edge,
		// so we have the two edges
		// e1 = (q1,st1,q2)
		// e2 = (q2,st2,q3)
		RCFGEdge predEdge = target.getIncomingEdges().get(0);
		RCFGEdge succEdge = target.getOutgoingEdges().get(0);

		ProgramPoint pred = (ProgramPoint) predEdge.getSource();
		ProgramPoint succ = (ProgramPoint) succEdge.getTarget();

		if (!checkTargetNode(target) && !checkNodePair(pred, succ)) {
			// the nodes do not fulfill the conditions, return
			return target.getOutgoingEdges();
		}

		if (!checkEdgePair(predEdge, succEdge)) {
			// the edges do not fulfill the conditions, return
			return target.getOutgoingEdges();
		}

		// all conditions are met so we can start with creating new edges
		// we delete e1 and e2 and q2 and add the new edge (q1,st1;st2,q3)

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    will remove " + target.getLocationName());
		}

		predEdge.disconnectSource();
		predEdge.disconnectTarget();
		succEdge.disconnectSource();
		succEdge.disconnectTarget();
		mRemovedEdges += 2;

		new SequentialComposition(pred, succ, root.getRootAnnot().getBoogie2SMT(), root.getRootAnnot()
				.getModGlobVarManager(), false, false, mServices, new CodeBlock[] { (CodeBlock) predEdge,
				(CodeBlock) succEdge });

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    removed 2, added 2 edges");
		}
		// we added new edges to pred, we have to recheck them now
		return pred.getOutgoingEdges();

	}
}
