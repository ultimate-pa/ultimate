package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;

/**
 * Moderately aggressive minimization. Tries to remove states that have exactly
 * one predecessor and one successor state (put possibly more edges).
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class MinimizeStatesMultiEdgeSingleNode extends BaseMinimizeStates {

	public MinimizeStatesMultiEdgeSingleNode(RootNode product, IUltimateServiceProvider services) {
		super(product, services);
	}

	@Override
	protected List<RCFGEdge> processCandidate(RootNode root, ProgramPoint target) {

		if (new HashSet<>(target.getIncomingNodes()).size() != 1
				|| new HashSet<>(target.getOutgoingNodes()).size() != 1) {
			return target.getOutgoingEdges();
		}

		// this node has exactly one predecessor and one successor, but may have
		// more edges
		// so we have the incoming edges
		// ei = (q1,sti,q2) in Ei
		// and the outoging edges
		// eo = (q2,sto,q3) in Eo
		// and we will try to replace them by |Ei| * |Eo| edges

		// a precondition is that there is only one predecessor and one
		// successor, so this is enough to get it
		ProgramPoint pred = (ProgramPoint) target.getIncomingEdges().get(0).getSource();
		ProgramPoint succ = (ProgramPoint) target.getOutgoingEdges().get(0).getTarget();

		if (!checkTargetNode(target) && !checkNodePair(pred, succ)) {
			// the nodes do not fulfill the conditions, return
			return target.getOutgoingEdges();
		}

		if (!checkEdgePairs(target.getIncomingEdges(), target.getOutgoingEdges())) {
			// the edges do not fulfill the conditions, return
			return target.getOutgoingEdges();
		}

		// all conditions are met so we can start with creating new edges
		// for each ei from Ei and for each eo from Eo we add a new edge
		// (q1,st1;st2,q3)

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    will remove " + target.getLocationName());
		}

		List<RCFGEdge> predEdges = new ArrayList<RCFGEdge>(target.getIncomingEdges());
		List<RCFGEdge> succEdges = new ArrayList<RCFGEdge>(target.getOutgoingEdges());

		for (RCFGEdge predEdge : predEdges) {
			predEdge.disconnectSource();
			predEdge.disconnectTarget();
		}

		for (RCFGEdge succEdge : succEdges) {
			succEdge.disconnectSource();
			succEdge.disconnectTarget();
		}

		int newEdges = 0;
		for (RCFGEdge predEdge : predEdges) {
			CodeBlock predCB = (CodeBlock) predEdge;
			if (predCB.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("    already infeasible: " + predCB);
				}
				continue;
			}
			for (RCFGEdge succEdge : succEdges) {
				CodeBlock succCB = (CodeBlock) succEdge;

				if (succCB.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("    already infeasible: " + succCB);
					}
					continue;
				}

				SequentialComposition sc = new SequentialComposition(pred, succ, root.getRootAnnot().getBoogie2SMT(),
						root.getRootAnnot().getModGlobVarManager(), false, false, mServices, new CodeBlock[] { predCB,
								succCB });
				assert sc.getTarget() != null;
				assert sc.getSource() != null;
				newEdges++;
			}
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    removed " + (predEdges.size() + succEdges.size()) + ", added " + newEdges + " edges");
		}

		mRemovedEdges += predEdges.size() + succEdges.size();
		// we added new edges to pred, we have to recheck them now
		return pred.getOutgoingEdges();
	}

}
