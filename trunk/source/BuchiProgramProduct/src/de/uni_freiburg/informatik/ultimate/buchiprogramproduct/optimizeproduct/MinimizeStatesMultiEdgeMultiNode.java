package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;

/**
 * Most aggressive minimization. Tries to remove states no matter what.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class MinimizeStatesMultiEdgeMultiNode extends BaseMinimizeStates {

	public MinimizeStatesMultiEdgeMultiNode(RootNode product, IUltimateServiceProvider services) {
		super(product, services);
	}

	@Override
	protected Collection<? extends RCFGEdge> processCandidate(RootNode root, ProgramPoint target) {
		// we have the incoming edges
		// ei = (qi,sti,q) in EI
		// and the outgoing edges
		// ej = (q,stj,qj) in EO
		// and we will try to replace them by |EI| * |EO| edges

		List<RCFGNode> incomingNodes = target.getIncomingNodes();
		List<RCFGNode> outgoingNodes = target.getOutgoingNodes();

		if (!incomingNodes.isEmpty() && !outgoingNodes.isEmpty() && !checkTargetNode(target)
				&& !checkAllNodes(incomingNodes, outgoingNodes)) {
			// the nodes do not fulfill the conditions, return
			return target.getOutgoingEdges();
		}

		if (!checkEdgePairs(target.getIncomingEdges(), target.getOutgoingEdges())) {
			// the edges do not fulfill the conditions, return
			return target.getOutgoingEdges();
		}

		// we will not change the acceptance conditions, so we can start
		// with creating new edges
		// for each ei from EI, for each ej from EO
		// we add a new edge (qi,sti;stj,qj)

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    will remove " + target.getLocationName());
		}

		List<RCFGEdge> predEdges = new ArrayList<RCFGEdge>(target.getIncomingEdges());
		List<RCFGEdge> succEdges = new ArrayList<RCFGEdge>(target.getOutgoingEdges());

		// collect information for new edges beforehand (because
		// SequentialComposition disconnects the edges and we wont get their
		// source/target information afterwards)
		ArrayList<EdgeConstructionInfo> infos = new ArrayList<>();
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
				infos.add(new EdgeConstructionInfo((ProgramPoint) predEdge.getSource(), (ProgramPoint) succEdge
						.getTarget(), predCB, succCB));
			}
		}

		for (RCFGEdge predEdge : predEdges) {
			predEdge.disconnectSource();
			predEdge.disconnectTarget();
		}

		for (RCFGEdge succEdge : succEdges) {
			succEdge.disconnectSource();
			succEdge.disconnectTarget();
		}

		ArrayList<RCFGEdge> rtr = new ArrayList<>();
		for (EdgeConstructionInfo info : infos) {
			SequentialComposition sc = new SequentialComposition(info.getSource(), info.getTarget(), root
					.getRootAnnot().getBoogie2SMT(), root.getRootAnnot().getModGlobVarManager(), false, false,
					mServices, new CodeBlock[] { info.getFirst(), info.getSecond() });
			assert sc.getTarget() != null;
			assert sc.getSource() != null;
			rtr.add(sc);
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("    removed " + (predEdges.size() + succEdges.size()) + ", added " + rtr.size() + " edges");
		}

		mRemovedEdges += predEdges.size() + succEdges.size();
		// we added new edges to all predecessors, we have to recheck them now
		return rtr;
	}

	private class EdgeConstructionInfo {
		ProgramPoint getSource() {
			return mSource;
		}

		ProgramPoint getTarget() {
			return mTarget;
		}

		CodeBlock getFirst() {
			return mFirst;
		}

		CodeBlock getSecond() {
			return mSecond;
		}

		public EdgeConstructionInfo(ProgramPoint source, ProgramPoint target, CodeBlock first, CodeBlock second) {
			this.mSource = source;
			this.mTarget = target;
			this.mFirst = first;
			this.mSecond = second;
		}

		ProgramPoint mSource;
		ProgramPoint mTarget;
		CodeBlock mFirst;
		CodeBlock mSecond;
	}

}
