package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot.BuchiProgramAcceptingStateAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;

public class MinimizeStatesMultiEdgeSingleNode extends BaseProductOptimizer {

	public MinimizeStatesMultiEdgeSingleNode(RootNode product, IUltimateServiceProvider services) {
		super(product, services);
		mLogger.info("Removed " + mRemovedEdges + " edges and " + mRemovedLocations
				+ " locations and replaced them with sequential compositions");
	}

	@Override
	protected RootNode process(RootNode root) {
		ArrayDeque<RCFGEdge> edges = new ArrayDeque<>();
		HashSet<RCFGEdge> closed = new HashSet<>();

		edges.addAll(root.getOutgoingEdges());

		while (!edges.isEmpty()) {
			RCFGEdge current = edges.removeFirst();
			if (closed.contains(current)) {
				continue;
			} else if (current.getTarget() == null || current.getSource() == null) {
				// disconnected edges can remain in the queue if they were
				// inserted previously
				continue;
			}
			closed.add(current);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Processing edge " + current.hashCode());
				mLogger.debug("    " + current);
			}
			ProgramPoint target = (ProgramPoint) current.getTarget();
			if (current instanceof RootEdge) {
				edges.addAll(current.getTarget().getOutgoingEdges());
			} else if (new HashSet<>(target.getIncomingNodes()).size() == 1
					&& new HashSet<>(target.getOutgoingNodes()).size() == 1) {
				// // its a candidate
				edges.addAll(processCandidate(root, target));
			} else {
				edges.addAll(current.getTarget().getOutgoingEdges());
			}
		}

		removeDisconnectedLocations(root);

		return root;
	}

	/**
	 * 
	 * @param target
	 * @return A list of edges that should be processed next
	 */
	private List<RCFGEdge> processCandidate(RootNode root, ProgramPoint target) {
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

		if (!checkEdges(target.getIncomingEdges(), target.getOutgoingEdges())) {
			// the edges do not fulfill the conditions, return
			return succ.getOutgoingEdges();
		}

		if (BuchiProgramAcceptingStateAnnotation.getAnnotation(pred) != null
				|| BuchiProgramAcceptingStateAnnotation.getAnnotation(target) == null
				|| BuchiProgramAcceptingStateAnnotation.getAnnotation(succ) != null) {
			// we will not change the acceptance conditions, so we can start
			// with creating new edges
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
					if(mLogger.isDebugEnabled()){
						mLogger.debug("Already infeasible: "+predCB);	
					}
					continue;
				}
				for (RCFGEdge succEdge : succEdges) {
					CodeBlock succCB = (CodeBlock) succEdge;

					if (succCB.getTransitionFormula().isInfeasible() == Infeasibility.INFEASIBLE) {
						if(mLogger.isDebugEnabled()){
							mLogger.debug("Already infeasible: "+succCB);	
						}
						continue;
					}

					SequentialComposition sc = new SequentialComposition(pred, succ, root.getRootAnnot()
							.getBoogie2SMT(), root.getRootAnnot().getModGlobVarManager(), false, false, mServices,
							new CodeBlock[] { predCB, succCB });
					assert sc.getTarget() != null;
					assert sc.getSource() != null;
					newEdges++;
				}
			}

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("    removed " + (predEdges.size() + succEdges.size()) + ", added " + newEdges + " edges");
			}

			mRemovedEdges += predEdges.size() + succEdges.size();
			return pred.getOutgoingEdges();

		}
		return succ.getOutgoingEdges();

	}

	private boolean checkEdges(List<RCFGEdge> predEdges, List<RCFGEdge> succEdges) {
		for (RCFGEdge predEdge : predEdges) {
			for (RCFGEdge succEdge : succEdges) {
				if (!(predEdge instanceof CodeBlock) || !(succEdge instanceof CodeBlock)) {
					// if one of the edges is no codeblock, it is a root edge,
					// and we cannot apply the rule
					return false;
				}

				if (predEdge instanceof Call && succEdge instanceof Return) {
					// this is allowed, continue
				} else if (predEdge instanceof Return || predEdge instanceof Call || succEdge instanceof Return
						|| succEdge instanceof Call) {
					// we can only compose (Call,Return), no other combination
					// of Call /
					// Return.
					return false;
				}
			}
		}
		return true;
	}

	@Override
	public boolean IsGraphChanged() {
		return mRemovedEdges > 0 || mRemovedLocations > 0;
	}
}
