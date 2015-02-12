package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot.BuchiProgramAcceptingStateAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;

public class MinimizeStatesSingleEdgeSingleNode extends BaseProductOptimizer {

	public MinimizeStatesSingleEdgeSingleNode(RootNode product, IUltimateServiceProvider services) {
		super(product, services);
		mLogger.info("Removed " + mRemovedEdges + " edges and " + mRemovedLocations
				+ " and replaced them with sequential compositions");
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
			}
			closed.add(current);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Processing edge " + current.hashCode());
				mLogger.debug("    " + current);
			}
			ProgramPoint target = (ProgramPoint) current.getTarget();

			if (target.getIncomingEdges().size() == 1 && target.getOutgoingEdges().size() == 1) {
				// its a candidate
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
		// this node has exactly one incoming and one outgoing edge,
		// so we have the two edges
		// e1 = (q1,st1,q2)
		// e2 = (q2,st2,q3)
		RCFGEdge predEdge = target.getIncomingEdges().get(0);
		RCFGEdge succEdge = target.getOutgoingEdges().get(0);

		if (!(predEdge instanceof CodeBlock) || !(succEdge instanceof CodeBlock)) {
			// if one of the edges is no codeblock, it is a root edge, and we
			// cannot apply the rule
			return target.getOutgoingEdges();
		}

		if (predEdge instanceof Call && succEdge instanceof Return) {
			// this is allowed, continue
		} else if (predEdge instanceof Return || predEdge instanceof Call || succEdge instanceof Return
				|| succEdge instanceof Call) {
			// we can only compose (Call,Return), no other combination of Call /
			// Return.
			return target.getOutgoingEdges();
		}

		ProgramPoint pred = (ProgramPoint) predEdge.getSource();
		ProgramPoint succ = (ProgramPoint) succEdge.getTarget();

		if (BuchiProgramAcceptingStateAnnotation.getAnnotation(pred) != null
				|| BuchiProgramAcceptingStateAnnotation.getAnnotation(target) == null
				|| BuchiProgramAcceptingStateAnnotation.getAnnotation(succ) != null) {
			// we will not change the acceptance condition, so we delete e1 and
			// e2 and q2
			// and add the new edge (q1,st1;st2,q3)
			
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("    will remove " + target.getLocationName());
			}
			
			predEdge.disconnectSource();
			predEdge.disconnectTarget();
			succEdge.disconnectSource();
			succEdge.disconnectTarget();
			mRemovedEdges += 2;

			new SequentialComposition(pred, succ, root.getRootAnnot().getBoogie2SMT(), root.getRootAnnot()
					.getModGlobVarManager(), true, true, mServices, new CodeBlock[] { (CodeBlock) predEdge,
					(CodeBlock) succEdge });
			
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("    removed 2, added 2 edges");
			}
			
			return pred.getOutgoingEdges();
		}
		return succ.getOutgoingEdges();

	}

	@Override
	public boolean IsGraphChanged() {
		return mRemovedEdges > 0 || mRemovedLocations > 0;
	}
}
