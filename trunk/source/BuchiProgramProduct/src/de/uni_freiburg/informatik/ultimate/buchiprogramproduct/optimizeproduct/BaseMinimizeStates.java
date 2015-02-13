package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.Activator;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot.BuchiProgramAcceptingStateAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public abstract class BaseMinimizeStates extends BaseProductOptimizer {

	private boolean mIgnoreBlowup;

	public BaseMinimizeStates(RootNode product, IUltimateServiceProvider services) {
		super(product, services);
		mLogger.info("Removed " + mRemovedEdges + " edges and " + mRemovedLocations
				+ " locations and replaced them with sequential compositions");
	}

	@Override
	protected void init(RootNode root, IUltimateServiceProvider services) {
		super.init(root, services);
		mIgnoreBlowup = new UltimatePreferenceStore(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.OPTIMIZE_MINIMIZE_STATES_IGNORE_BLOWUP);
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
				// disconnected edges could remain in the queue if they were
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
			} else {
				edges.addAll(processCandidate(root, target));
			}
		}
		if (mRemovedEdges > 0) {
			removeDisconnectedLocations(root);
		}

		return root;
	}

	protected abstract Collection<? extends RCFGEdge> processCandidate(RootNode root, ProgramPoint target);

	protected boolean checkEdgePairs(List<RCFGEdge> predEdges, List<RCFGEdge> succEdges) {
		if (!mIgnoreBlowup) {
			if (predEdges.size() + succEdges.size() < predEdges.size() * succEdges.size()) {
				// we would introduce more edges than we remove, we do not want
				// that
				return false;
			}
		}

		for (RCFGEdge predEdge : predEdges) {
			for (RCFGEdge succEdge : succEdges) {
				if (!checkEdgePair(predEdge, succEdge)) {
					return false;
				}
			}
		}
		return true;
	}

	protected boolean checkEdgePair(RCFGEdge predEdge, RCFGEdge succEdge) {
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
		return true;
	}

	protected boolean checkAllNodes(List<RCFGNode> predNodes, List<RCFGNode> succNodes) {
		for (RCFGNode predNode : predNodes) {
			if(BuchiProgramAcceptingStateAnnotation.getAnnotation(predNode) == null){
				return false;
			}
		}
		
		for (RCFGNode succNode : succNodes) {
			if(BuchiProgramAcceptingStateAnnotation.getAnnotation(succNode) == null){
				return false;
			}
		}
		return true;
	}

	protected boolean checkTargetNode(RCFGNode target) {
		return BuchiProgramAcceptingStateAnnotation.getAnnotation(target) == null;
	}

	protected boolean checkNodePair(RCFGNode pred, RCFGNode succ) {
		return BuchiProgramAcceptingStateAnnotation.getAnnotation(pred) != null
				|| BuchiProgramAcceptingStateAnnotation.getAnnotation(succ) != null;
	}

	@Override
	public boolean IsGraphChanged() {
		return mRemovedEdges > 0 || mRemovedLocations > 0;
	}

}