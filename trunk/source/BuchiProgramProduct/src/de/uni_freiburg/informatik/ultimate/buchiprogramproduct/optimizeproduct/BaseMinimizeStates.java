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
				+ " locations by large block encoding");
	}

	@Override
	protected void init(RootNode root, IUltimateServiceProvider services) {
		super.init(root, services);
		mIgnoreBlowup = new UltimatePreferenceStore(Activator.PLUGIN_ID)
				.getBoolean(PreferenceInitializer.OPTIMIZE_MINIMIZE_STATES_IGNORE_BLOWUP);
	}

	@Override
	protected RootNode process(RootNode root) {
		ArrayDeque<RCFGNode> nodes = new ArrayDeque<>();
		HashSet<RCFGNode> closed = new HashSet<>();

		nodes.addAll(root.getOutgoingNodes());

		while (!nodes.isEmpty()) {
			RCFGNode current = nodes.removeFirst();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Processing node " + current + " [" + current.hashCode() + "]");
			}
			if (current.getIncomingEdges().size() == 1 && current.getIncomingEdges().get(0) instanceof RootEdge) {
				nodes.addAll(current.getOutgoingNodes());
			} else {
				Collection<? extends RCFGEdge> edges = processCandidate(root, (ProgramPoint) current);
				for (RCFGEdge edge : edges) {
					if (!closed.contains(edge.getTarget())) {
						nodes.add(edge.getTarget());
					}
				}
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
			if (BuchiProgramAcceptingStateAnnotation.getAnnotation(predNode) == null) {
				return false;
			}
		}

		for (RCFGNode succNode : succNodes) {
			if (BuchiProgramAcceptingStateAnnotation.getAnnotation(succNode) == null) {
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
		return mRemovedLocations > 0;
	}

}