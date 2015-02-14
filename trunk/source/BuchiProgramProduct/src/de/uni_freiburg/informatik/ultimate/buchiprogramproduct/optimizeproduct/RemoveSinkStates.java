package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class RemoveSinkStates extends BaseProductOptimizer {

	public RemoveSinkStates(RootNode product, IUltimateServiceProvider services) {
		super(product, services);
		mLogger.info("Removed " + mRemovedEdges + " edges and " + mRemovedLocations
				+ " locations by removing sink states");
	}

	@Override
	protected void init(RootNode root, IUltimateServiceProvider services) {
	}

	@Override
	protected RootNode process(RootNode root) {
		List<RCFGNode> sinks = collectSinks(root);
		if (mLogger.isDebugEnabled()) {
			mLogger.info("Collected " + sinks.size() + " initial sink states");
		}
		removeSinks(sinks);
		removeDisconnectedLocations(root);
		return root;
	}

	private List<RCFGNode> collectSinks(RootNode root) {
		ArrayList<RCFGNode> rtr = new ArrayList<>();
		ArrayDeque<RCFGNode> nodes = new ArrayDeque<>();
		HashSet<RCFGNode> closed = new HashSet<>();
		nodes.addAll(root.getOutgoingNodes());
		while (!nodes.isEmpty()) {
			RCFGNode current = nodes.removeFirst();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			if (current.getOutgoingEdges().size() == 0) {
				rtr.add(current);
			} else {
				nodes.addAll(current.getOutgoingNodes());
			}

		}
		return rtr;
	}

	private void removeSinks(List<RCFGNode> sinks) {
		ArrayDeque<RCFGNode> nodes = new ArrayDeque<>();
		nodes.addAll(sinks);
		while (!nodes.isEmpty()) {
			RCFGNode current = nodes.removeFirst();

			if (current.getOutgoingEdges().size() == 0) {
				ArrayList<RCFGEdge> incoming = new ArrayList<>(current.getIncomingEdges());
				for (RCFGEdge edge : incoming) {
					nodes.add(edge.getSource());
					edge.disconnectSource();
					edge.disconnectTarget();
					mRemovedEdges++;
				}
			}
		}
	}

	@Override
	public boolean IsGraphChanged() {
		return mRemovedEdges > 0 || mRemovedLocations > 0;
	}
}
