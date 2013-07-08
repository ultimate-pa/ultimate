/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.algorithm;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.ConjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.ShortcutErrEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * This class is responsible for minimizing nodes with one incoming and more
 * than one outgoing edges. They are remain, while minimizing loops and goto's.
 * 
 * @author Stefan Wissert
 * 
 */
public class MinimizeLoopVisitor extends MinimizeBranchVisitor {


	/**
	 * @param logger
	 */
	public MinimizeLoopVisitor(Logger logger) {
		super(logger);
	}

	@Override
	protected MinimizedNode[] applyMinimizationRules(MinimizedNode node) {
		// if this node is not reachable anymore (since we cut it off, by
		// merging sequentially) we do not apply our minimization rules
		// ---> the node is not part of the graph anymore
		if (notReachableNodes.contains(node)) {
			return new MinimizedNode[0];
		}
		ArrayList<MinimizedNode> reVisitNodes = new ArrayList<MinimizedNode>();
		if (checkForSequentialMerge(node)) {
			reVisitNodes.addAll(recursiveLoopMerge(node));
		} else {
			reVisitNodes.addAll(Arrays.asList(super
					.applyMinimizationRules(node)));
		}
		return reVisitNodes.toArray(new MinimizedNode[0]);
	}

	/**
	 * @param node
	 * @return
	 */
	private List<MinimizedNode> recursiveLoopMerge(MinimizedNode node) {
		if (checkForSequentialMerge(node)) {
			IMinimizedEdge incoming = (IMinimizedEdge) node.getIncomingEdges()
					.get(0);
			ArrayList<MinimizedNode> reVisitNodes = new ArrayList<MinimizedNode>();
			for (IMinimizedEdge outgoing : node.getMinimalOutgoingEdgeLevel()) {
				// We check first, if it is possible to merge deep nodes first!
				recursiveLoopMerge(outgoing.getTarget());
			}
			// Now maybe we are now able do some merging
			for (IMinimizedEdge outgoing : node.getMinimalOutgoingEdgeLevel()) {
				reVisitNodes.addAll(Arrays.asList(super
						.applyMinimizationRules(outgoing.getTarget())));
			}
			s_Logger.debug("Sequential Composition of one incoming with multiple outgoing edges for: "
					+ node);
			ArrayList<MinimizedNode> checkForParallelMerge = new ArrayList<MinimizedNode>();

			if (checkForSequentialMerge(node)) {
				s_Logger.debug("Merging Sequential Node : " + node);
				checkForParallelMerge.addAll(mergeSequential(incoming,
						node.getMinimalOutgoingEdgeLevel()));
				reVisitNodes.addAll(checkForParallelMerge);
				for (MinimizedNode target : checkForParallelMerge) {
					reVisitNodes.addAll(Arrays.asList(super
							.applyMinimizationRules(target)));
				}
			}
			return reVisitNodes;
		} else {
			return new ArrayList<MinimizedNode>();
		}
	}

	/**
	 * @param incoming
	 * @param outgoing
	 * @return
	 */
	private List<MinimizedNode> mergeSequential(IMinimizedEdge incoming,
			List<IMinimizedEdge> outgoing) {
		// We have to compute the new outgoing edge level list
		ArrayList<IMinimizedEdge> outgoingList = new ArrayList<IMinimizedEdge>();
		ArrayList<MinimizedNode> reVisitNodes = new ArrayList<MinimizedNode>();
		for (IMinimizedEdge outgoingEdge : outgoing) {
			ConjunctionEdge conjunction;
			if (incoming instanceof ShortcutErrEdge
					|| outgoingEdge instanceof ShortcutErrEdge) {
				conjunction = new ShortcutErrEdge(incoming, outgoingEdge);
			} else {
				conjunction = new ConjunctionEdge(incoming, outgoingEdge);
			}
			outgoingList.add(conjunction);
			// We have to compute a new incoming list, for the target node of
			// this conjunction
			ArrayList<IMinimizedEdge> incomingList = new ArrayList<IMinimizedEdge>();
			incomingList.add(conjunction);
			for (IMinimizedEdge edge : conjunction.getTarget()
					.getMinimalIncomingEdgeLevel()) {
				// All edges except of the outgoingEdge, stay in the List!
				if (edge != outgoingEdge) {
					incomingList.add(edge);
				}
			}
			conjunction.getTarget().addNewIncomingEdgeLevel(incomingList);
			reVisitNodes.add(conjunction.getTarget());
		}
		// Now we have to compute the new outgoing list
		for (IMinimizedEdge edge : incoming.getSource()
				.getMinimalOutgoingEdgeLevel()) {
			// Except of the actual incoming-Edge, the rest stays in the list
			if (edge != incoming) {
				outgoingList.add(edge);
			}
		}
		incoming.getSource().addNewOutgoingEdgeLevel(outgoingList, null);
		visitedEdges.add(incoming);
		visitedEdges.addAll(outgoing);
		notReachableNodes.add(incoming.getTarget());
		return reVisitNodes;

	}

	/**
	 * @param node
	 * @return
	 */
	private boolean checkForSequentialMerge(MinimizedNode node) {
		// In this run there can be nodes with one incoming and two outgoing
		// edges, which we also want to merge
		if (node.getIncomingEdges().size() == 1
				&& node.getOutgoingEdges().size() >= 2) {
			// Maybe we have an incoming RootEdge, then we want not to minimize
			for (RCFGEdge edge : node.getOriginalNode().getIncomingEdges()) {
				if (edge instanceof RootEdge) {
					return false;
				}
			}
			HashSet<MinimizedNode> targetNodes = new HashSet<MinimizedNode>();
			for (IMinimizedEdge edge : node.getMinimalOutgoingEdgeLevel()) {
				// We do not include self-loops
				if (edge.getTarget() == node) {
					s_Logger.info("Found a self-loop, should not happen");
					return false;
				}
				if (targetNodes.contains(edge.getTarget())) {
					s_Logger.info("Found Parallel Nodes, should not happen");
					return false;
				}
				targetNodes.add(edge.getTarget());
			}

			// Second condition: edges are of type CodeBlock
			// In order to do this for many edges we use a list here
			ArrayList<IMinimizedEdge> listToCheck = new ArrayList<IMinimizedEdge>();
			listToCheck.add((IMinimizedEdge) node.getIncomingEdges().get(0));
			listToCheck.addAll(node.getMinimalOutgoingEdgeLevel());

			for (IMinimizedEdge edgeToCheck : listToCheck) {
				if (edgeToCheck.isBasicEdge()) {
					IBasicEdge basic = (IBasicEdge) edgeToCheck;
					if (basic.getOriginalEdge() instanceof Call
							|| basic.getOriginalEdge() instanceof Return
							|| basic.getOriginalEdge() instanceof Summary) {
						return false;
					}
				}
			}
			return true;
		}
		return false;
	}

}
