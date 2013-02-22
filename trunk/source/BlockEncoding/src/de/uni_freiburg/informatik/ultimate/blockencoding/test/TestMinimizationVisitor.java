/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.test;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.AbstractMinimizationVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * This visitor is used to validate the minimization results. It should iterate
 * over the minimized graph and check if he could apply a minimization rule. If
 * this is possible, we can say that the minimization is not complete.
 * 
 * @author Stefan Wissert
 * 
 */
public class TestMinimizationVisitor extends AbstractMinimizationVisitor {


	public TestMinimizationVisitor(Logger logger) {
		super(logger);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.
	 * AbstractRCFGVisitor
	 * #applyMinimizationRules(de.uni_freiburg.informatik.ultimate
	 * .blockencoding.model.MinimizedNode)
	 */
	@Override
	protected MinimizedNode[] applyMinimizationRules(MinimizedNode node) {
		// check if sequential merge is possible
		if (checkIfSequentialMergePossible(node)) {
			s_Logger.error("Sequential Minimization is possible -> so Minimization is not complete");
			s_Logger.info("Node: " + node);
			s_Logger.info("Incoming Edges: " + node.getIncomingEdges());
			s_Logger.info("Outgoing Edges: " + node.getOutgoingEdges());
			return new MinimizedNode[0];
		}
		// check if parallel merge is possible
		if (checkIfParallelMergePossible(node)) {
			s_Logger.error("Parallel Minimization is possible -> so Minimization is not complete");
			s_Logger.info("Node: " + node);
			s_Logger.info("Incoming Edges: " + node.getIncomingEdges());
			s_Logger.info("Outgoing Edges: " + node.getOutgoingEdges());
			return new MinimizedNode[0];
		}
		return new MinimizedNode[0];
	}

	private boolean checkIfSequentialMergePossible(MinimizedNode node) {
		// In this run there can be nodes with one incoming and two outgoing
		// edges, which we also want to merge
		if (checkForMultipleSequentialMerge(node)) {
			return true;
		} else if (node.getIncomingEdges().size() == 1
				&& node.getOutgoingEdges().size() == 1) {
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

	private boolean checkForMultipleSequentialMerge(MinimizedNode node) {
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

	private boolean checkIfParallelMergePossible(MinimizedNode node) {
		// In this implementation we check for incoming edges of the same source
		if (node.getIncomingEdges() == null
				|| node.getIncomingEdges().size() <= 1) {
			return false;
		}
		HashMap<MinimizedNode, IMinimizedEdge> pointingMap = new HashMap<MinimizedNode, IMinimizedEdge>();
		for (IMinimizedEdge incomingEdge : node.getMinimalIncomingEdgeLevel()) {
			if (!pointingMap.containsKey(incomingEdge.getSource())) {
				pointingMap.put(incomingEdge.getSource(), incomingEdge);
			} else {
				IMinimizedEdge parallelEdge = pointingMap.get(incomingEdge
						.getSource());
				// Check for Duplication in Formulas, TODO: This may be
				// algorithmic fixed
				if (!incomingEdge.isBasicEdge()) {
					if (((ICompositeEdge) incomingEdge)
							.duplicationOfFormula(parallelEdge)) {
						return false;
					}
				} else if (!parallelEdge.isBasicEdge()) {
					if (((ICompositeEdge) parallelEdge)
							.duplicationOfFormula(incomingEdge)) {
						return false;
					}
				}
				return true;
			}
		}
		return false;
	}

}
