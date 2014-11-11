/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.algorithm;

import java.util.ArrayList;
import java.util.HashMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.ConjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.ShortcutErrEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

/**
 * This class is a Visitor on the RCFG, so while calling the visitNode method we
 * traverse the whole tree. While doing this we try to minimize it according to
 * the following rules. <br>
 * <b>Sequential:</b> ---> node ---> <br>
 * All nodes with exactly one incoming and one outgoing edge <br>
 * <b>Parallel:</b> <br>
 * All parallel edges will be merges, as late as possible, this keeps the
 * formulas as small as possible
 * 
 * @author Stefan Wissert
 */
public class MinimizeBranchVisitor extends AbstractMinimizationVisitor {

	/**
	 * Constructor for the MinimizeBranchVisitor
	 * 
	 */
	public MinimizeBranchVisitor(Logger logger) {
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
		// First check is for parallel edges, we want to merge
		IMinimizedEdge[] parallelEdges = checkForParallelMerge(node);
		if (parallelEdges.length == 2) {
			s_Logger.debug("Parallel Merge: " + parallelEdges[0] + " v "
					+ parallelEdges[1]);
			reVisitNodes.add(mergeParallel(parallelEdges[0], parallelEdges[1]));
		}
		// Sequential-Merge of two edges:
		if (checkForSequentialMerge(node)) {
			IMinimizedEdge out = node.getMinimalOutgoingEdgeLevel().get(0);
			IMinimizedEdge in = node.getMinimalIncomingEdgeLevel().get(0);
			if (visitedEdges.contains(in) && visitedEdges.contains(out)) {
				return reVisitNodes.toArray(new MinimizedNode[0]);
			}
			s_Logger.debug("Sequential Merge: " + in + " /\\ " + out);
			MinimizedNode[] succNodes = mergeSequential(in, out);

			// In every case we revisit the merged node
			visitedEdges.add(out);
			visitedEdges.add(in);
			for (MinimizedNode succ : succNodes) {
				reVisitNodes.add(succ);
			}
		}
		return reVisitNodes.toArray(new MinimizedNode[0]);
	}

	/**
	 * This method checks the incoming edges of a node, if they have parallel
	 * edges, if so it return an array which contains exactly those two edges
	 * 
	 * @param node
	 *            the node to inspect
	 * @return an array with exactly two or zero entries
	 */
	private IMinimizedEdge[] checkForParallelMerge(MinimizedNode node) {
		// In this implementation we check for incoming edges of the same source
		if (node.getIncomingEdges() == null
				|| node.getIncomingEdges().size() <= 1) {
			return new IMinimizedEdge[0];
		}
		HashMap<MinimizedNode, IMinimizedEdge> pointingMap = new HashMap<MinimizedNode, IMinimizedEdge>();
		ArrayList<IMinimizedEdge> parallelEdges = new ArrayList<IMinimizedEdge>();
		for (IMinimizedEdge incomingEdge : node.getMinimalIncomingEdgeLevel()) {
			if (!pointingMap.containsKey(incomingEdge.getSource())) {
				pointingMap.put(incomingEdge.getSource(), incomingEdge);
			} else {
				// We found a parallel edge
				// TODO: can there exist more than two parallel edges?
				parallelEdges.add(incomingEdge);
				parallelEdges.add(pointingMap.get(incomingEdge.getSource()));
				IMinimizedEdge parallelEdge = pointingMap.get(incomingEdge
						.getSource());
				// ParallelEdges maybe Return-Edges, we do not merge them
				if (incomingEdge.isBasicEdge()
						&& ((IBasicEdge) incomingEdge).getOriginalEdge() instanceof Return) {
					return new IMinimizedEdge[0];
				}
				if (parallelEdge.isBasicEdge()
						&& ((IBasicEdge) parallelEdge).getOriginalEdge() instanceof Return) {
					throw new IllegalArgumentException("");
				}
				// Check for Duplication in Formulas, TODO: This may be
				// algorithmic fixed
				if (!incomingEdge.isBasicEdge()) {
					if (((ICompositeEdge) incomingEdge)
							.duplicationOfFormula(parallelEdge)) {
						return new IMinimizedEdge[0];
					}
				} else if (!parallelEdge.isBasicEdge()) {
					if (((ICompositeEdge) parallelEdge)
							.duplicationOfFormula(incomingEdge)) {
						return new IMinimizedEdge[0];
					}
				}
				return parallelEdges.toArray(new IMinimizedEdge[0]);
			}
		}
		return new IMinimizedEdge[0];
	}

	/**
	 * This method check if it is allowed to merge sequentially
	 * 
	 * @param node
	 *            the node to check
	 * @return true if we can merge sequentially
	 */
	private boolean checkForSequentialMerge(MinimizedNode node) {
		// First condition: --->(node)--->
		if (node.getIncomingEdges().size() == 1
				&& node.getOutgoingEdges().size() == 1) {
			IMinimizedEdge incoming = (IMinimizedEdge) node.getIncomingEdges()
					.get(0);
			IMinimizedEdge outgoing = (IMinimizedEdge) node.getOutgoingEdges()
					.get(0);

			// If they are basic edges, we do not want to have Call, Return,
			// Summary
			if (incoming.isBasicEdge()) {
				// Next condition we do not merge Call, Return and Summary edges
				if (((IBasicEdge) incoming).getOriginalEdge() instanceof Call) {
					return false;
				}
				if (((IBasicEdge) incoming).getOriginalEdge() instanceof Return) {
					return false;
				}
// Following three lines were commented by Matthias at 2014-10-08 because
// he thought that it is ok to merge summary edges with other edges.
//				if (((IBasicEdge) incoming).getOriginalEdge() instanceof Summary) {
//					return false;
//				}
			}
			if (outgoing.isBasicEdge()) {
				if (((IBasicEdge) outgoing).getOriginalEdge() instanceof Call) {
					return false;
				}
				if (((IBasicEdge) outgoing).getOriginalEdge() instanceof Return) {
					return false;
				}
// Following three lines were commented by Matthias at 2014-10-08 because
// he thought that it is ok to merge summary edges with other edges.
//				if (((IBasicEdge) outgoing).getOriginalEdge() instanceof Summary) {
//					return false;
//				}
			}
			return true;
		}
		return false;
	}

	/**
	 * This method merges two parallel edges into one edge
	 * 
	 * @param edge1
	 *            first parallel edge
	 * @param edge2
	 *            second parallel edge
	 * @return the next node to visit, in our algorithm the predecessor of the
	 *         merged parallel edges
	 */
	private MinimizedNode mergeParallel(IMinimizedEdge edge1,
			IMinimizedEdge edge2) {
		DisjunctionEdge disjunction = new DisjunctionEdge(edge1, edge2);
		ArrayList<IMinimizedEdge> outgoingList = new ArrayList<IMinimizedEdge>();
		outgoingList.add(disjunction);
		// the outgoing edges of disjunction.getSource() maybe not initialized
		if (disjunction.getSource().getOutgoingEdges() == null) {
			initializeOutgoingEdges(disjunction.getSource());
		}

		for (IMinimizedEdge edge : disjunction.getSource()
				.getMinimalOutgoingEdgeLevel()) {
			if (edge != edge1 && edge != edge2) {
				outgoingList.add(edge);
			}
		}
		// we have to add a new minimized level for the outgoing edges
		disjunction.getSource().addNewOutgoingEdgeLevel(outgoingList, null);
		if (disjunction.getTarget().getIncomingEdges() == null) {
			initializeIncomingEdges(disjunction.getTarget());
		}
		ArrayList<IMinimizedEdge> incomingList = new ArrayList<IMinimizedEdge>();
		incomingList.add(disjunction);
		for (IMinimizedEdge edge : disjunction.getTarget()
				.getMinimalIncomingEdgeLevel()) {
			if (edge != edge1 && edge != edge2) {
				incomingList.add(edge);
			}
		}
		// and also we have to add a new minimized level for the incoming edges
		disjunction.getTarget().addNewIncomingEdgeLevel(incomingList);
		// merge the parallel ones
		// new ParallelComposition((ProgramPoint) edge1.getSource(),
		// (ProgramPoint) edge1.getTarget(), boogie2smt, edge1, edge2);
		visitedEdges.add(edge1);
		visitedEdges.add(edge2);
		return disjunction.getSource();
	}

	/**
	 * This method merges two sequential edges into one edge
	 * 
	 * @param edge1
	 *            first sequential edge
	 * @param edge2
	 *            second sequential edge
	 * @return the next node to visit, in our algorithm this is the target of
	 *         edge 2
	 */
	protected MinimizedNode[] mergeSequential(IMinimizedEdge edge1,
			IMinimizedEdge edge2) {
		ConjunctionEdge conjunction;
		if (edge1 instanceof ShortcutErrEdge || edge2 instanceof ShortcutErrEdge) {
			conjunction = new ShortcutErrEdge(edge1, edge2);
		} else {
			conjunction = new ConjunctionEdge(edge1, edge2);
		}
		// We have to compute the new outgoing edge level list
		ArrayList<IMinimizedEdge> outgoingList = new ArrayList<IMinimizedEdge>();
		outgoingList.add(conjunction);
		// the outgoing edges of conjunction.getSource() maybe not initialized
		if (conjunction.getSource().getOutgoingEdges() == null) {
			initializeOutgoingEdges(conjunction.getSource());
		}
		for (IMinimizedEdge edge : conjunction.getSource()
				.getMinimalOutgoingEdgeLevel()) {
			if (edge != edge1 && edge != edge2) {
				outgoingList.add(edge);
			}
		}
		conjunction.getSource().addNewOutgoingEdgeLevel(outgoingList, null);
		// IncomingEdges of conjunction.getTarget() may not initialized!
		if (conjunction.getTarget().getIncomingEdges() == null) {
			initializeIncomingEdges(conjunction.getTarget());
		}
		ArrayList<IMinimizedEdge> incomingList = new ArrayList<IMinimizedEdge>();
		incomingList.add(conjunction);
		for (IMinimizedEdge edge : conjunction.getTarget()
				.getMinimalIncomingEdgeLevel()) {
			if (edge != edge1 && edge != edge2) {
				incomingList.add(edge);
			}
		}
		conjunction.getTarget().addNewIncomingEdgeLevel(incomingList);
		// new SequentialComposition(pre, succ, boogie2smt, edge1, edge2);
		visitedEdges.add(edge1);
		visitedEdges.add(edge2);
		notReachableNodes.add(edge1.getTarget());
		return new MinimizedNode[] { conjunction.getTarget() };
	}
}
