/*
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 * 
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.algorithm;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.ConjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.ShortcutErrEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
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
	public MinimizeBranchVisitor(final ILogger logger) {
		super(logger);
	}

	@Override
	protected MinimizedNode[] applyMinimizationRules(final MinimizedNode node) {
		// if this node is not reachable anymore (since we cut it off, by
		// merging sequentially) we do not apply our minimization rules
		// ---> the node is not part of the graph anymore
		if (notReachableNodes.contains(node)) {
			return new MinimizedNode[0];
		}
		final ArrayList<MinimizedNode> reVisitNodes = new ArrayList<MinimizedNode>();
		// First check is for parallel edges, we want to merge
		final IMinimizedEdge[] parallelEdges = checkForParallelMerge(node);
		if (parallelEdges.length == 2) {
			mLogger.debug("Parallel Merge: " + parallelEdges[0] + " v "
					+ parallelEdges[1]);
			reVisitNodes.add(mergeParallel(parallelEdges[0], parallelEdges[1]));
		}
		// Sequential-Merge of two edges:
		if (checkForSequentialMerge(node)) {
			final IMinimizedEdge out = node.getMinimalOutgoingEdgeLevel().get(0);
			final IMinimizedEdge in = node.getMinimalIncomingEdgeLevel().get(0);
			if (mVisitedEdges.contains(in) && mVisitedEdges.contains(out)) {
				return reVisitNodes.toArray(new MinimizedNode[reVisitNodes.size()]);
			}
			mLogger.debug("Sequential Merge: " + in + " /\\ " + out);
			final MinimizedNode[] succNodes = mergeSequential(in, out);

			// In every case we revisit the merged node
			mVisitedEdges.add(out);
			mVisitedEdges.add(in);
			for (final MinimizedNode succ : succNodes) {
				reVisitNodes.add(succ);
			}
		}
		return reVisitNodes.toArray(new MinimizedNode[reVisitNodes.size()]);
	}

	/**
	 * This method checks the incoming edges of a node, if they have parallel
	 * edges, if so it return an array which contains exactly those two edges
	 * 
	 * @param node
	 *            the node to inspect
	 * @return an array with exactly two or zero entries
	 */
	private IMinimizedEdge[] checkForParallelMerge(final MinimizedNode node) {
		// In this implementation we check for incoming edges of the same source
		if (node.getIncomingEdges() == null
				|| node.getIncomingEdges().size() <= 1) {
			return new IMinimizedEdge[0];
		}
		final HashMap<MinimizedNode, IMinimizedEdge> pointingMap = new HashMap<MinimizedNode, IMinimizedEdge>();
		final ArrayList<IMinimizedEdge> parallelEdges = new ArrayList<IMinimizedEdge>();
		for (final IMinimizedEdge incomingEdge : node.getMinimalIncomingEdgeLevel()) {
			if (!pointingMap.containsKey(incomingEdge.getSource())) {
				pointingMap.put(incomingEdge.getSource(), incomingEdge);
			} else {
				// We found a parallel edge
				// TODO: can there exist more than two parallel edges?
				parallelEdges.add(incomingEdge);
				parallelEdges.add(pointingMap.get(incomingEdge.getSource()));
				final IMinimizedEdge parallelEdge = pointingMap.get(incomingEdge
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
				return parallelEdges.toArray(new IMinimizedEdge[parallelEdges.size()]);
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
	private boolean checkForSequentialMerge(final MinimizedNode node) {
		// First condition: --->(node)--->
		if (node.getIncomingEdges().size() == 1
				&& node.getOutgoingEdges().size() == 1) {
			final IMinimizedEdge incoming = node.getIncomingEdges()
					.get(0);
			final IMinimizedEdge outgoing = node.getOutgoingEdges()
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
	private MinimizedNode mergeParallel(final IMinimizedEdge edge1,
			final IMinimizedEdge edge2) {
		final DisjunctionEdge disjunction = new DisjunctionEdge(edge1, edge2);
		final ArrayList<IMinimizedEdge> outgoingList = new ArrayList<IMinimizedEdge>();
		outgoingList.add(disjunction);
		// the outgoing edges of disjunction.getSource() maybe not initialized
		if (disjunction.getSource().getOutgoingEdges() == null) {
			initializeOutgoingEdges(disjunction.getSource());
		}

		for (final IMinimizedEdge edge : disjunction.getSource()
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
		final ArrayList<IMinimizedEdge> incomingList = new ArrayList<IMinimizedEdge>();
		incomingList.add(disjunction);
		for (final IMinimizedEdge edge : disjunction.getTarget()
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
		mVisitedEdges.add(edge1);
		mVisitedEdges.add(edge2);
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
	protected MinimizedNode[] mergeSequential(final IMinimizedEdge edge1,
			final IMinimizedEdge edge2) {
		ConjunctionEdge conjunction;
		if (edge1 instanceof ShortcutErrEdge || edge2 instanceof ShortcutErrEdge) {
			conjunction = new ShortcutErrEdge(edge1, edge2);
		} else {
			conjunction = new ConjunctionEdge(edge1, edge2);
		}
		// We have to compute the new outgoing edge level list
		final ArrayList<IMinimizedEdge> outgoingList = new ArrayList<IMinimizedEdge>();
		outgoingList.add(conjunction);
		// the outgoing edges of conjunction.getSource() maybe not initialized
		if (conjunction.getSource().getOutgoingEdges() == null) {
			initializeOutgoingEdges(conjunction.getSource());
		}
		for (final IMinimizedEdge edge : conjunction.getSource()
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
		final ArrayList<IMinimizedEdge> incomingList = new ArrayList<IMinimizedEdge>();
		incomingList.add(conjunction);
		for (final IMinimizedEdge edge : conjunction.getTarget()
				.getMinimalIncomingEdgeLevel()) {
			if (edge != edge1 && edge != edge2) {
				incomingList.add(edge);
			}
		}
		conjunction.getTarget().addNewIncomingEdgeLevel(incomingList);
		// new SequentialComposition(pre, succ, boogie2smt, edge1, edge2);
		mVisitedEdges.add(edge1);
		mVisitedEdges.add(edge2);
		notReachableNodes.add(edge1.getTarget());
		return new MinimizedNode[] { conjunction.getTarget() };
	}
}
