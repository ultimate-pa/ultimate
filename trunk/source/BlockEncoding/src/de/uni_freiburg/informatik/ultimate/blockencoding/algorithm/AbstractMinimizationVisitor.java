/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.visitor.IMinimizationVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.BasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;

/**
 * This abstract class, is the base class for visitor who want to minimize the CFG. It traverses the CFG, according to
 * DFS and makes sure that every edge is only visited once. <br>
 * While traversing the RCFG, it builds up the new data model (->MinimizedNode) and initializes the nodes, if this had
 * not happen before <br>
 * It provides for subclasses an abstract method, which they could implement to apply the minimization rules.
 *
 * @author Stefan Wissert
 *
 */
public abstract class AbstractMinimizationVisitor implements IMinimizationVisitor {

	protected HashSet<IMinimizedEdge> mVisitedEdges;

	protected HashSet<MinimizedNode> notReachableNodes;

	protected final ILogger mLogger;

	private final HashMap<BoogieIcfgLocation, MinimizedNode> referenceNodeMap;

	private final HashMap<CodeBlock, IMinimizedEdge> referenceEdgeMap;

	private final HashMap<String, MinimizedNode> referenceToMethodEntry;

	private boolean containsCallReturnEdge;

	/**
	 * Constructor which is called by the subclasses, to initialize the data structures
	 */
	protected AbstractMinimizationVisitor(final ILogger logger) {
		mLogger = logger;
		mVisitedEdges = new HashSet<>();
		notReachableNodes = new HashSet<>();
		referenceNodeMap = new HashMap<>();
		referenceEdgeMap = new HashMap<>();
		referenceToMethodEntry = new HashMap<>();
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see de.uni_freiburg.informatik.ultimate.blockencoding.interfaces.visitor. IRCFGVisitor
	 * #visitNode(de.uni_freiburg.informatik.ultimate.blockencoding.model .MinimizedNode)
	 */
	@Override
	public void visitNode(final MinimizedNode node) {
		// Remark 14.02.2012
		// It can happen that, we have already an instance of an MinimizedNode,
		// this must be used here. So ask here our referenceNodeMap.
		if (!referenceNodeMap.containsKey(node.getOriginalNode())) {
			referenceNodeMap.put(node.getOriginalNode(), node);
		}
		mVisitedEdges.clear();
		notReachableNodes.clear();
		containsCallReturnEdge = false;
		referenceToMethodEntry.put(node.getOriginalNode().getProcedure(), node);
		internalVisitNode(node);
	}

	/**
	 * The internally used visit-Method. This is necessary because we need to reset the visitedEdges-Set
	 *
	 * @param node
	 *            the node to visit
	 */
	private void internalVisitNode(final MinimizedNode node) {

		// While traversing we are also building up the new model
		if (node.getOutgoingEdges() == null) {
			initializeOutgoingEdges(node);
		}

		if (node.getIncomingEdges() == null) {
			initializeIncomingEdges(node);
		}

		// We have no outgoing edges, so we reached an end of the recursion
		if (node.getOutgoingEdges().size() == 0) {
			// Special Case: The last node can have multiple incoming nodes
			// --> so a parallel merge is possible, we should apply the rules
			// here!
			applyMinimizationRules(node);
			return;
		}

		// abstract method where the minimize visitor can apply there rules
		final MinimizedNode[] reVisitNodes = applyMinimizationRules(node);
		if (reVisitNodes.length > 0) {
			for (final MinimizedNode toVisitNode : reVisitNodes) {
				internalVisitNode(toVisitNode);
			}

		} else {
			final ArrayList<IMinimizedEdge> edgeList = new ArrayList<>(node.getMinimalOutgoingEdgeLevel());
			for (final IMinimizedEdge edge : edgeList) {
				if (edge.isBasicEdge()) {
					// We ignore Call- and Return-Edges
					// They will be processed later
					// TODO: The intuition behind this is unclear!
					final CodeBlock block = ((IBasicEdge) edge).getOriginalEdge();
					if (block instanceof Call) {
						containsCallReturnEdge = true;
						continue;
					}
					if (block instanceof Return) {
						continue;
					}
				}

				if (!mVisitedEdges.contains(edge)) {
					mVisitedEdges.add(edge);
					if (edge.getTarget() != null) {
						internalVisitNode(edge.getTarget());
					}
				}
			}
		}

	}

	/**
	 * Abstract method, which should be implemented by the minimization Visitors.
	 *
	 * @param node
	 *            the node to check if minimization is possible
	 * @return an array of nodes which should be revisited, because we changed their edges
	 */
	protected abstract MinimizedNode[] applyMinimizationRules(MinimizedNode node);

	/**
	 * @param node
	 */
	protected void initializeOutgoingEdges(final MinimizedNode node) {
		// OutgoingEdges of MinimizedNode are not initialized
		final ArrayList<IMinimizedEdge> outEdges = new ArrayList<>();
		for (final IcfgEdge edge : node.getOriginalNode().getOutgoingEdges()) {
			outEdges.add(getReferencedMinEdge((CodeBlock) edge, node,
					getReferencedMinNode((BoogieIcfgLocation) edge.getTarget(), edge, false)));
		}
		node.addNewOutgoingEdgeLevel(outEdges, null);
	}

	/**
	 * @param node
	 */
	protected void initializeIncomingEdges(final MinimizedNode node) {
		// IncomingEdges of MinimizedNode are not initialized
		final ArrayList<IMinimizedEdge> inEdges = new ArrayList<>();
		for (final IcfgEdge edge : node.getOriginalNode().getIncomingEdges()) {
			if (edge instanceof RootEdge) {
				continue;
			}
			inEdges.add(getReferencedMinEdge((CodeBlock) edge,
					getReferencedMinNode((BoogieIcfgLocation) edge.getSource(), edge, true), node));
		}
		node.addNewIncomingEdgeLevel(inEdges);
	}

	/**
	 * @param originalEdge
	 * @param source
	 * @param target
	 * @return
	 */
	private IMinimizedEdge getReferencedMinEdge(final CodeBlock originalEdge, final MinimizedNode source,
			final MinimizedNode target) {
		if (!referenceEdgeMap.containsKey(originalEdge)) {
			referenceEdgeMap.put(originalEdge, new BasicEdge(originalEdge, source, target));
		}
		return referenceEdgeMap.get(originalEdge);
	}

	/**
	 * @param originalNode
	 * @return
	 */
	private MinimizedNode getReferencedMinNode(final BoogieIcfgLocation originalNode, final IcfgEdge edge,
			final boolean incoming) {
		if (!referenceNodeMap.containsKey(originalNode)) {
			final MinimizedNode minNode = new MinimizedNode(originalNode);
			referenceNodeMap.put(originalNode, minNode);
		}
		return referenceNodeMap.get(originalNode);
	}

	/**
	 * If we have a call edge to an method entry (Ultimate.START), we create while visiting one method, an
	 * MinimizedNode. We have to use it later, since we want to keep our references.
	 *
	 * @param methodEntry
	 * @return null if there is no referenced node.
	 */
	public MinimizedNode getReferencedMethodEntryNode(final BoogieIcfgLocation methodEntry) {
		if (referenceNodeMap.containsKey(methodEntry)) {
			return referenceNodeMap.get(methodEntry);
		}
		return null;
	}

	/**
	 * Now we can determine if for a certain visitor run (method node) there exists a outgoing call edge. This is needed
	 * because there is a possible duplication of formulas (detected on 03.04.2013 on pipline_unsafe.cil.c)
	 *
	 * @return true, if there is an outgoing call edge
	 */
	public boolean isCallReturnEdgeInvolved() {
		return containsCallReturnEdge;
	}

	/**
	 * @param node
	 * @return
	 */
	public MinimizedNode getCorrespondingStartNode(final MinimizedNode node) {
		if (referenceToMethodEntry.containsKey(node.getOriginalNode().getProcedure())) {
			return referenceToMethodEntry.get(node.getOriginalNode().getProcedure());
		}
		throw new IllegalArgumentException("There should be a start node for every procedure!");
	}
}
