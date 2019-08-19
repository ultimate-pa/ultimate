/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
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
package de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.visitor;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.AbstractMinimizationVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
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

	public TestMinimizationVisitor(ILogger logger) {
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
			mLogger.error("Sequential Minimization is possible -> so Minimization is not complete");
			mLogger.info("Node: " + node);
			mLogger.info("Incoming Edges: " + node.getIncomingEdges());
			mLogger.info("Outgoing Edges: " + node.getOutgoingEdges());
			return new MinimizedNode[0];
		}
		// check if parallel merge is possible
		if (checkIfParallelMergePossible(node)) {
			mLogger.error("Parallel Minimization is possible -> so Minimization is not complete");
			mLogger.info("Node: " + node);
			mLogger.info("Incoming Edges: " + node.getIncomingEdges());
			mLogger.info("Outgoing Edges: " + node.getOutgoingEdges());
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
			final ArrayList<IMinimizedEdge> listToCheck = new ArrayList<IMinimizedEdge>();
			listToCheck.add(node.getIncomingEdges().get(0));
			listToCheck.addAll(node.getMinimalOutgoingEdgeLevel());

			for (final IMinimizedEdge edgeToCheck : listToCheck) {
				if (edgeToCheck.isBasicEdge()) {
					final IBasicEdge basic = (IBasicEdge) edgeToCheck;
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
			for (final IcfgEdge edge : node.getOriginalNode().getIncomingEdges()) {
				if (edge instanceof RootEdge) {
					return false;
				}
			}
			final HashSet<MinimizedNode> targetNodes = new HashSet<MinimizedNode>();
			for (final IMinimizedEdge edge : node.getMinimalOutgoingEdgeLevel()) {
				// We do not include self-loops
				if (edge.getTarget() == node) {
					mLogger.info("Found a self-loop, should not happen");
					return false;
				}
				if (targetNodes.contains(edge.getTarget())) {
					mLogger.info("Found Parallel Nodes, should not happen");
					return false;
				}
				targetNodes.add(edge.getTarget());
			}

			// Second condition: edges are of type CodeBlock
			// In order to do this for many edges we use a list here
			final ArrayList<IMinimizedEdge> listToCheck = new ArrayList<IMinimizedEdge>();
			listToCheck.add(node.getIncomingEdges().get(0));
			listToCheck.addAll(node.getMinimalOutgoingEdgeLevel());

			for (final IMinimizedEdge edgeToCheck : listToCheck) {
				if (edgeToCheck.isBasicEdge()) {
					final IBasicEdge basic = (IBasicEdge) edgeToCheck;
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
		final HashMap<MinimizedNode, IMinimizedEdge> pointingMap = new HashMap<MinimizedNode, IMinimizedEdge>();
		for (final IMinimizedEdge incomingEdge : node.getMinimalIncomingEdgeLevel()) {
			if (!pointingMap.containsKey(incomingEdge.getSource())) {
				pointingMap.put(incomingEdge.getSource(), incomingEdge);
			} else {
				final IMinimizedEdge parallelEdge = pointingMap.get(incomingEdge
						.getSource());
				// ParallelEdges maybe Return-Edges, we do not merge them
				if (incomingEdge.isBasicEdge()
						&& ((IBasicEdge) incomingEdge).getOriginalEdge() instanceof Return) {
					return false;
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
