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
package de.uni_freiburg.informatik.ultimate.blockencoding.test.unit;

import java.util.ArrayList;
import java.util.HashSet;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.MinimizeBranchVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.MinimizeLoopVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.test.ExecuteUnitTestObserver;
import de.uni_freiburg.informatik.ultimate.blockencoding.test.util.RCFGStore;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import junit.framework.TestCase;

/**
 * The object under test is the MinimizeLoopVisitor, which is responsible for
 * minimizing branching sequential parts, that means nodes with one incoming and
 * multiple outgoing edges can be merged. But we do this afterwards the basic
 * minimization.
 * 
 * @author Stefan Wissert
 * 
 */
public class TestMinimizeLoopVisitor extends TestCase {

	/**
	 * the object under test.
	 */
	private MinimizeLoopVisitor mlv;

	private MinimizeBranchVisitor mbv;

	private IcfgLocation rcfgNode;

	private ILogger logger;

	private HashSet<IMinimizedEdge> visitedEdges;

	private HashSet<MinimizedNode> mergeableNodes;
	
	private final IUltimateServiceProvider mServices = null;


	/*
	 * (non-Javadoc)
	 * 
	 * @see junit.framework.TestCase#setUp()
	 */
	@Override
	protected void setUp() throws Exception {
		rcfgNode = RCFGStore.getRCFG();
		logger = ExecuteUnitTestObserver.getLogger();
		mbv = new MinimizeBranchVisitor(logger);
		mlv = new MinimizeLoopVisitor(logger, mServices);
		visitedEdges = new HashSet<IMinimizedEdge>();
		mergeableNodes = new HashSet<MinimizedNode>();
	}

	@Test
	public void testSequentialBranchingMinimization() {
		// Since we not directly minimize the root node, we have to iterate
		// first over the RootEdges
		assertTrue(rcfgNode instanceof RootNode);
		assertNotNull(rcfgNode.getOutgoingEdges());
		for (final IcfgEdge edge : rcfgNode.getOutgoingEdges()) {
			assertTrue(edge instanceof RootEdge);
			assertTrue(edge.getTarget() instanceof BoogieIcfgLocation);
			testMinimizationOfFunction((BoogieIcfgLocation) edge.getTarget());
		}
	}

	private void testMinimizationOfFunction(final BoogieIcfgLocation entryPoint) {
		assertNotNull(entryPoint.getIncomingEdges());
		// It can happen that while minimizing we already created an Min.Node we
		// have to use here
		MinimizedNode minEntryPoint = mbv
				.getReferencedMethodEntryNode(entryPoint);
		// Probably it can be null
		if (minEntryPoint == null) {
			minEntryPoint = new MinimizedNode(entryPoint);
		}
		// the object mapping should be the same
		assertEquals(minEntryPoint.getOriginalNode(), entryPoint);
		// Since we already tested that the initialization is right, we now
		// execute the minimization and compare the result with the original
		// RCFG
		mbv.visitNode(minEntryPoint);
		// now it is possible that we can minimize sequentially,
		// with one incoming and multiple outgoing edges
		// to validate our visitor we first collect all nodes which can be
		// removed from the minimized graph, then we run the visitor and then we
		// check whether our expectation holds or not
		visitedEdges.clear();
		mergeableNodes.clear();
		collectMergeableNodes(minEntryPoint);
		// now we run the MinimizeLoopVisitor
		mlv.visitNode(minEntryPoint);
		// and now we check if all nodes are out of the new graph and if we
		// there are maybe other nodes that are still not minimized
		visitedEdges.clear();
		checkSeqBranchMinimization(minEntryPoint);
	}

	private void collectMergeableNodes(final MinimizedNode node) {
		assertNotNull(node.getOutgoingEdges());
		if (node.getOutgoingEdges().size() == 0) {
			return;
		}
		// we check this node if it is mergeable or not
		assertNotNull(node.getIncomingEdges());
		if (checkForSequentialMerge(node)) {
			mergeableNodes.add(node);
		}

		for (final IMinimizedEdge edge : node.getOutgoingEdges()) {
			// We ignore Call- and Return-Edges
			// They will be processed later
			if (edge.isBasicEdge()
					&& (((IBasicEdge) edge).getOriginalEdge() instanceof Call || ((IBasicEdge) edge)
							.getOriginalEdge() instanceof Return)) {
				continue;
			}
			if (!visitedEdges.contains(edge)) {
				visitedEdges.add(edge);
				collectMergeableNodes(edge.getTarget());
			}
		}
	}
	
	private void checkSeqBranchMinimization(final MinimizedNode node) {
		assertNotNull(node.getOutgoingEdges());
		if (node.getOutgoingEdges().size() == 0) {
			return;
		}
		// now we check if there is any mergeable node left!
		assertFalse(mergeableNodes.contains(node));
		assertFalse(checkForSequentialMerge(node));
		for (final IMinimizedEdge edge : node.getOutgoingEdges()) {
			// We ignore Call- and Return-Edges
			// They will be processed later
			if (edge.isBasicEdge()
					&& (((IBasicEdge) edge).getOriginalEdge() instanceof Call || ((IBasicEdge) edge)
							.getOriginalEdge() instanceof Return)) {
				continue;
			}
			if (!visitedEdges.contains(edge)) {
				visitedEdges.add(edge);
				collectMergeableNodes(edge.getTarget());
			}
		}
	}

	private boolean checkForSequentialMerge(final MinimizedNode node) {
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
					return false;
				}
				if (targetNodes.contains(edge.getTarget())) {
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
}
