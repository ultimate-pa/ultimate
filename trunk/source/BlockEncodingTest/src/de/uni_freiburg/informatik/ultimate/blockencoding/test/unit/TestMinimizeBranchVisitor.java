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

import java.util.HashSet;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.MinimizeBranchVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.ConjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.test.ExecuteUnitTestObserver;
import de.uni_freiburg.informatik.ultimate.blockencoding.test.util.RCFGStore;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
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
 * This Test has the purpose to test the minimization, which is done by the
 * MinimizeBranchVisitor. There we minimize easy sequential parts (-->X-->) and
 * parallel parts which are common, for example in standard if-Branches.
 * 
 * @author Stefan Wissert
 * 
 */
public class TestMinimizeBranchVisitor extends TestCase {

	/**
	 * the object under test.
	 */
	private MinimizeBranchVisitor mbv;

	/**
	 * the start node of the given rcfg.
	 */
	private IcfgLocation rcfgNode;

	private ILogger logger;

	private HashSet<IMinimizedEdge> visitedEdges;

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
		visitedEdges = new HashSet<IMinimizedEdge>();
	}

	@Test
	public void testBasicMinimizationOfRCFG() {
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

	private void testMinimizationOfFunction(BoogieIcfgLocation entryPoint) {
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
		// Now we have to validate, the result of our minimization
		// To do this we iterate over the result graph and check the minimized
		// edges if they are converted correctly
		iterateOverMinModel(minEntryPoint);
	}

	private void iterateOverMinModel(MinimizedNode node) {
		assertNotNull(node.getOutgoingEdges());
		if (node.getOutgoingEdges().size() == 0) {
			return;
		}
		for (final IMinimizedEdge edge : node.getOutgoingEdges()) {
			// We ignore Call- and Return-Edges
			// They will be processed later
			if (edge.isBasicEdge()
					&& (((IBasicEdge) edge).getOriginalEdge() instanceof Call || ((IBasicEdge) edge)
							.getOriginalEdge() instanceof Return)) {
				continue;
			}
			if (visitedEdges.contains(edge)) {
				continue;
			}
			visitedEdges.add(edge);
			analyzeMinimizedEdge(edge);
			// check if this edge can be merged sequentially
			assertNotNull(edge.getTarget().getOutgoingEdges());
			assertNotNull(edge.getTarget().getIncomingEdges());
			if (edge.getTarget().getIncomingEdges().size() == 1) {
				if (edge.getTarget().getOutgoingEdges().size() == 1) {
					final IMinimizedEdge minEdge = edge.getTarget()
							.getOutgoingEdges().get(0);
					assertTrue(minEdge.isBasicEdge());
					assertTrue(((IBasicEdge) minEdge).getOriginalEdge() instanceof Summary
							|| ((IBasicEdge) minEdge).getOriginalEdge() instanceof Return);
				} else {
					assertTrue(edge.getTarget().getOutgoingEdges().size() > 1
							|| edge.getTarget().getOutgoingEdges().size() == 0);
				}
			}
			// check if this edge can be merged parallel
			assertNotNull(edge.getSource().getOutgoingEdges());
			for (final IMinimizedEdge checkEdge : edge.getSource().getOutgoingEdges()) {
				if (checkEdge == edge) {
					continue;
				}
				assertFalse(edge.getTarget().equals(checkEdge.getTarget()));
			}
			iterateOverMinModel(edge.getTarget());
		}
	}

	private void analyzeMinimizedEdge(IMinimizedEdge edge) {
		if (edge.isBasicEdge()) {
			return;
		}
		if (edge instanceof ConjunctionEdge) {
			// check the sequential merge
			final ConjunctionEdge conjunction = (ConjunctionEdge) edge;
			assertTrue(conjunction.getCompositeEdges().length == 2);
			final IMinimizedEdge left = conjunction.getCompositeEdges()[0];
			final IMinimizedEdge right = conjunction.getCompositeEdges()[1];
			assertEquals(left.getTarget(), right.getSource());
			assertEquals(left.getTarget().getOriginalNode(), right.getSource()
					.getOriginalNode());
			final MinimizedNode inspectNode = left.getTarget();
			assertTrue(inspectNode.getOutgoingEdges().size() == 1);
			assertTrue(inspectNode.getIncomingEdges().size() == 1);
			assertEquals(left, inspectNode.getIncomingEdges().get(0));
			assertEquals(right, inspectNode.getOutgoingEdges().get(0));
			analyzeMinimizedEdge(left);
			analyzeMinimizedEdge(right);
			return;
		}
		if (edge instanceof DisjunctionEdge) {
			// check the parallel merge
			final DisjunctionEdge disjunction = (DisjunctionEdge) edge;
			assertTrue(disjunction.getCompositeEdges().length == 2);
			final IMinimizedEdge left = disjunction.getCompositeEdges()[0];
			final IMinimizedEdge right = disjunction.getCompositeEdges()[1];
			assertEquals(left.getSource(), right.getSource());
			assertEquals(left.getTarget(), right.getTarget());
			final MinimizedNode source = left.getSource();
			final MinimizedNode target = left.getTarget();
			assertEquals(disjunction.getSource(), source);
			assertEquals(disjunction.getTarget(), target);
			analyzeMinimizedEdge(left);
			analyzeMinimizedEdge(right);
			return;
		}
		throw new IllegalStateException("Edge is not Composite or"
				+ " Basic, should not happen!");
	}
}
