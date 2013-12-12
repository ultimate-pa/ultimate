/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.test.unit;

import java.util.HashSet;

import org.apache.log4j.Logger;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.MinimizeBranchVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.ConjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.test.util.RCFGStore;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
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
	private RCFGNode rcfgNode;

	private Logger logger;

	private HashSet<IMinimizedEdge> visitedEdges;

	/*
	 * (non-Javadoc)
	 * 
	 * @see junit.framework.TestCase#setUp()
	 */
	@Override
	protected void setUp() throws Exception {
		rcfgNode = RCFGStore.getRCFG();
		logger = UltimateServices.getInstance()
				.getLogger(Activator.s_PLUGIN_ID);
		mbv = new MinimizeBranchVisitor(logger);
		visitedEdges = new HashSet<IMinimizedEdge>();
	}

	@Test
	public void testBasicMinimizationOfRCFG() {
		// Since we not directly minimize the root node, we have to iterate
		// first over the RootEdges
		assertTrue(rcfgNode instanceof RootNode);
		assertNotNull(rcfgNode.getOutgoingEdges());
		for (RCFGEdge edge : rcfgNode.getOutgoingEdges()) {
			assertTrue(edge instanceof RootEdge);
			assertTrue(edge.getTarget() instanceof ProgramPoint);
			testMinimizationOfFunction((ProgramPoint) edge.getTarget());
		}
	}

	private void testMinimizationOfFunction(ProgramPoint entryPoint) {
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
		for (IMinimizedEdge edge : node.getOutgoingEdges()) {
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
					IMinimizedEdge minEdge = edge.getTarget()
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
			for (IMinimizedEdge checkEdge : edge.getSource().getOutgoingEdges()) {
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
			ConjunctionEdge conjunction = (ConjunctionEdge) edge;
			assertTrue(conjunction.getCompositeEdges().length == 2);
			IMinimizedEdge left = conjunction.getCompositeEdges()[0];
			IMinimizedEdge right = conjunction.getCompositeEdges()[1];
			assertEquals(left.getTarget(), right.getSource());
			assertEquals(left.getTarget().getOriginalNode(), right.getSource()
					.getOriginalNode());
			MinimizedNode inspectNode = left.getTarget();
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
			DisjunctionEdge disjunction = (DisjunctionEdge) edge;
			assertTrue(disjunction.getCompositeEdges().length == 2);
			IMinimizedEdge left = disjunction.getCompositeEdges()[0];
			IMinimizedEdge right = disjunction.getCompositeEdges()[1];
			assertEquals(left.getSource(), right.getSource());
			assertEquals(left.getTarget(), right.getTarget());
			MinimizedNode source = left.getSource();
			MinimizedNode target = left.getTarget();
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
