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
import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.MinimizeCallReturnVisitor;
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
import junit.framework.TestCase;

/**
 * With this visitor we test the minimization of Call- and Return-Edges, a
 * condition for this is a successful run of the MinimizeBranchVisitor and the
 * MinimizeLoopVisitor.
 * 
 * @author Stefan Wissert
 * 
 */
public class TestMinimizeCallReturnVisitor extends TestCase {

	/**
	 * the object under test.
	 */
	private MinimizeCallReturnVisitor mcrv;

	private MinimizeBranchVisitor mbv;

	private MinimizeLoopVisitor mlv;

	private IcfgLocation rcfgNode;

	private ILogger logger;
	
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
		mcrv = new MinimizeCallReturnVisitor(logger, mbv);
	}

	@Test
	public void testMinimizationCallReturn() {
		// Since we not directly minimize the root node, we have to iterate
		// first over the RootEdges
		assertTrue(rcfgNode instanceof RootNode);
		assertNotNull(rcfgNode.getOutgoingEdges());
		final ArrayList<MinimizedNode> functionHeader = new ArrayList<MinimizedNode>();
		for (final IcfgEdge edge : rcfgNode.getOutgoingEdges()) {
			assertTrue(edge instanceof RootEdge);
			assertTrue(edge.getTarget() instanceof BoogieIcfgLocation);
			functionHeader.add(minimizeSingleFunction((BoogieIcfgLocation) edge
					.getTarget()));
		}
		// now the basic RCFG is minimized, but Call- and Return-Edges are still
		// present in the graph
		final ArrayList<IMinimizedEdge> callEdges = new ArrayList<IMinimizedEdge>();
		for (final MinimizedNode functionHead : functionHeader) {
			assertNotNull(functionHead.getIncomingEdges());
			// We search for incoming "Call"-Edges!
			for (final IMinimizedEdge inEdge : functionHead.getIncomingEdges()) {
				if (inEdge.isBasicEdge()
						&& ((IBasicEdge) inEdge).getOriginalEdge() instanceof Call) {
					// We found a call edge, which we store in a global list
					callEdges.add(inEdge);
				}
			}
		}
		// Now we check which of our collected Call-Edges can be minimized
		final HashSet<IMinimizedEdge> minimizableCallEdges = new HashSet<IMinimizedEdge>();
		for (final IMinimizedEdge callEdge : callEdges) {
			if (checkCallReturnMinimization(callEdge)) {
				minimizableCallEdges.add(callEdge);
			}
		}
		// now we execute the Call-Return Minimization Visitor
		for (final MinimizedNode functionHead : functionHeader) {
			mcrv.visitNode(functionHead);
		}
		// so every Call-Return edge which can be minimized is now minimized
		// Now we perform checks
		for (final MinimizedNode functionHead : functionHeader) {
			assertNotNull(functionHead.getIncomingEdges());
			for (final IMinimizedEdge inEdge : functionHead.getIncomingEdges()) {
				if (inEdge.isBasicEdge()
						&& ((IBasicEdge) inEdge).getOriginalEdge() instanceof Call) {
					assertFalse(minimizableCallEdges.contains(inEdge));
					assertFalse(checkCallReturnMinimization(inEdge));
				}
			}
		}
	}

	/**
	 * Does the complete minimization process, so executing all the other
	 * visitors
	 * 
	 * @param target
	 */
	private MinimizedNode minimizeSingleFunction(BoogieIcfgLocation methodEntryPoint) {
		assertNotNull(methodEntryPoint.getIncomingEdges());
		// It can happen that while minimizing we already created an Min.Node we
		// have to use here
		MinimizedNode minEntryPoint = mbv
				.getReferencedMethodEntryNode(methodEntryPoint);
		// Probably it can be null
		if (minEntryPoint == null) {
			minEntryPoint = new MinimizedNode(methodEntryPoint);
		}
		// the object mapping should be the same
		assertEquals(minEntryPoint.getOriginalNode(), methodEntryPoint);
		// Since we already tested that the initialization is right, we now
		// execute the minimization and compare the result with the original
		// RCFG
		mbv.visitNode(minEntryPoint);
		// After the basic minimization, we execute the loop minimization, which
		// we already tested, after that we can test the Call-Return
		// minimization
		mlv.visitNode(minEntryPoint);
		return minEntryPoint;
	}

	/**
	 * is it possible to minimize these callEdge?
	 * 
	 * @param callEdge
	 * @return
	 */
	private boolean checkCallReturnMinimization(IMinimizedEdge callEdge) {
		// we check the outgoing edges of the callEdge.getTarget
		assertTrue(callEdge.isBasicEdge());
		assertTrue(((IBasicEdge) callEdge).getOriginalEdge() instanceof Call);
		assertNotNull(callEdge.getTarget().getOutgoingEdges());
		final ArrayList<MinimizedNode> errorLocs = new ArrayList<MinimizedNode>();
		final ArrayList<MinimizedNode> targetLocs = new ArrayList<MinimizedNode>();
		for (final IMinimizedEdge edge : callEdge.getTarget().getOutgoingEdges()) {
			if (edge.isOldVarInvolved()) {
				return false;
			}
			if (edge.getTarget().getOriginalNode().isErrorLocation()) {
				errorLocs.add(edge.getTarget());
			} else {
				targetLocs.add(edge.getTarget());
			}
		}
		if ((errorLocs.size() + targetLocs.size()) == callEdge.getTarget()
				.getOutgoingEdges().size()) {
			if (targetLocs.size() == 1) {
				// now we have to inspect the targetLoc[0].getTarget if there
				// are
				// only Return-Edges, than it is possible to minimize it
				for (final IMinimizedEdge possibleReturnEdge : targetLocs.get(0)
						.getOutgoingEdges()) {
					if (!possibleReturnEdge.isBasicEdge()) {
						return false;
					}
					final IBasicEdge basicEdge = (IBasicEdge) possibleReturnEdge;
					if (!(basicEdge.getOriginalEdge() instanceof Return)) {
						return false;
					}
				}
				return true;
			}
		}
		return false;
	}
}
