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
package de.uni_freiburg.informatik.ultimate.blockencoding.test.unit;

import java.util.ArrayList;
import java.util.HashSet;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.PrintEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.BasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
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
import junit.framework.TestCase;

/**
 * The purpose of this class, is to test the initialization of the Minimized
 * Model, which is done in the AbstractMinimizationVisitor. There we iterate
 * over an RCFG (Note: the first node have to be converted). Since we can not
 * access the methods in the abstract class, we use the child-class:
 * PrintEdgesVisitor.
 * 
 * @author Stefan Wissert
 * 
 */
public class TestAbstractMinimizationVisitor extends TestCase {

	/**
	 * the object under test.
	 */
	private PrintEdgeVisitor mRcfgVisitor;

	/**
	 * Base node of the RCFG to test.
	 */
	private IcfgLocation mRcfgNode;

	private ILogger mLogger;

	private HashSet<IcfgLocation> mVisitedOrigNodes;

	private HashSet<MinimizedNode> mVisitedMinNodes;


	@Override
	@Before
	protected void setUp() throws Exception {
		mRcfgNode = RCFGStore.getRCFG();
		mLogger = ExecuteUnitTestObserver.getLogger();
		mRcfgVisitor = new PrintEdgeVisitor(mLogger);
		mVisitedOrigNodes = new HashSet<IcfgLocation>();
		mVisitedMinNodes = new HashSet<MinimizedNode>();
		// output the start node
		final RootNode rootNode = (RootNode) mRcfgNode;
		String fileName = "";
		for (final String key : rootNode.getRootAnnot().getEntryNodes().keySet()) {
			if (!key.equals("ULTIMATE.init") && !key.equals("ULTIMATE.start")) {
				fileName = rootNode.getRootAnnot().getEntryNodes().get(key)
						.getPayload().getLocation().getFileName();
				break;
			}
		}
		mLogger.error("Start Test on File: " + fileName);
	}

	@Test
	public void testInitializationForGivenRCFG() {
		mLogger.info("Start Testing the intialization of MinModel");
		assertTrue(mRcfgNode instanceof RootNode);
		for (final IcfgEdge edge : mRcfgNode.getOutgoingEdges()) {
			assertTrue(edge instanceof RootEdge);
			assertTrue(edge.getTarget() instanceof BoogieIcfgLocation);
			final BoogieIcfgLocation methodEntryNode = (BoogieIcfgLocation) edge.getTarget();
			final MinimizedNode minEntryNode = new MinimizedNode(methodEntryNode);
			assertEquals(minEntryNode.getOriginalNode(), methodEntryNode);
			assertNull(minEntryNode.getOutgoingEdges());
			assertNull(minEntryNode.getIncomingEdges());
			// run the visitor which initializes the model
			mRcfgVisitor.visitNode(minEntryNode);
			assertNotNull(minEntryNode.getOutgoingEdges());
			assertNotNull(minEntryNode.getIncomingEdges());
			// now we compare the original and the initialized graph
			compareOriginalAndMinimizedGraph(methodEntryNode, minEntryNode);
		}
	}

	private void compareOriginalAndMinimizedGraph(final BoogieIcfgLocation originalNode,
			final MinimizedNode minNode) {
		if (mVisitedMinNodes.contains(minNode)
				&& mVisitedOrigNodes.contains(originalNode)) {
			return;
		}
		assertEquals(minNode.getOriginalNode(), originalNode);
		final ArrayList<MinimizedNode> minNodeList = new ArrayList<MinimizedNode>();
		final ArrayList<BoogieIcfgLocation> origNodeList = new ArrayList<BoogieIcfgLocation>();
		for (int i = 0; i < minNode.getOutgoingEdges().size(); i++) {
			final IMinimizedEdge minEdge = minNode.getOutgoingEdges().get(i);
			assertTrue(minEdge.isBasicEdge());
			final IcfgEdge originalEdge = originalNode.getOutgoingEdges().get(i);
			assertEquals(((BasicEdge) minEdge).getOriginalEdge(), originalEdge);
			assertTrue(originalEdge.getTarget() instanceof BoogieIcfgLocation);
			if (originalEdge instanceof Call || originalEdge instanceof Return) {
				minNodeList.add(minEdge.getTarget());
				origNodeList.add((BoogieIcfgLocation) originalEdge.getTarget());
			}
		}
		for (int i = 0; i < minNodeList.size(); i++) {
			compareOriginalAndMinimizedGraph(origNodeList.get(i),
					minNodeList.get(i));
			mVisitedMinNodes.add(minNodeList.get(i));
			mVisitedOrigNodes.add(origNodeList.get(i));
		}
	}

}
