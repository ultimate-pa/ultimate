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

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.PrintEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.converter.MinModelConverter;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.BlockEncodingAnnotation;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
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
 * After the first step of BlockEncoding we have a new model, which have to be
 * converted at the end of the process. So that the model checker can work, with
 * the known RCFG-structure. <br>
 * In order to test this, we take the original RCFG an convert it into the
 * minimized model, but we do not minimize the graph. So after the conversion
 * the original and the new graph should look the same.
 * 
 * @author Stefan Wissert
 * 
 */
public class TestMinModelConversion extends TestCase {

	/**
	 * Object under test.
	 */
	private MinModelConverter minModelConverter;

	/**
	 * Is needed to create a Minimized Model
	 */
	private PrintEdgeVisitor printEdgeVisitor;

	private IcfgLocation rcfgNode;

	private ILogger logger;
	
	private HashSet<IcfgEdge> visitedEdges;

	/*
	 * (non-Javadoc)
	 * 
	 * @see junit.framework.TestCase#setUp()
	 */
	@Override
	protected void setUp() throws Exception {
		rcfgNode = RCFGStore.getRCFG();
		minModelConverter = new MinModelConverter(ExecuteUnitTestObserver.getServices());
		printEdgeVisitor = new PrintEdgeVisitor(ExecuteUnitTestObserver.getLogger());
		visitedEdges = new HashSet<IcfgEdge>();
	}

	@Test
	public void testMinModelConversion() {
		// First we need to create a MinModel therefore we use the
		// PrintEdgesVisitor, which does no minimization but initializes the
		// model
		assertTrue(rcfgNode instanceof RootNode);
		assertNotNull(rcfgNode.getOutgoingEdges());
		for (final IcfgEdge edge : rcfgNode.getOutgoingEdges()) {
			assertTrue(edge instanceof RootEdge);
			assertTrue(edge.getTarget() instanceof BoogieIcfgLocation);
			final BoogieIcfgLocation methodEntryPoint = (BoogieIcfgLocation) edge.getTarget();
			assertNotNull(methodEntryPoint.getIncomingEdges());
			// It can happen that while minimizing we already created an
			// Min.Node we have to use here
			MinimizedNode minEntryPoint = printEdgeVisitor
					.getReferencedMethodEntryNode(methodEntryPoint);
			// Probably it can be null
			if (minEntryPoint == null) {
				minEntryPoint = new MinimizedNode(methodEntryPoint);
			}
			// the object mapping should be the same
			assertEquals(minEntryPoint.getOriginalNode(), methodEntryPoint);
			// Now we execute the visitor to initialize the model
			printEdgeVisitor.visitNode(minEntryPoint);
			BlockEncodingAnnotation.addAnnotation(edge,
					new BlockEncodingAnnotation(minEntryPoint));
		}
		// Now the minimized model is initialized, so we can perform the
		// conversion with the MinModelConverter
		final RootNode convRoot = minModelConverter
				.startConversion((RootNode) rcfgNode);
		// now we compare the original and the converted one, it should be
		// exactly the same (semantically)!
		compareRCFGs((RootNode) rcfgNode, convRoot);
	}

	/**
	 * In this method we compare the both RootNodes of the RCFGs.
	 * 
	 * @param origRoot
	 *            RootNode of the original RCFG
	 * @param convRoot
	 *            RootNode of the converted RCFG
	 */
	private void compareRCFGs(RootNode origRoot, RootNode convRoot) {
		assertEquals(origRoot.getOutgoingEdges().size(), convRoot
				.getOutgoingEdges().size());
		// We iterate over the outgoing edges of the corresponding root nodes
		for (int i = 0; i < origRoot.getOutgoingEdges().size(); i++) {
			assertTrue(origRoot.getOutgoingEdges().get(i).getTarget() instanceof BoogieIcfgLocation);
			final BoogieIcfgLocation oFuncEntry = (BoogieIcfgLocation) origRoot
					.getOutgoingEdges().get(i).getTarget();
			assertTrue(convRoot.getOutgoingEdges().get(i).getTarget() instanceof BoogieIcfgLocation);
			final BoogieIcfgLocation cFuncEntry = (BoogieIcfgLocation) convRoot
					.getOutgoingEdges().get(i).getTarget();
			// we can do a check with equals, since this is overwritten
			assertEquals(oFuncEntry, cFuncEntry);
			visitRCFGFunction(oFuncEntry, cFuncEntry);
		}
	}

	/**
	 * @param oNode
	 *            the original Node
	 * @param cNode
	 *            the converted Node
	 */
	private void visitRCFGFunction(BoogieIcfgLocation oNode, BoogieIcfgLocation cNode) {
		assertEquals(oNode, cNode);
		logger.debug("UNIT-TEST: " + oNode + " - " + cNode);
		logger.debug("OUT-Edges O: " + oNode.getOutgoingEdges());
		logger.debug("OUT_Edges C: " + cNode.getOutgoingEdges());
		assertEquals(oNode.getOutgoingEdges().size(), cNode.getOutgoingEdges()
				.size());
		// End of Recursion
		if (oNode.getOutgoingEdges().size() == 0) {
			return;
		}
		for (int i = 0; i < oNode.getOutgoingEdges().size(); i++) {
			final IcfgEdge oEdge = oNode.getOutgoingEdges().get(i);
			final IcfgEdge cEdge = cNode.getOutgoingEdges().get(i);
			// if already visited the edges, we stop...
			if (visitedEdges.contains(oEdge)) {
				assertTrue(visitedEdges.contains(cEdge));
				continue;
			}
			visitedEdges.add(oEdge);
			visitedEdges.add(cEdge);
			// We do not follow Call-Edges
			if (oEdge instanceof Call) {
				assertTrue(cEdge instanceof Call);
				continue;
			}
			// ... and also not Return-Edges
			if (oEdge instanceof Return) {
				assertTrue(oEdge instanceof Return);
				continue;
			}
			assertTrue(oEdge.getTarget() instanceof BoogieIcfgLocation);
			assertTrue(cEdge.getTarget() instanceof BoogieIcfgLocation);
			visitRCFGFunction((BoogieIcfgLocation) oEdge.getTarget(),
					(BoogieIcfgLocation) cEdge.getTarget());
		}
	}

}
