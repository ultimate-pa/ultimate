/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.test.unit;

import java.util.HashSet;

import junit.framework.TestCase;

import org.apache.log4j.Logger;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.PrintEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.converter.MinModelConverter;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.BlockEncodingAnnotation;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.test.ExecuteUnitTestObserver;
import de.uni_freiburg.informatik.ultimate.blockencoding.test.util.RCFGStore;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

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

	private RCFGNode rcfgNode;

	private Logger logger;
	
	private HashSet<RCFGEdge> visitedEdges;

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
		visitedEdges = new HashSet<RCFGEdge>();
	}

	@Test
	public void testMinModelConversion() {
		// First we need to create a MinModel therefore we use the
		// PrintEdgesVisitor, which does no minimization but initializes the
		// model
		assertTrue(rcfgNode instanceof RootNode);
		assertNotNull(rcfgNode.getOutgoingEdges());
		for (RCFGEdge edge : rcfgNode.getOutgoingEdges()) {
			assertTrue(edge instanceof RootEdge);
			assertTrue(edge.getTarget() instanceof ProgramPoint);
			ProgramPoint methodEntryPoint = (ProgramPoint) edge.getTarget();
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
		RootNode convRoot = minModelConverter
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
			assertTrue(origRoot.getOutgoingEdges().get(i).getTarget() instanceof ProgramPoint);
			ProgramPoint oFuncEntry = (ProgramPoint) origRoot
					.getOutgoingEdges().get(i).getTarget();
			assertTrue(convRoot.getOutgoingEdges().get(i).getTarget() instanceof ProgramPoint);
			ProgramPoint cFuncEntry = (ProgramPoint) convRoot
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
	private void visitRCFGFunction(ProgramPoint oNode, ProgramPoint cNode) {
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
			RCFGEdge oEdge = oNode.getOutgoingEdges().get(i);
			RCFGEdge cEdge = cNode.getOutgoingEdges().get(i);
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
			assertTrue(oEdge.getTarget() instanceof ProgramPoint);
			assertTrue(cEdge.getTarget() instanceof ProgramPoint);
			visitRCFGFunction((ProgramPoint) oEdge.getTarget(),
					(ProgramPoint) cEdge.getTarget());
		}
	}

}
