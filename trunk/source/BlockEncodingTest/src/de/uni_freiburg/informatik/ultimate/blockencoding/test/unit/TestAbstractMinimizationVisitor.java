package de.uni_freiburg.informatik.ultimate.blockencoding.test.unit;

import java.util.ArrayList;
import java.util.HashSet;

import junit.framework.TestCase;

import org.apache.log4j.Logger;
import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.PrintEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.BasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
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
	private PrintEdgeVisitor rcfgVisitor;

	/**
	 * Base node of the RCFG to test.
	 */
	private RCFGNode rcfgNode;

	private Logger s_Logger;

	private HashSet<RCFGNode> visitedOrigNodes;

	private HashSet<MinimizedNode> visitedMinNodes;


	@Before
	protected void setUp() throws Exception {
		rcfgNode = RCFGStore.getRCFG();
		s_Logger = UltimateServices.getInstance().getLogger(
				Activator.s_PLUGIN_ID);
		rcfgVisitor = new PrintEdgeVisitor(s_Logger);
		visitedOrigNodes = new HashSet<RCFGNode>();
		visitedMinNodes = new HashSet<MinimizedNode>();
		// output the start node
		RootNode rootNode = (RootNode) rcfgNode;
		String fileName = "";
		for (String key : rootNode.getRootAnnot().getEntryNodes().keySet()) {
			if (key.equals("ULTIMATE.init") || key.equals("ULTIMATE.start")) {
				continue;
			}
			fileName = rootNode.getRootAnnot().getEntryNodes().get(key)
					.getPayload().getLocation().getFileName();
			break;
		}
		s_Logger.error("Start Test on File: " + fileName);
	}

	@Test
	public void testInitializationForGivenRCFG() {
		s_Logger.info("Start Testing the intialization of MinModel");
		assertTrue(rcfgNode instanceof RootNode);
		for (RCFGEdge edge : rcfgNode.getOutgoingEdges()) {
			assertTrue(edge instanceof RootEdge);
			assertTrue(edge.getTarget() instanceof ProgramPoint);
			ProgramPoint methodEntryNode = (ProgramPoint) edge.getTarget();
			MinimizedNode minEntryNode = new MinimizedNode(methodEntryNode);
			assertEquals(minEntryNode.getOriginalNode(), methodEntryNode);
			assertNull(minEntryNode.getOutgoingEdges());
			assertNull(minEntryNode.getIncomingEdges());
			// run the visitor which initializes the model
			rcfgVisitor.visitNode(minEntryNode);
			assertNotNull(minEntryNode.getOutgoingEdges());
			assertNotNull(minEntryNode.getIncomingEdges());
			// now we compare the original and the initialized graph
			compareOriginalAndMinimizedGraph(methodEntryNode, minEntryNode);
		}
	}

	private void compareOriginalAndMinimizedGraph(ProgramPoint originalNode,
			MinimizedNode minNode) {
		if (visitedMinNodes.contains(minNode)
				&& visitedOrigNodes.contains(originalNode)) {
			return;
		}
		assertEquals(minNode.getOriginalNode(), originalNode);
		ArrayList<MinimizedNode> minNodeList = new ArrayList<MinimizedNode>();
		ArrayList<ProgramPoint> origNodeList = new ArrayList<ProgramPoint>();
		for (int i = 0; i < minNode.getOutgoingEdges().size(); i++) {
			IMinimizedEdge minEdge = minNode.getOutgoingEdges().get(i);
			assertTrue(minEdge.isBasicEdge());
			RCFGEdge originalEdge = originalNode.getOutgoingEdges().get(i);
			assertEquals(((BasicEdge) minEdge).getOriginalEdge(), originalEdge);
			assertTrue(originalEdge.getTarget() instanceof ProgramPoint);
			if (originalEdge instanceof Call || originalEdge instanceof Return) {
				minNodeList.add(minEdge.getTarget());
				origNodeList.add((ProgramPoint) originalEdge.getTarget());
			}
		}
		for (int i = 0; i < minNodeList.size(); i++) {
			compareOriginalAndMinimizedGraph(origNodeList.get(i),
					minNodeList.get(i));
			visitedMinNodes.add(minNodeList.get(i));
			visitedOrigNodes.add(origNodeList.get(i));
		}
	}

}
