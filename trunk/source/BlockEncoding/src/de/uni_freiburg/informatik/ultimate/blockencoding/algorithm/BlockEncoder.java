/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.algorithm;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.BlockEncodingAnnotation;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.test.TestMinimizationVisitor;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockendcoding.preferences.PreferencePage;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * This Class is the base class for the minimization algorithm. <br>
 * He starts the minimization on a RootNode, which is the input of this class. <br>
 * On this RootNode, the minimization is applied. This is done with the single
 * Minimization Visitors.
 * 
 * @author Stefan Wissert
 * 
 */
public class BlockEncoder {

	/**
	 * Shared Ultimate Logger instance.
	 */
	private static Logger s_Logger;

	private MinimizeBranchVisitor mbVisitor;

	private MinimizeLoopVisitor mlVisitor;

	private TestMinimizationVisitor tmVisitor;

	private MinimizeCallReturnVisitor mcrVisitor;

	public BlockEncoder() {
		s_Logger = UltimateServices.getInstance().getLogger(
				Activator.s_PLUGIN_ID);
	}

	/**
	 * Public method to start the minimization.
	 * 
	 * @param root
	 *            the RootNode of the input RCFG
	 * @return the minimized CFG
	 */
	public RootNode startMinimization(RootNode root) {
		s_Logger.info("Start BlockEncoding on RCFG");
		// Initialize the Visitors, which apply the minimization rules
		mbVisitor = new MinimizeBranchVisitor();
		mlVisitor = new MinimizeLoopVisitor();
		mcrVisitor = new MinimizeCallReturnVisitor();
		// TODO this only for validating purposes
		tmVisitor = new TestMinimizationVisitor();

		for (RCFGEdge edge : root.getOutgoingEdges()) {
			if (edge instanceof RootEdge) {
				RootEdge rootEdge = (RootEdge) edge;
				if (rootEdge.getTarget() instanceof ProgramPoint) {
					processFunction((ProgramPoint) rootEdge.getTarget(),
							rootEdge);
				} else {
					s_Logger.warn("Minimization canceled, illegal RCFG!");
					throw new IllegalArgumentException(
							"Node is no ProgramPoint, illegal RCFG");
				}
			} else {
				s_Logger.warn("Minimization canceled, illegal RCFG!");
				throw new IllegalArgumentException(
						"An outgoing edge of RootNode is not a RootEdge");
			}
		}
		// Since we merged some Call- and Return-Edges we need to execute
		// mbVisitor again
		// FIXME: it seems to work, but Call, Summary and Return-Edges can not
		// be part of some Sequential or parallel composition
		// Now it is configurable if this minimization should be done!
		IEclipsePreferences prefs = ConfigurationScope.INSTANCE
				.getNode(Activator.s_PLUGIN_ID);
		if (prefs.getBoolean(PreferencePage.NAME_CALLMINIMIZE, false)) {
			for (RCFGEdge edge : root.getOutgoingEdges()) {
				if (edge instanceof RootEdge) {
					s_Logger.debug("Try to merge Call- and Return-Edges for the Method: "
							+ edge.getTarget());
					mcrVisitor.visitNode(BlockEncodingAnnotation.getAnnotation(
							(RootEdge) edge).getNode());
				}
			}
			for (RCFGEdge edge : root.getOutgoingEdges()) {
				if (edge instanceof RootEdge) {
					mlVisitor.visitNode(BlockEncodingAnnotation.getAnnotation(
							(RootEdge) edge).getNode());
					tmVisitor.visitNode(BlockEncodingAnnotation.getAnnotation(
							(RootEdge) edge).getNode());
				}
			}
		}
		return root;
	}

	/**
	 * This method processes the CFG of a single function. Basically the
	 * functions are independent from each other.
	 * 
	 * @param methodEntryNode
	 *            the entry point of a function
	 */
	private void processFunction(ProgramPoint methodEntryNode, RootEdge rootEdge) {
		s_Logger.info("Start processing function: "
				+ methodEntryNode.getProcedure());
		// Remark: While doing the initialization of the min model, we probably
		// create already a method entry node
		MinimizedNode node = mbVisitor
				.getReferencedMethodEntryNode(methodEntryNode);
		if (node == null) {
			node = new MinimizedNode(methodEntryNode);
		}
		// First we minimize all sequential and all branches
		// In order to do this we use MinimizeBranchVisitor
		mbVisitor.visitNode(node);
		// Now it is possible to have nodes with one incoming and two outgoing
		// edges, which can be merged however
		// To minimize such edges we use the MinimizeLoopVisitor (which is a
		// subclass of MinimizeBranchVisitor)
		// ---> internally it executes also the rules form mbVisitor
		mlVisitor.visitNode(node);
		// Validate the minimization (TODO maybe only for testing)
		tmVisitor.visitNode(node);
		BlockEncodingAnnotation.addAnnotation(rootEdge,
				new BlockEncodingAnnotation(node));
	}
}