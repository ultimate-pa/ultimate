/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.algorithm;

import java.util.ArrayList;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.BlockEncodingAnnotation;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.RatingFactory;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.util.EncodingStatistics;
import de.uni_freiburg.informatik.ultimate.blockencoding.test.visitor.TestMinimizationVisitor;
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

	private boolean shouldMinimizeCallReturn;

	private ArrayList<MinimizedNode> nonCallingFunctions;

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
		// initialize the statistics
		EncodingStatistics.init();
		// We need to know, which rating strategy should be chosen
		IEclipsePreferences prefs = ConfigurationScope.INSTANCE
				.getNode(Activator.s_PLUGIN_ID);
		RatingFactory.getInstance().setRatingStrategy(
				prefs.get(PreferencePage.NAME_STRATEGY, "0"));
		shouldMinimizeCallReturn = prefs.getBoolean(
				PreferencePage.NAME_CALLMINIMIZE, false);
		// Initialize the Visitors, which apply the minimization rules
		mbVisitor = new MinimizeBranchVisitor(s_Logger);
		mlVisitor = new MinimizeLoopVisitor(s_Logger);
		mcrVisitor = new MinimizeCallReturnVisitor(s_Logger, mbVisitor);
		tmVisitor = new TestMinimizationVisitor(s_Logger);

		nonCallingFunctions = new ArrayList<MinimizedNode>();

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
		// Now it is configurable if this minimization should be done!
		if (shouldMinimizeCallReturn) {
			for (MinimizedNode node : nonCallingFunctions) {
				mlVisitor.visitNode(node);
			}
			// Since it is possible to merge methods in different steps, we have
			// to handle this. Therefore we made up a list where the
			// MinimizeCallReturnVisitor tells us which nodes we have to inspect
			// again!
			ArrayList<MinimizedNode> methodNodes = new ArrayList<MinimizedNode>();
			for (RCFGEdge edge : root.getOutgoingEdges()) {
				if (edge instanceof RootEdge) {
					methodNodes.add(BlockEncodingAnnotation.getAnnotation(
							(RootEdge) edge).getNode());
				}
			}
			// Now we start processing the method nodes, first step is to
			// replace the call and return edges with substitutions
			do {
				for (MinimizedNode node : methodNodes) {
					s_Logger.debug("Try to merge Call- and Return-Edges for the Method: "
							+ node);
					mcrVisitor.visitNode(node);
				}
				methodNodes.clear();
				methodNodes.addAll(mcrVisitor.getNodesForReVisit());
				// clear the nodes found by the mcrVisitor
				mcrVisitor.getNodesForReVisit().clear();
				// Here try to minimize the rest of the CFG, so that maybe a
				// further minimization is possible in the next run
				for (RCFGEdge edge : root.getOutgoingEdges()) {
					if (edge instanceof RootEdge) {
						mbVisitor.visitNode(BlockEncodingAnnotation
								.getAnnotation((RootEdge) edge).getNode());
					}
				}
				for (RCFGEdge edge : root.getOutgoingEdges()) {
					if (edge instanceof RootEdge) {
						mlVisitor.visitNode(BlockEncodingAnnotation
								.getAnnotation((RootEdge) edge).getNode());
						tmVisitor.visitNode(BlockEncodingAnnotation
								.getAnnotation((RootEdge) edge).getNode());
					}
				}
			} while (!methodNodes.isEmpty());
		}
		// print collected statistics
		s_Logger.info("---- Collected Statistics ----");
		s_Logger.info("Amount of basic edges: "
				+ EncodingStatistics.countOfBasicEdges);
		s_Logger.info("Amount of created disjunctions: "
				+ EncodingStatistics.countOfDisjunctions);
		s_Logger.info("Max. amount of disjunctions in one edge: "
				+ EncodingStatistics.maxDisjunctionsInOneEdge);
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
		if (!shouldMinimizeCallReturn) {
			// if we do not want to minimize call and return edges, we do this
			// minimization here, if not we do not do this here because it can
			// lead to duplication of formulas
			mlVisitor.visitNode(node);
			// Validate the minimization
			tmVisitor.visitNode(node);
		} else if (!mbVisitor.isCallReturnEdgeInvolved()) {
			nonCallingFunctions.add(node);
		}
		BlockEncodingAnnotation.addAnnotation(rootEdge,
				new BlockEncodingAnnotation(node));
	}
}