/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
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
package de.uni_freiburg.informatik.ultimate.blockencoding.algorithm;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.visitor.TestMinimizationVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.BlockEncodingAnnotation;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.RatingFactory.RatingStrategy;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.util.EncodingStatistics;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * This Class is the base class for the minimization algorithm. <br>
 * He starts the minimization on a RootNode, which is the input of this class. <br>
 * On this RootNode, the minimization is applied. This is done with the single Minimization Visitors.
 *
 * @author Stefan Wissert
 *
 */
public class BlockEncoder {

	private final ILogger mLogger;

	private MinimizeBranchVisitor mbVisitor;

	private MinimizeLoopVisitor mlVisitor;

	private TestMinimizationVisitor tmVisitor;

	private MinimizeCallReturnVisitor mcrVisitor;

	private boolean shouldMinimizeCallReturn;

	private ArrayList<MinimizedNode> nonCallingFunctions;

	private final IUltimateServiceProvider mServices;

	public BlockEncoder(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
	}

	/**
	 * Public method to start the minimization.
	 *
	 * @param root
	 *            the RootNode of the input RCFG
	 * @return the minimized CFG
	 */
	public RootNode startMinimization(final RootNode root) {
		mLogger.info("Start BlockEncoding on RCFG");
		// initialize the statistics
		EncodingStatistics.init();
		// We need to know, which rating strategy should be chosen
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		RatingFactory.getInstance()
				.setRatingStrategy(prefs.getEnum(PreferenceInitializer.LABEL_STRATEGY, RatingStrategy.class));
		shouldMinimizeCallReturn = prefs.getBoolean(PreferenceInitializer.LABEL_CALLMINIMIZE);

		// Initialize the Visitors, which apply the minimization rules
		mbVisitor = new MinimizeBranchVisitor(mLogger);
		mlVisitor = new MinimizeLoopVisitor(mLogger, mServices);
		mcrVisitor = new MinimizeCallReturnVisitor(mLogger, mbVisitor);
		tmVisitor = new TestMinimizationVisitor(mLogger);

		nonCallingFunctions = new ArrayList<>();

		for (final IcfgEdge edge : root.getOutgoingEdges()) {
			if (edge instanceof RootEdge) {
				final RootEdge rootEdge = (RootEdge) edge;
				if (rootEdge.getTarget() instanceof BoogieIcfgLocation) {
					processFunction((BoogieIcfgLocation) rootEdge.getTarget(), rootEdge);
				} else {
					mLogger.warn("Minimization canceled, illegal RCFG!");
					throw new IllegalArgumentException("Node is no ProgramPoint, illegal RCFG");
				}
			} else {
				mLogger.warn("Minimization canceled, illegal RCFG!");
				throw new IllegalArgumentException("An outgoing edge of RootNode is not a RootEdge");
			}
		}
		// Since we merged some Call- and Return-Edges we need to execute
		// mbVisitor again
		// Now it is configurable if this minimization should be done!
		if (shouldMinimizeCallReturn) {
			for (final MinimizedNode node : nonCallingFunctions) {
				mlVisitor.visitNode(node);
			}
			// Since it is possible to merge methods in different steps, we have
			// to handle this. Therefore we made up a list where the
			// MinimizeCallReturnVisitor tells us which nodes we have to inspect
			// again!
			final ArrayList<MinimizedNode> methodNodes = new ArrayList<>();
			for (final IcfgEdge edge : root.getOutgoingEdges()) {
				if (edge instanceof RootEdge) {
					methodNodes.add(BlockEncodingAnnotation.getAnnotation(edge).getNode());
				}
			}
			// Now we start processing the method nodes, first step is to
			// replace the call and return edges with substitutions
			do {
				for (final MinimizedNode node : methodNodes) {
					mLogger.debug("Try to merge Call- and Return-Edges for the Method: " + node);
					mcrVisitor.visitNode(node);
				}
				methodNodes.clear();
				methodNodes.addAll(mcrVisitor.getNodesForReVisit());
				// clear the nodes found by the mcrVisitor
				mcrVisitor.getNodesForReVisit().clear();
				// Here try to minimize the rest of the CFG, so that maybe a
				// further minimization is possible in the next run
				for (final IcfgEdge edge : root.getOutgoingEdges()) {
					if (edge instanceof RootEdge) {
						mbVisitor.visitNode(BlockEncodingAnnotation.getAnnotation(edge).getNode());
					}
				}
				for (final IcfgEdge edge : root.getOutgoingEdges()) {
					if (edge instanceof RootEdge) {
						mlVisitor.visitNode(BlockEncodingAnnotation.getAnnotation(edge).getNode());
						tmVisitor.visitNode(BlockEncodingAnnotation.getAnnotation(edge).getNode());
					}
				}
			} while (!methodNodes.isEmpty());
		}
		// print collected statistics
		mLogger.info("---- Collected Statistics ----");
		mLogger.info("Amount of basic edges: " + EncodingStatistics.countOfBasicEdges);
		mLogger.info("Amount of created disjunctions: " + EncodingStatistics.countOfDisjunctions);
		mLogger.info("Max. amount of disjunctions in one edge: " + EncodingStatistics.maxDisjunctionsInOneEdge);
		mLogger.info("Max. different variables in one edge: " + EncodingStatistics.maxDiffVariablesInOneEdge);
		mLogger.info("Min. different variables in one edge: " + EncodingStatistics.minDiffVariablesInOneEdge);
		return root;
	}

	/**
	 * This method processes the CFG of a single function. Basically the functions are independent from each other.
	 *
	 * @param methodEntryNode
	 *            the entry point of a function
	 */
	private void processFunction(final BoogieIcfgLocation methodEntryNode, final RootEdge rootEdge) {
		mLogger.info("Start processing function: " + methodEntryNode.getProcedure());
		// Remark: While doing the initialization of the min model, we probably
		// create already a method entry node
		MinimizedNode node = mbVisitor.getReferencedMethodEntryNode(methodEntryNode);
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
		BlockEncodingAnnotation.addAnnotation(rootEdge, new BlockEncodingAnnotation(node));
	}
}
