/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Stefan Wissert
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
package de.uni_freiburg.informatik.ultimate.blockencoding.converter;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.blockencoding.algorithm.visitor.IMinimizationVisitor;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.ConjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.DisjunctionEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.MinimizedNode;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.ShortcutErrEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IBasicEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.ICompositeEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRatingHeuristic;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.DisjunctMultiStatementRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.metrics.DisjunctVariablesRating;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.util.EncodingStatistics;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.GotoEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.TransFormulaAdder;

/**
 * This special visitor class is responsible for the conversion from MinimizedEdges and MinimizedNodes, back to
 * ProgramPoint and CodeBlock-Edges.
 *
 * @author Stefan Wissert
 *
 */
public class ConversionVisitor implements IMinimizationVisitor {

	private final ILogger mLogger;

	private BoogieIcfgLocation mStartNode;

	private final HashMap<MinimizedNode, BoogieIcfgLocation> mRefNodeMap;

	private final HashMap<BoogieIcfgLocation, BoogieIcfgLocation> mOrigToNewMap;

	private final HashMap<String, HashMap<DebugIdentifier, BoogieIcfgLocation>> mLocNodesForAnnot;

	private final HashSet<IMinimizedEdge> mVisitedEdges;

	private final Boogie2SMT mBoogie2SMT;

	private final TransFormulaAdder mTransFormBuilder;

	private final ModifiableGlobalsTable mModGlobalVarManager;

	private final HashMap<IMinimizedEdge, Integer> mCheckForMultipleFormula;

	private IRatingHeuristic mHeuristic;

	private boolean mLBE;

	private final Stack<ArrayList<CodeBlock>> mSeqComposedBlocks;

	private final HashSet<IMinimizedEdge> mHasConjunctionAsParent;

	private final IUltimateServiceProvider mServices;

	private final CodeBlockFactory mCbf;

	private final SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private final XnfConversionTechnique mXnfConversionTechnique =
			XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	/**
	 * Simplify TransFormulas of CodeBlocks
	 */
	private final boolean mSimplify;

	/**
	 * Apply an extended (more expensive) partial quantifier elimination to eliminate auxiliary variables.
	 */
	private final boolean mExtPqe = false;

	/**
	 * @param boogie2smt
	 * @param root
	 */
	public ConversionVisitor(final Boogie2SMT boogie2smt, final RootNode root, final IRatingHeuristic heuristic,
			final IUltimateServiceProvider services, final boolean simplify) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplify = simplify;
		mRefNodeMap = new HashMap<>();
		mOrigToNewMap = new HashMap<>();
		mLocNodesForAnnot = new HashMap<>();
		mVisitedEdges = new HashSet<>();
		mBoogie2SMT = boogie2smt;
		mCheckForMultipleFormula = new HashMap<>();
		mTransFormBuilder = new TransFormulaAdder(boogie2smt, mServices);
		mModGlobalVarManager = root.getRootAnnot().getCfgSmtToolkit().getModifiableGlobalsTable();
		mCbf = root.getRootAnnot().getCodeBlockFactory();
		mSeqComposedBlocks = new Stack<>();
		mHasConjunctionAsParent = new HashSet<>();
		if (heuristic == null) {
			mLBE = true;
		} else {
			mLBE = false;
			mHeuristic = heuristic;
		}
	}

	/**
	 * This method have to be called before the visitNode-Method!
	 *
	 * @param startNode
	 *            initial start point for the conversion
	 */
	public void init(final BoogieIcfgLocation startNode) {
		mStartNode = startNode;
	}

	@Override
	public void visitNode(final MinimizedNode node) {
		mVisitedEdges.clear();
		if (mStartNode == null) {
			mLogger.warn("Illegal Execution Behaviour," + "init have to be called, before visitNode()!");
			throw new IllegalStateException("No valid state that startNode == null");
		}
		if (!mRefNodeMap.containsKey(node)) {
			mRefNodeMap.put(node, mStartNode);
		}

		// Start recursion here
		internalVisitNode(node);
	}

	/**
	 * This method runs recursively over all minimized nodes, which are reachable from the initial node (function head).
	 * While doing this we convert every edge into a valid CodeBlock and every node in a ProgramPoint. In the end the
	 * whole function is translated in a RCFG.
	 *
	 * @param node
	 *            MinimizedNode to convert
	 * @param simplify
	 * @param extPqe
	 */
	private void internalVisitNode(final MinimizedNode node) {
		// We have no outgoing edges, so we reached an end of the recursion
		if (node.getOutgoingEdges() == null) {
			return;
		}
		// We now get the Edges according to the rating!
		final ArrayList<IMinimizedEdge> edgeList = getEdgesAccordingToRating(node);
		// if edgeList has no entries, we reached an end of the graph
		if (edgeList.isEmpty()) {
			return;
		}
		for (final IMinimizedEdge edge : edgeList) {
			if (!mVisitedEdges.contains(edge)) {
				mVisitedEdges.add(edge);
				// the minimized edge here has to be converted to a
				// CodeBlock-Edge
				CodeBlock cb = null;
				mCheckForMultipleFormula.clear();
				mHasConjunctionAsParent.clear();
				mSeqComposedBlocks.clear();
				mLogger.debug("New Converted Edge: " + edge + " Source: " + edge.getSource() + " / Target: "
						+ edge.getTarget());
				mLogger.debug("Size of Formula: " + edge.getElementCount());
				// Now we create a converted CodeBlock-edge
				// We add one first sequential composed list level
				mSeqComposedBlocks.push(new ArrayList<CodeBlock>());
				if (edge.getRating() instanceof DisjunctVariablesRating
						|| edge.getRating() instanceof DisjunctMultiStatementRating) {
					final Integer[] ratingValues = (Integer[]) edge.getRating().getRatingValueContainer().getValue();
					mLogger.info("Disjunctions: " + ratingValues[0] + " UsedVars: " + ratingValues[1]
							+ " ComputedValue: " + ratingValues[2]);
				}
				// add statistical information
				EncodingStatistics.addToTotalRating(edge.getRating().getRatingValueAsInteger());
				EncodingStatistics.incTotalEdges();
				// Convert IMinimizedEdge to valid RCFGEdge
				cb = convertMinimizedEdge(edge, mSimplify, mExtPqe);
				if (cb instanceof GotoEdge) {
					// it is possible that the found replacement, is Goto-Edge,
					// which we have to convert in a valid edge
					cb = replaceGotoEdge(cb, null);
				} else if (edge instanceof ShortcutErrEdge) {
					if (cb instanceof ShortcutCodeBlock) {
						cb = mCbf.constructSequentialComposition(null, null, false, false,
								Arrays.asList(((ShortcutCodeBlock) cb).getCodeBlocks()), mXnfConversionTechnique,
								mSimplificationTechnique);
					} else {
						throw new IllegalArgumentException(
								"Converted CodeBlock for ShortcutErrEdge" + " is no ShortcutCodeBlock");
					}
				}
				if (cb != null) {
					mLogger.debug("<-Converted Formula->: " + cb.getTransformula());
					cb.connectSource(getReferencedNode(edge.getSource()));
					cb.connectTarget(getReferencedNode(edge.getTarget()));
				} else {
					mLogger.debug("Formula not converted, probably due to timeout.");
				}
				// now we print out all edges which we added more than two times
				for (final Entry<IMinimizedEdge, Integer> entry : mCheckForMultipleFormula.entrySet()) {
					if (entry.getValue() < 2) {
						continue;
					}
					mLogger.error("Edge: " + entry.getKey() + " Occurence: " + entry.getValue());
				}
				// Since we convert function by function, we do not need to
				// follow Call- and Return-Edges
				if (edge.isBasicEdge() && (((IBasicEdge) edge).getOriginalEdge() instanceof Call
						|| ((IBasicEdge) edge).getOriginalEdge() instanceof Return)) {
					continue;
				}
				if (edge.getTarget() != null) {
					internalVisitNode(edge.getTarget());
				}
			}
		}
	}

	/**
	 * Here we search the the level of edges, which fulfill the rating boundary.
	 *
	 * @param node
	 *            the minimized node
	 * @return the edges which fulfill the rating boundary
	 */
	private ArrayList<IMinimizedEdge> getEdgesAccordingToRating(final MinimizedNode node) {
		// if we use LBE, we take alway the maximal minimization
		if (mLBE) {
			return new ArrayList<>(node.getMinimalOutgoingEdgeLevel());
		}
		// we iterate over the different edge levels and check the property, we
		// start with the most minimized level (which is LBE)
		for (int i = node.getOutgoingEdgeLevels().size() - 1; i >= 0; i--) {
			final SimpleEntry<IRating, List<IMinimizedEdge>> entry = node.getOutgoingEdgeLevels().get(i);
			if (entry.getKey() == null) {
				mLogger.debug("Outgoing edge level is null, should " + "only happen for ULTIMATE.start (" + node + ")");
				return new ArrayList<>();
			}
			// we check if the rated value is okay, for a certain edge level, if
			// not we can use this level
			if (mHeuristic.isRatingBoundReached(entry.getKey(), entry.getValue())) {
				return new ArrayList<>(entry.getValue());
			}
		}
		// We should never reach this state here, because there should exist at
		// least one edge level which is below the boundary!
		throw new IllegalStateException("No Outgoing-Edge-Level is below the boundary, should not happen!");
	}

	/**
	 * We put into our reference map to a minimized node a new ProgramPoint which is used later on during the
	 * conversion, and then we return it. the access on the map, should always be handled by this method.
	 *
	 * @param node
	 *            the minimized Node to convert
	 * @return the created ProgramPoint
	 */
	public BoogieIcfgLocation getReferencedNode(final MinimizedNode node) {
		if (mRefNodeMap.containsKey(node)) {
			return mRefNodeMap.get(node);
		}
		final BoogieASTNode astNode = node.getOriginalNode().getBoogieASTNode();
		final BoogieIcfgLocation newNode = new BoogieIcfgLocation(node.getOriginalNode().getDebugIdentifier(),
				node.getOriginalNode().getProcedure(), node.getOriginalNode().isErrorLocation(), astNode);
		// inserted by alex 1.11.2014: (don't forget the annotations.. (mb this would be nicer in the constructor
		// TODO
		for (final Entry<String, IAnnotations> annots : node.getOriginalNode().getPayload().getAnnotations()
				.entrySet()) {
			newNode.getPayload().getAnnotations().put(annots.getKey(), annots.getValue());
		}
		mRefNodeMap.put(node, newNode);
		// to reset the rootAnnot, we need to keep a map from the original
		// program points, to the new ones. And since we only create
		// ProgramPoints here it is the right place to store it.
		mOrigToNewMap.put(node.getOriginalNode(), newNode);
		// In addition we also have to fill the map which stores every
		// ProgramPoint in relation to its name and the procedure name
		if (mLocNodesForAnnot.containsKey(newNode.getProcedure())) {
			mLocNodesForAnnot.get(newNode.getProcedure()).put(newNode.getDebugIdentifier(), newNode);
		} else {
			final HashMap<DebugIdentifier, BoogieIcfgLocation> newMap = new HashMap<>();
			newMap.put(newNode.getDebugIdentifier(), newNode);
			mLocNodesForAnnot.put(newNode.getProcedure(), newMap);
		}
		return newNode;
	}

	/**
	 * This recursive method, converts a MinimizedEdge into a valid CodeBlock. While doing this, the method uses
	 * "Sequential" and "Parallel" Composition.
	 *
	 * @param edge
	 *            the minimized edge to convert
	 * @param simplify
	 * @param extPqe
	 * @return a converted CodeBlock
	 */
	private CodeBlock convertMinimizedEdge(final IMinimizedEdge edge, final boolean simplify, final boolean extPqe) {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			return null;
		}
		if (mCheckForMultipleFormula.containsKey(edge)) {
			mCheckForMultipleFormula.put(edge, mCheckForMultipleFormula.get(edge) + 1);
		} else {
			mCheckForMultipleFormula.put(edge, 1);
		}
		// We build a CodeBlock using Recursion
		// We reach one end if we have an BasicEdge
		if (edge.isBasicEdge()) {
			return convertBasicEdge(edge);
		}

		if (edge instanceof ICompositeEdge) {
			final IMinimizedEdge[] edges = ((ICompositeEdge) edge).getCompositeEdges();
			if (edge instanceof ConjunctionEdge) {
				// Since we want to compose sequential edges complete we
				// remember which sub-Edges has a conjunction as parent
				mHasConjunctionAsParent.add(edges[0]);
				mHasConjunctionAsParent.add(edges[1]);
			}
			if (edge instanceof DisjunctionEdge) {
				// When we have a disjunction we have possible two conjunctions
				// at both branches of this. So we have to create two new lists
				// on the stack.
				mSeqComposedBlocks.push(new ArrayList<CodeBlock>());
				mSeqComposedBlocks.push(new ArrayList<CodeBlock>());
			}
			final ArrayList<CodeBlock> recConvEdges = new ArrayList<>();
			for (final IMinimizedEdge compEdge : edges) {
				final CodeBlock convEdge = convertMinimizedEdge(compEdge, simplify, extPqe);
				if (edge instanceof ConjunctionEdge && convEdge != null) {
					// add on the actual list of the stack
					mSeqComposedBlocks.peek().add(convEdge);
				}
				if (convEdge instanceof Summary) {
					// we ignore Summary-Edges
					continue;
				}
				if (convEdge != null) {
					// we simply ignore null edges
					recConvEdges.add(convEdge);
				}
			}
			// some controlling here, if there are no converted edges, there
			// should be edges to compose sequentially
			if (recConvEdges.isEmpty() && mSeqComposedBlocks.isEmpty()) {
				mLogger.error("Conversion fails, both sides are null (" + edges[0] + " -- " + edges[1] + ")");
				throw new IllegalStateException(
						"Conversion failure, both sides are null" + " / and there are no seq. edges to compose!");
			}
			if (edge instanceof ConjunctionEdge) {

				// if the parent of this conjunction is also a conjunction we do
				// not create a sequential composition here
				// seqComposedBlocks.addAll(recConvEdges);
				if (mHasConjunctionAsParent.contains(edge)) {
					return null;
				}
				// In a conjunction, we can ignore GotoEdges
				final ArrayList<CodeBlock> composeEdges = new ArrayList<>();
				final ArrayList<CodeBlock> gotoEdges = new ArrayList<>();
				// we take the actual list from the stack...
				for (final CodeBlock cb : mSeqComposedBlocks.pop()) {
					if (cb instanceof GotoEdge) {
						gotoEdges.add(cb);
						continue;
					}
					composeEdges.add(cb);
				}
				// Special case: only Goto's we to transpose it to assume true
				if (composeEdges.isEmpty()) {
					if (gotoEdges.isEmpty()) {
						throw new IllegalArgumentException("No compose edges, there should be goto-Edges!");
					}
					// We add here a SequentialComposition with only one
					// element, because we have to remove later a list from the
					// stack whereas this is only done for not
					// SequentialCompositons
					if (edge instanceof ShortcutErrEdge) {
						return new ShortcutCodeBlock(null, null,
								new CodeBlock[] { replaceGotoEdge(gotoEdges.get(0), gotoEdges.get(1)) }, mLogger);
					}
					return mCbf.constructSequentialComposition(null, null, simplify, extPqe,
							Collections.singletonList(replaceGotoEdge(gotoEdges.get(0), gotoEdges.get(1))),
							mXnfConversionTechnique, mSimplificationTechnique);
				}
				if (edge instanceof ShortcutErrEdge) {
					return new ShortcutCodeBlock(null, null, composeEdges.toArray(new CodeBlock[composeEdges.size()]),
							mLogger);
				}
				return mCbf.constructSequentialComposition(null, null, simplify, extPqe,
						Collections.unmodifiableList(composeEdges), mXnfConversionTechnique, mSimplificationTechnique);
			}
			if (edge instanceof DisjunctionEdge) {
				final ArrayList<CodeBlock> composeEdges = new ArrayList<>();
				for (final CodeBlock cb : recConvEdges) {
					if (!(cb instanceof SequentialComposition) && !mSeqComposedBlocks.pop().isEmpty()) {
						throw new IllegalArgumentException(
								"It is not allowed to pop " + "non empty lists, from the stack");
					}
					if (cb instanceof GotoEdge) {
						composeEdges.add(replaceGotoEdge(cb, null));
						continue;
					}
					composeEdges.add(cb);
				}
				// TODO: For non composite edges we have to remove one thing
				// from the stack? Is this case applicable?
				if (composeEdges.size() == 1) {
					// If we have only one composedEdge we return it, because a
					// parallel composition is not needed
					if (composeEdges.get(0) instanceof SequentialComposition) {
						// -> we only pop() if the one edge is an
						// SequentialComposition, otherwise this has already
						// done
						mSeqComposedBlocks.pop();
					}
					return composeEdges.get(0);
				}
				if (composeEdges.size() != 2) {
					throw new IllegalArgumentException(
							"For DisjunctionEdges there should always" + " be exactly two edges, to compose!");
				}
				if (composeEdges.get(0) instanceof ShortcutCodeBlock
						|| composeEdges.get(1) instanceof ShortcutCodeBlock) {
					throw new IllegalArgumentException("Shortcut is contained in ParallelComposition?");
				}
				final List<CodeBlock> parallelCodeBlocks = new ArrayList<>();
				parallelCodeBlocks.add(composeEdges.get(0));
				parallelCodeBlocks.add(composeEdges.get(1));
				return mCbf.constructParallelComposition(null, null, parallelCodeBlocks, mXnfConversionTechnique,
						mSimplificationTechnique);
			}
		}
		// should never reach this end here?
		mLogger.error("Failure during construction of formulas... " + edge);
		return null;
	}

	/**
	 * This method converts a basic edge into one basic code block. It is copied, because we create new instances, since
	 * we do not want to change the original RCFG.
	 *
	 * @param edge
	 *            IMinimizedEdge which is a basic edge
	 * @return corresponding CodeBlock
	 */
	private CodeBlock convertBasicEdge(final IMinimizedEdge edge) {
		final CodeBlock cb = ((IBasicEdge) edge).getOriginalEdge();
		final CodeBlock copyOfCodeBlock;
		// We need to convert the basic edges, into new ones
		// -> so basically we create a new instance of the CodeBlock,
		// this is necessary to avoid mixing of the models
		if (cb instanceof StatementSequence) {
			copyOfCodeBlock = mCbf.constructStatementSequence(null, null, ((StatementSequence) cb).getStatements(),
					((StatementSequence) cb).getOrigin());
		} else if (cb instanceof Call) {
			copyOfCodeBlock = mCbf.constructCall(null, null, ((Call) cb).getCallStatement());
		} else if (cb instanceof Return) {
			copyOfCodeBlock = mCbf.constructReturn(null, null, ((Return) cb).getCorrespondingCall());
		} else if (cb instanceof Summary) {
			// This situation can happen, if a Call/Return/Summary-Edges are
			// involved, they are not part of the formula and are ignored
			copyOfCodeBlock = cb;
		} else if (cb instanceof GotoEdge) {
			copyOfCodeBlock = cb;
		} else {
			throw new IllegalArgumentException("Failure while converting a CodeBlock of type " + cb.getClass());
		}
		copyOfCodeBlock.setTransitionFormula(cb.getTransformula());
		ModelUtils.copyAnnotations(cb, copyOfCodeBlock);
		return copyOfCodeBlock;
	}

	/**
	 * This method replaces an Goto-Edge with the statement "assume true". <br>
	 * TODO: Need to be clarified if this is correct.
	 *
	 * @param gotoEdge
	 *            the Goto-Edge to convert
	 * @param secondGotoEdge
	 *            maybe somites we have to convert two Goto-Edges
	 * @return the converted "assume true"
	 */
	private CodeBlock replaceGotoEdge(final CodeBlock gotoEdge, final CodeBlock secondGotoEdge) {

		final ILocation loc = ILocation.getAnnotation(gotoEdge);
		final StatementSequence replacement = mCbf.constructStatementSequence(null, null,
				new AssumeStatement(loc, new BooleanLiteral(loc, BoogieType.TYPE_BOOL, true)));
		if (secondGotoEdge == null) {
			ModelUtils.copyAnnotations(gotoEdge, replacement);
		} else {
			ModelUtils.mergeAnnotations(replacement, gotoEdge, secondGotoEdge);
		}
		final String procId = gotoEdge.getPrecedingProcedure();
		mTransFormBuilder.addTransitionFormulas(replacement, procId, mXnfConversionTechnique, mSimplificationTechnique);
		return replacement;
	}

	/**
	 * @return the origToNewMap
	 */
	public HashMap<BoogieIcfgLocation, BoogieIcfgLocation> getOrigToNewMap() {
		return mOrigToNewMap;
	}

	/**
	 * @return the locNodesForAnnot
	 */
	public HashMap<String, HashMap<DebugIdentifier, BoogieIcfgLocation>> getLocNodesForAnnot() {
		return mLocNodesForAnnot;
	}
}
