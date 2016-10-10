/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 * 
 * This file is part of the ULTIMATE BuchiProgramProduct plug-in.
 * 
 * The ULTIMATE BuchiProgramProduct plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiProgramProduct plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiProgramProduct plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiProgramProduct plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiProgramProduct plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.productgenerator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.Activator;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.ProductBacktranslator;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LTLStepAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot.BuchiProgramAcceptingStateAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeIterator;

/**
 * This class is implementing the Buchi program product, i.e. interleaving a BuchiAutomaton with the CFG.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author Langenfeld
 * 
 * @see Masterarbeit Langenfeld, "Fairness Modulo Theory: A New Approach to LTL Software Model Checking"
 *
 */
public final class ProductGenerator {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final ProductBacktranslator mBacktranslator;
	private final BuchiProgramAcceptingStateAnnotation mAcceptingNodeAnnotation;
	private final RootNode mRcfgRoot;
	private final RootNode mProductRoot;
	private final INestedWordAutomaton<CodeBlock, String> mNWA;
	private final CodeBlockFactory mCodeblockFactory;
	private final ProductLocationNameGenerator mNameGenerator;

	private final Set<ProgramPoint> mRCFGLocations;
	private final Set<ProgramPoint> mRcfgSinks;
	private final Set<ProgramPoint> mRootSuccessorProgramPoints;
	private final Set<ProgramPoint> mHelperProductStates;
	private final Map<String, ProgramPoint> mProductLocations;
	private final Map<ProgramPoint, List<Call>> mOrigRcfgCallLocs2CallEdges;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final boolean mEverythingIsAStep;

	public ProductGenerator(final INestedWordAutomaton<CodeBlock, String> nwa, final RootNode rcfg,
			final LTLPropertyCheck ltlAnnot, final IUltimateServiceProvider services,
			final ProductBacktranslator backtrans, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		// services and logger
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		// save parameters
		mNWA = nwa;
		mRcfgRoot = rcfg;
		mCodeblockFactory = mRcfgRoot.getRootAnnot().getCodeBlockFactory();
		mBacktranslator = backtrans;
		mXnfConversionTechnique = xnfConversionTechnique;
		mSimplificationTechnique = simplificationTechnique;

		// initialize state
		mRCFGLocations = new HashSet<>();
		mProductLocations = new HashMap<>();
		mOrigRcfgCallLocs2CallEdges = new HashMap<>();
		mRootSuccessorProgramPoints = new HashSet<>();
		mAcceptingNodeAnnotation = new BuchiProgramAcceptingStateAnnotation();
		mRcfgSinks = new HashSet<>();
		mHelperProductStates = new HashSet<>();
		mNameGenerator = new ProductLocationNameGenerator(nwa);

		mEverythingIsAStep =
				new RCFGEdgeIterator(mRcfgRoot).asStream().allMatch(a -> LTLStepAnnotation.getAnnotation(a) == null);
		if (mEverythingIsAStep) {
			mLogger.info("The program has no step specification, so we assume maximum atomicity");
		}

		// create the new root node
		mProductRoot = new RootNode(mRcfgRoot.getPayload().getLocation(), mRcfgRoot.getRootAnnot());
		// the root annotation has to be updated to be accurate in the new RCFG
		// * getProgramPoints() will be refilled during calls to
		// createProgramPoint()
		mProductRoot.getRootAnnot().getProgramPoints().clear();
		// * getLoopLocations(), getEntryNodes() and getExitNodes() will be
		// replaced during calls to
		// createProgramPoint(), so we just let it be

		// mark the root node with the current LTL property for possible counter
		// examples
		ltlAnnot.annotate(mProductRoot);

		// start product generation
		collectRcfgLocations();
		createProductStates();
		createEdges();

		pruneNonProductSinks();

		generateTransFormulas();
	}

	public RootNode getProductRcfg() {
		return mProductRoot;
	}

	/**
	 * Collect all states that are part of the RCFG into a List.
	 */
	private void collectRcfgLocations() {
		final Set<ProgramPoint> unhandledLocations = new LinkedHashSet<>();

		for (final RCFGEdge p : mRcfgRoot.getOutgoingEdges()) {
			unhandledLocations.add((ProgramPoint) p.getTarget());
		}

		// collect all Nodes in the RCFG for the product
		ProgramPoint currentPoint;
		while (!unhandledLocations.isEmpty()) {
			currentPoint = unhandledLocations.iterator().next();
			unhandledLocations.remove(currentPoint);
			mRCFGLocations.add(currentPoint);
			for (final RCFGEdge p : currentPoint.getOutgoingEdges()) {
				if (!mRCFGLocations.contains(p.getTarget()) && !unhandledLocations.contains(p.getTarget())) {
					unhandledLocations.add((ProgramPoint) p.getTarget());
				}
			}
			// collect all sinks and add self loops to them
			if (currentPoint.getOutgoingEdges().isEmpty()) {
				mRcfgSinks.add(currentPoint);
				mapNewEdge2OldEdge(mCodeblockFactory.constructStatementSequence(currentPoint, currentPoint,
						generateNeverClaimAssumeStatement(new BooleanLiteral(null, true))), null);
			}
		}
	}

	/**
	 * Multiply states and make them available in the dictionary with their new name.
	 */
	private void createProductStates() {
		for (final ProgramPoint origpp : mRCFGLocations) {
			if (isNonProductNode(origpp)) {
				final ProgramPoint newPP = createProductProgramPoint(mNameGenerator.generateStateName(origpp), origpp);
				updateProductStates(newPP, mNameGenerator.generateStateName(origpp));
				continue;
			}

			for (final String nwaState : mNWA.getStates()) {
				final ProgramPoint newPP =
						createProductProgramPoint(mNameGenerator.generateStateName(origpp, nwaState), origpp);
				updateProductStates(newPP, mNameGenerator.generateStateName(origpp, nwaState));

				// accepting states are marked with AcceptingNodeAnnotation
				if (mNWA.isFinal(nwaState)) {
					mAcceptingNodeAnnotation.annotate(newPP);
				}
			}
		}
	}

	private void updateProductStates(final ProgramPoint newPP, final String statename) {
		assert statename.equals(newPP.getPosition());
		final ProgramPoint rtr = mProductLocations.put(newPP.getPosition(), newPP);
		if (rtr != null) {
			throw new AssertionError("The original RCFG had two locations with the same location name");
		}
	}

	/**
	 * Sinks are always product nodes. Nodes belonging to certain procedures may not be product nodes, because we want
	 * to ignore static initialization.
	 */
	private static boolean isNonProductNode(final ProgramPoint loc) {
		final String procname = loc.getProcedure();
		return "ULTIMATE.init".equals(procname) || "ULTIMATE.start".equals(procname);
	}

	/**
	 * Creates the edges of the Büchi program product in a two-stage algorithm (first, all edges except returns, second
	 * all returns).
	 */
	private void createEdges() {
		// first, do everything except return edges
		createAllEdgesExceptReturn();

		// second, handle all return edges
		createAllReturnEdges();
	}

	private void createAllReturnEdges() {
		for (final ProgramPoint origRcfgSourceLoc : mRCFGLocations) {
			for (final RCFGEdge rcfgEdge : origRcfgSourceLoc.getOutgoingEdges()) {
				if (!(rcfgEdge instanceof Return)) {
					// skip all edges that are not return edges
					continue;
				}
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Handling return edge from " + rcfgEdge.getSource() + " to " + rcfgEdge.getTarget());
				}

				final ProgramPoint origRcfgTargetLoc = (ProgramPoint) rcfgEdge.getTarget();
				final Return returnEdge = (Return) rcfgEdge;

				if (isNonProductNode(origRcfgSourceLoc) && isNonProductNode(origRcfgTargetLoc)) {
					createReturnEdgesNonProduct(origRcfgSourceLoc, origRcfgTargetLoc, returnEdge);
				} else if (isNonProductNode(origRcfgSourceLoc)) {
					createReturnEdgesNonProductToProduct(origRcfgSourceLoc, origRcfgTargetLoc, returnEdge);
				} else {
					createReturnEdgesOther(origRcfgSourceLoc, returnEdge, false);
				}
			}
		}
	}

	private void createAllEdgesExceptReturn() {
		for (final ProgramPoint origRcfgSourceLoc : mRCFGLocations) {
			for (final RCFGEdge rcfgEdge : origRcfgSourceLoc.getOutgoingEdges()) {
				if (rcfgEdge instanceof Summary && ((Summary) rcfgEdge).calledProcedureHasImplementation()) {
					// we ignore summaries for which procedures have
					// implementations
						continue;
					}

				if (rcfgEdge instanceof Return) {
					// we will handle return in a second iteration
					continue;
				}

				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Processing [" + rcfgEdge.hashCode() + "][" + rcfgEdge.getClass().getSimpleName()
							+ "] " + rcfgEdge.getSource() + " --> " + rcfgEdge.getTarget());
					mLogger.debug("\t" + rcfgEdge);
				}

				final ProgramPoint origRcfgTargetLoc = (ProgramPoint) rcfgEdge.getTarget();
				if (isNonProductNode(origRcfgSourceLoc) && isNonProductNode(origRcfgTargetLoc)) {
					createEdgesNonProduct(origRcfgSourceLoc, rcfgEdge, origRcfgTargetLoc);
				} else if (isNonProductNode(origRcfgSourceLoc)) {
					createEdgeFromNonProductToProduct(origRcfgSourceLoc, rcfgEdge);
				} else if (isNonProductNode(origRcfgTargetLoc)) {
					createEdgesFromProductToNonProduct(origRcfgSourceLoc, rcfgEdge, origRcfgTargetLoc);
				} else {
					createEdgesProduct(origRcfgSourceLoc, rcfgEdge);
				}
			}
		}
	}

	private void createReturnEdgesOther(final ProgramPoint origRcfgSourceLoc, final Return returnEdge,
			final boolean isProgramStep) {
		for (final String nwaLoc : mNWA.getStates()) {
			final ProgramPoint productSourceLoc =
					mProductLocations.get(mNameGenerator.generateStateName(origRcfgSourceLoc, nwaLoc));
			assert productSourceLoc != null;
			handleEdgeReturn(productSourceLoc, nwaLoc, returnEdge, isProgramStep);
		}
	}

	private void createReturnEdgesNonProductToProduct(final ProgramPoint origRcfgSourceLoc,
			final ProgramPoint origRcfgTargetLoc, final Return returnEdge) {
		final ProgramPoint productSourceLoc =
				mProductLocations.get(mNameGenerator.generateStateName(origRcfgSourceLoc));
		assert productSourceLoc != null;

		// there must be exactly one corresponding call, as this is
		// a return for an original call
		assert mOrigRcfgCallLocs2CallEdges.get(returnEdge.getCallerProgramPoint()).size() == 1;

		for (final String nwaLoc : mNWA.getStates()) {
			final ProgramPoint productTargetLoc =
					mProductLocations.get(mNameGenerator.generateStateName(origRcfgTargetLoc, nwaLoc));
			createNewReturnEdge(productSourceLoc, returnEdge, productTargetLoc,
					mOrigRcfgCallLocs2CallEdges.get(returnEdge.getCallerProgramPoint()).get(0));
		}
	}

	private void createReturnEdgesNonProduct(final ProgramPoint origRcfgSourceLoc, final ProgramPoint origRcfgTargetLoc,
			final Return returnEdge) {
		// handle all return edges in the non-product part
		final ProgramPoint productSourceLoc =
				mProductLocations.get(mNameGenerator.generateStateName(origRcfgSourceLoc));
		final ProgramPoint productTargetLoc =
				mProductLocations.get(mNameGenerator.generateStateName(origRcfgTargetLoc));

		assert productSourceLoc != null;
		assert productTargetLoc != null;

		// there must be exactly one corresponding call, as this is
		// a return for an original call
		assert mOrigRcfgCallLocs2CallEdges.get(returnEdge.getCallerProgramPoint()).size() == 1;
		createNewReturnEdge(productSourceLoc, returnEdge, productTargetLoc,
				mOrigRcfgCallLocs2CallEdges.get(returnEdge.getCallerProgramPoint()).get(0));
	}

	private void createEdgesProduct(final ProgramPoint origRcfgSourceLoc, final RCFGEdge rcfgEdge) {
		final boolean isProgramStep = mEverythingIsAStep || LTLStepAnnotation.getAnnotation(rcfgEdge) != null;
		// if the source is a product state, we know that the
		// target is also a product state
		// this is the normal case
		for (final String nwaLoc : mNWA.getStates()) {
			final ProgramPoint productSourceLoc =
					mProductLocations.get(mNameGenerator.generateStateName(origRcfgSourceLoc, nwaLoc));
			
			addRootEdgeIfNecessary(origRcfgSourceLoc, nwaLoc, productSourceLoc);
			if (rcfgEdge instanceof StatementSequence) {
				handleEdgeStatementSequence(productSourceLoc, nwaLoc, (StatementSequence) rcfgEdge, isProgramStep);
			} else if (rcfgEdge instanceof Call) {
				handleEdgeCall(productSourceLoc, nwaLoc, (Call) rcfgEdge, origRcfgSourceLoc, isProgramStep);
			} else if (rcfgEdge instanceof Summary) {
				handleEdgeSummary(productSourceLoc, nwaLoc, (Summary) rcfgEdge);
			} else {
				// we encounted an unhandled edge type and have
				// to abort
				throw new UnsupportedOperationException("BuchiProgramProduct does not support RCFGEdges of type "
						+ rcfgEdge.getClass().getSimpleName());
			}
		}
	}

	private void createEdgesFromProductToNonProduct(final ProgramPoint origRcfgSourceLoc, final RCFGEdge origRcfgEdge,
			final ProgramPoint origRcfgTargetLoc) throws AssertionError {
		// this case can only occur if we call to a
		// non-product method to the product part.
		// therefore, only Call and Summary edges are
		// allowed

		for (final String nwaLoc : mNWA.getStates()) {
			final ProgramPoint productSourceLoc =
					mProductLocations.get(mNameGenerator.generateStateName(origRcfgSourceLoc, nwaLoc));
			final ProgramPoint productTargetLoc =
					mProductLocations.get(mNameGenerator.generateStateName(origRcfgTargetLoc));

			addRootEdgeIfNecessary(origRcfgSourceLoc, nwaLoc, productSourceLoc);

			assert productSourceLoc != null;
			assert productTargetLoc != null;

			if (origRcfgEdge instanceof Call) {
				createNewCallEdge(origRcfgSourceLoc, productSourceLoc, (Call) origRcfgEdge, productTargetLoc);
			} else if (origRcfgEdge instanceof Summary) {
				createNewSummaryEdge(productSourceLoc, (Summary) origRcfgEdge, productTargetLoc);
			} else {
				throw new AssertionError("You cannot go from product to non-product parts "
						+ "without using Call, Return or Summary edges");
			}
		}
	}

	private void createEdgeFromNonProductToProduct(final ProgramPoint origRcfgSourceLoc, final RCFGEdge rcfgEdge)
			throws AssertionError {
		// if the source is a non-product state and the target is
		// part of a real product state, we know that it has to be a
		// call edge or an edge to a sink state.
		// if its a call edge, we generate new call edges that link
		// the non-product state with all product states that are
		// initial states (because we enter the part were we observe
		// the property)
		// if its a edge to a sink state its slightly more
		// complicated.

		final ProgramPoint productSourceLoc =
				mProductLocations.get(mNameGenerator.generateStateName(origRcfgSourceLoc));
		addRootEdgeIfNecessary(origRcfgSourceLoc, null, productSourceLoc);
		if (rcfgEdge instanceof Call) {
			handleEdgeCallFromNonProduct(productSourceLoc, (Call) rcfgEdge, origRcfgSourceLoc);
		} else if (rcfgEdge instanceof Summary) {
			handleEdgeSummaryFromNonProduct(productSourceLoc, (Summary) rcfgEdge);
		} else {
			throw new AssertionError();
		}
	}

	private void createEdgesNonProduct(final ProgramPoint origRcfgSourceLoc, final RCFGEdge rcfgEdge,
			final ProgramPoint origRcfgTargetLoc) throws AssertionError {
		// if the current node and its target belong to ignored
		// procedures, just replicate the RCFG

		final ProgramPoint productSourceLoc =
				mProductLocations.get(mNameGenerator.generateStateName(origRcfgSourceLoc));
		final ProgramPoint productTargetLoc =
				mProductLocations.get(mNameGenerator.generateStateName(origRcfgTargetLoc));
		assert productSourceLoc != null;
		assert productTargetLoc != null;

		addRootEdgeIfNecessary(origRcfgSourceLoc, null, productSourceLoc);

		if (rcfgEdge instanceof StatementSequence) {
			createNewStatementSequence(productSourceLoc, (StatementSequence) rcfgEdge, productTargetLoc, null, false);
		} else if (rcfgEdge instanceof Call) {
			createNewCallEdge(origRcfgSourceLoc, productSourceLoc, (Call) rcfgEdge, productTargetLoc);
		} else if (rcfgEdge instanceof Summary) {
			createNewSummaryEdge(productSourceLoc, (Summary) rcfgEdge, productTargetLoc);
		} else {
			throw new AssertionError("Did not expect edge of type " + rcfgEdge.getClass().getSimpleName());
		}
	}

	private boolean addRootEdgeIfNecessary(final ProgramPoint origRcfgSourceLoc, final String nwaState,
			final ProgramPoint productTargetLoc) {
		if (origRcfgSourceLoc.getIncomingEdges().size() == 1
				&& origRcfgSourceLoc.getIncomingEdges().get(0) instanceof RootEdge
				&& (nwaState == null || mNWA.isInitial(nwaState))) {
			assert productTargetLoc != null;
			if (!mRootSuccessorProgramPoints.contains(productTargetLoc)) {
				final RootEdge edge = new RootEdge(mProductRoot, productTargetLoc);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Created RootEdge (" + mProductRoot + ", " + productTargetLoc + ")");
				}
				mapNewEdge2OldEdge(edge, null);
				mRootSuccessorProgramPoints.add(productTargetLoc);
			}
			return true;
		}
		return false;
	}

	private void pruneNonProductSinks() {
		// all helper states that have edges to non-product states receive a
		// self-loop that keeps them in the same product state as the LTL NWA

		for (final ProgramPoint helper : mHelperProductStates) {
			// we only consider helpers that lead from product parts to
			// non-product parts, and those helpers have only return edges as
			// incoming edge
			if (!areAllIncomingEdgesReturn(helper) || !areAllDirectPredecessorsProductNodes(helper)
					|| !areAllDirectSuccessorsNonProductNodes(helper)) {
				continue;
			}

			pruneNonProductSink(helper);
		}
	}

	private void pruneNonProductSink(final ProgramPoint helper) {
			final List<RCFGEdge> outEdges = new ArrayList<>(helper.getOutgoingEdges());
			final Set<RCFGNode> successors = new HashSet<>(helper.getOutgoingNodes());
			final Set<RCFGNode> predecessors = new HashSet<>(helper.getIncomingNodes());

			for (final RCFGEdge outgoing : outEdges) {
				// remove all outgoing edges
				outgoing.disconnectSource();
				outgoing.disconnectTarget();
			}

			// remove the targets and all the nodes that can be reached from the
			// target
			for (final RCFGNode successor : successors) {
				removeProductProgramPointAndSuccessors((ProgramPoint) successor);
			}

			// we add a self loop that will be used later
			final StatementSequence seq = mCodeblockFactory.constructStatementSequence(helper, helper,
					generateNeverClaimAssumeStatement(new BooleanLiteral(null, BoogieType.TYPE_BOOL, true)));
			mapNewEdge2OldEdge(seq, null);

			// determine what kind of loop has to be added to this state based
			// on the LTL NWA state of the predecessor
			boolean added = false;
			for (final String nwaState : mNWA.getStates()) {
				for (final RCFGNode node : predecessors) {
					final ProgramPoint predecessor = (ProgramPoint) node;
				if (!predecessor.getPosition().endsWith(nwaState)) {
					continue;
				}

				// ok, the predecessor is from this node; now we add self loops to the helper state that keep us
				// in this NWA state
				for (final OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaState)) {
							if (autTrans.getSucc().equals(nwaState)) {
								createNewStatementSequence(helper, seq, helper, autTrans.getLetter(),false);
								added = true;
							}
						}

						if (mNWA.isFinal(nwaState)) {
					// and if the nwa state is accepting, this state will also be accepting
							mAcceptingNodeAnnotation.annotate(helper);
						}
					}
				}
			// hacky shit: the ss is now useless; we remove it
			if (added) {
				seq.disconnectSource();
				seq.disconnectTarget();
			}
		}

	private static boolean areAllIncomingEdgesReturn(final ProgramPoint helper) {
		for (final RCFGEdge edge : helper.getIncomingEdges()) {
			if (!(edge instanceof Return)) {
				return false;
			}
		}
		return true;
	}

	private static boolean areAllDirectPredecessorsProductNodes(final ProgramPoint helper) {
		for (final RCFGNode node : helper.getIncomingNodes()) {
			final ProgramPoint pre = (ProgramPoint) node;
			if (isNonProductNode(pre)) {
				return false;
			}
		}
		return true;
	}

	private static boolean areAllDirectSuccessorsNonProductNodes(final ProgramPoint helper) {
		for (final RCFGNode node : helper.getOutgoingNodes()) {
			final ProgramPoint successor = (ProgramPoint) node;
			if (!isNonProductNode(successor)) {
				return false;
			}
		}
		return true;
	}

	private void removeProductProgramPointAndSuccessors(final ProgramPoint successor) {
		// removes the given product program point and all successors

		// first, collect all points that should be removed
		final Set<ProgramPoint> toRemove = new HashSet<>();
		final Deque<ProgramPoint> work = new LinkedList<>();
		work.add(successor);
		while (!work.isEmpty()) {
			final ProgramPoint current = work.removeFirst();
			if (toRemove.contains(current)) {
				continue;
			}
			toRemove.add(current);

			for (final RCFGEdge succ : current.getOutgoingEdges()) {
				work.addFirst((ProgramPoint) succ.getTarget());
			}
		}

		final RootAnnot rootAnnot = mProductRoot.getRootAnnot();
		for (final ProgramPoint current : toRemove) {
			final String name = current.getPosition();
			// update annotations

			final Map<String, ProgramPoint> prog2programPoints =
					rootAnnot.getProgramPoints().get(current.getProcedure());
			if (prog2programPoints != null) {
				prog2programPoints.remove(name);
			}

			rootAnnot.getLoopLocations().remove(current);

			final ProgramPoint entry = rootAnnot.getEntryNodes().get(current.getProcedure());
			if (current.equals(entry)) {
				rootAnnot.getEntryNodes().remove(current.getProcedure());
			}

			final ProgramPoint exit = rootAnnot.getExitNodes().get(current.getProcedure());
			if (current.equals(exit)) {
				rootAnnot.getExitNodes().remove(current);
			}

			if (ProductLocationNameGenerator.isHelperState(current)) {
				mHelperProductStates.remove(current);
			}
		}
	}

	private void generateTransFormulas() {
		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(mProductRoot, mServices, mSimplificationTechnique, mXnfConversionTechnique);

		final Set<Entry<String, Map<String, ProgramPoint>>> programPoints =
				mProductRoot.getRootAnnot().getProgramPoints().entrySet();
		for (final Entry<String, Map<String, ProgramPoint>> pairs : programPoints) {
			for (final Entry<String, ProgramPoint> loc : pairs.getValue().entrySet()) {
				for (final RCFGEdge edge : loc.getValue().getOutgoingEdges()) {
					generateTransformula(tfb, pairs.getKey(), edge);
					}
				}
			}
		}

	private static void generateTransformula(final TransFormulaBuilder tfb, final String procId, final RCFGEdge edge) {
		if (edge instanceof StatementSequence || edge instanceof Summary) {
			tfb.addTransFormula((CodeBlock) edge, procId);
	}
	}

	private void handleEdgeStatementSequence(final ProgramPoint productLoc, final String nwaLoc,
			final StatementSequence rcfgEdge, final boolean isProgramStep) {
		ProgramPoint targetpp;
		// if this is a program step encode normal (crossproduct) else 
		// stay in the same buchi state and append program flow
		if(isProgramStep){
			for (final OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaLoc)) {
				//add no edges if this is not a program step or not the program flow
				targetpp = mProductLocations
						.get(mNameGenerator.generateStateName((ProgramPoint) rcfgEdge.getTarget(), autTrans.getSucc()));
				// append statements of rcfg and ltl
				createNewStatementSequence(productLoc, rcfgEdge, targetpp, autTrans.getLetter(), isProgramStep);
			}
		} else {
			//add no edges if this is not a program step or not the program flow
			targetpp = mProductLocations
					.get(mNameGenerator.generateStateName((ProgramPoint) rcfgEdge.getTarget(), nwaLoc));
			// append statements of rcfg and ltl
			createNewStatementSequence(productLoc, rcfgEdge, targetpp, null, isProgramStep);
		}
		
		
		

	}

	private void handleEdgeReturn(final ProgramPoint productLoc, final String nwaLoc, final Return returnEdge,
			final boolean isProgramStep) {
		// The calls used for the returns are dummy calls,
		// that have nothing common with the original
		// call except the caller location, that has to be
		// popped from the stack.
		// The target pp and call statement are never used
		// and therefore left blank

		// for all possible call origins: CallPP x LTLStates
		// be able to return to the helper state
		final ProgramPoint caller = returnEdge.getCallerProgramPoint();

		assert caller != null;
		assert mOrigRcfgCallLocs2CallEdges != null;

		if (mOrigRcfgCallLocs2CallEdges.get(caller) == null) {
			// this seems to be a pathological case; we inspect it closer, but
			// we do not add a return edge!
			final Call correspondingCall = returnEdge.getCorrespondingCall();
			mLogger.warn("Ignoring return edge from " + returnEdge.getSource() + " to " + returnEdge.getTarget()
					+ " (Corresponding call: " + correspondingCall + " from " + correspondingCall.getSource() + ")");

			return;
		}

		final ProgramPoint origRcfgTargetLoc = (ProgramPoint) returnEdge.getTarget();
		final String helperName = mNameGenerator.generateHelperStateName(origRcfgTargetLoc.getPosition());
		final ProgramPoint helper = createProductProgramPoint(helperName, origRcfgTargetLoc);

		for (final Call call : mOrigRcfgCallLocs2CallEdges.get(caller)) {
			createNewReturnEdge(productLoc, returnEdge, helper, call);
		}

		// From the helpernode, the original call target is
		// connected with a new
		// edge with the fitting assumption of the call. The
		// edge is calculated
		// like any other edge in the graph.
		for (final OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaLoc)) {
			if (!isProgramStep && !autTrans.getSucc().equals(nwaLoc)) {
				continue;
			}
			ProgramPoint targetpp =
					mProductLocations.get(mNameGenerator.generateStateName(origRcfgTargetLoc, autTrans.getSucc()));
			if (targetpp == null) {
				// returns may connect with multiple edges to a single state
				// that is part of the non-product states
				targetpp = mProductLocations.get(mNameGenerator.generateStateName(origRcfgTargetLoc));
			}
			createNewStatementSequence(helper, null, targetpp, autTrans.getLetter(), isProgramStep);
		}
	}

	private void handleEdgeSummary(final ProgramPoint productSourceLoc, final String nwaLoc, final Summary summary) {
		// the summary edge in the original program should be concatenated with
		// each outgoing letter of the NWA and the resulting edges should be
		// inserted in the new NWA (happens automatically during construction)

		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(mProductRoot, mServices, mSimplificationTechnique, mXnfConversionTechnique);

		ProgramPoint targetpp;
		for (final OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaLoc)) {
			targetpp = mProductLocations
					.get(mNameGenerator.generateStateName((ProgramPoint) summary.getTarget(), autTrans.getSucc()));
			final List<CodeBlock> sumAndSs = new ArrayList<>();
			final StatementSequence seq = mCodeblockFactory.constructStatementSequence(productSourceLoc, targetpp,
					checkLetter(autTrans.getLetter()), Origin.IMPLEMENTATION);

			tfb.addTransFormula(seq, ((ProgramPoint) summary.getSource()).getProcedure());

			sumAndSs.add(createNewSummaryEdge(productSourceLoc, summary, targetpp));
			sumAndSs.add(seq);

			mCodeblockFactory.constructSequentialComposition(productSourceLoc, targetpp, true, true, sumAndSs,
					mXnfConversionTechnique, mSimplificationTechnique);
		}
	}

	private void handleEdgeSummaryFromNonProduct(final ProgramPoint productSourceLoc, final Summary rcfgEdge) {
		final ProgramPoint origRcfgTargetLoc = (ProgramPoint) rcfgEdge.getTarget();
		for (final String initialNWAState : mNWA.getInitialStates()) {
			final ProgramPoint productTargetLoc =
					mProductLocations.get(mNameGenerator.generateStateName(origRcfgTargetLoc, initialNWAState));
			createNewSummaryEdge(productSourceLoc, rcfgEdge, productTargetLoc);
		}

	}

	private void handleEdgeCall(final ProgramPoint productSourceLoc, final String nwaSourceState,
			final Call origRcfgEdge, final ProgramPoint origRcfgSourceLoc, final boolean isProgramStep) {

		final String helperName = mNameGenerator.generateHelperStateName(productSourceLoc.getPosition());
		final ProgramPoint origRcfgTargetLoc = (ProgramPoint) origRcfgEdge.getTarget();
		final ProgramPoint helper = createProductProgramPoint(helperName, origRcfgTargetLoc);

		createNewCallEdge(origRcfgSourceLoc, productSourceLoc, origRcfgEdge, helper);

		// From the helpernode, the original call target is
		// connected with a new
		// edge with the fitting assumption of the call. The
		// edge is calculated
		// like any other edge in the graph.
		for (final OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaSourceState)) {
			final ProgramPoint targetpp =
					mProductLocations.get(mNameGenerator.generateStateName(origRcfgTargetLoc, autTrans.getSucc()));
			//if the transition would lead into another BA state and is no program step continue
			if(!isProgramStep && !autTrans.getSucc().equals(nwaSourceState)) {
				continue;
			}
			createNewStatementSequence(helper, null, targetpp, autTrans.getLetter(), isProgramStep);
		}
	}

	private void handleEdgeCallFromNonProduct(final ProgramPoint productSourceLoc, final Call origRcfgEdge,
			final ProgramPoint origRcfgSourceLoc) {
		final ProgramPoint origRcfgTargetLoc = (ProgramPoint) origRcfgEdge.getTarget();
		for (final String initialNWAState : mNWA.getInitialStates()) {
			final ProgramPoint productTargetLoc =
					mProductLocations.get(mNameGenerator.generateStateName(origRcfgTargetLoc, initialNWAState));
			createNewCallEdge(origRcfgSourceLoc, productSourceLoc, origRcfgEdge, productTargetLoc);
		}
	}

	private Summary createNewSummaryEdge(final ProgramPoint productSourceLoc, final Summary origSummary,
			final ProgramPoint productTargetLoc) {
		assert productSourceLoc != null;
		assert productTargetLoc != null;
		final Summary sum = mCodeblockFactory.constructSummary(productSourceLoc, productTargetLoc,
				origSummary.getCallStatement(), false);
		sum.setTransitionFormula(origSummary.getTransitionFormula());

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Created summary edge (" + productSourceLoc + ", " + productTargetLoc + ") for call "
					+ BoogiePrettyPrinter.print(origSummary.getCallStatement()));
		}
		return sum;
	}

	private Return createNewReturnEdge(final ProgramPoint productSourceLoc, final Return origRcfgEdge,
			final ProgramPoint productTargetLoc, final Call correspondingCall) {
		assert productSourceLoc != null;
		assert productTargetLoc != null;
		final Return returnEdge =
				mCodeblockFactory.constructReturn(productSourceLoc, productTargetLoc, correspondingCall);
		returnEdge.setTransitionFormula(origRcfgEdge.getTransitionFormula());
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Created return edge (" + productSourceLoc + ", " + productTargetLoc + ") for call from "
					+ correspondingCall.getSource());
		}
		mapNewEdge2OldEdge(returnEdge, origRcfgEdge);
		return returnEdge;
	}

	private Call createNewCallEdge(final ProgramPoint origRcfgSourceLoc, final ProgramPoint productSourceLoc,
			final Call origRcfgEdge, final ProgramPoint productTargetLoc) {
		assert productSourceLoc != null;
		assert productTargetLoc != null;
		final Call call =
				mCodeblockFactory.constructCall(productSourceLoc, productTargetLoc, origRcfgEdge.getCallStatement());
		call.setTransitionFormula(origRcfgEdge.getTransitionFormula());
		mapNewEdge2OldEdge(call, origRcfgEdge);

		// store all call edges in hashmap for the handling of return edges
		// later on
		List<Call> calls = mOrigRcfgCallLocs2CallEdges.get(origRcfgSourceLoc);
		if (calls == null) {
			calls = new ArrayList<>();
			mOrigRcfgCallLocs2CallEdges.put(origRcfgSourceLoc, calls);
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Adding call to " + call + " for " + productSourceLoc + ", " + productTargetLoc + " under "
					+ origRcfgSourceLoc);
		}
		calls.add(call);

		return call;
	}

	private ProgramPoint createProductProgramPoint(final String stateName, final ProgramPoint originalState) {
		final ProgramPoint rtr =
				new ProgramPoint(stateName, originalState.getProcedure(), false, originalState.getBoogieASTNode());

		// update annotations
		final RootAnnot rootAnnot = mProductRoot.getRootAnnot();
		Map<String, ProgramPoint> prog2programPoints = rootAnnot.getProgramPoints().get(originalState.getProcedure());
		if (prog2programPoints == null) {
			prog2programPoints = new HashMap<>();
			rootAnnot.getProgramPoints().put(originalState.getProcedure(), prog2programPoints);
		}
		prog2programPoints.put(stateName, rtr);

		final ILocation currentLoopLoc = mProductRoot.getRootAnnot().getLoopLocations().remove(originalState);
		if (currentLoopLoc != null) {
			rootAnnot.getLoopLocations().put(rtr, currentLoopLoc);
		}

		// TODO: It may happen that we have multiple entry points because of the
		// products; but we can currently only represent one. Do we need to do
		// something about that?

		final ProgramPoint entry = rootAnnot.getEntryNodes().get(originalState.getProcedure());
		if (entry != null) {
			rootAnnot.getEntryNodes().put(originalState.getProcedure(), rtr);
		}

		final ProgramPoint exit = rootAnnot.getExitNodes().get(originalState.getProcedure());
		if (exit != null) {
			rootAnnot.getExitNodes().put(originalState.getProcedure(), rtr);
		}

		if (ProductLocationNameGenerator.isHelperState(rtr)) {
			mHelperProductStates.add(rtr);
		}

		return rtr;
	}

	private StatementSequence createNewStatementSequence(final ProgramPoint currentpp,
			final StatementSequence originalSS, final ProgramPoint targetpp, final CodeBlock letter,
			final boolean isProgramStep) {
		final List<Statement> stmts = new ArrayList<>();
		if (originalSS != null) {
			stmts.addAll(originalSS.getStatements());
		}
		if(isProgramStep){
			stmts.addAll(checkLetter(letter));
		}
		// create the edge
		StatementSequence newSS; 
		assert currentpp != null;
		assert targetpp != null;
		if (originalSS == null) {
			newSS = mCodeblockFactory.constructStatementSequence(currentpp, targetpp, stmts, Origin.IMPLEMENTATION);
		} else {
			newSS = mCodeblockFactory.constructStatementSequence(currentpp, targetpp, stmts, originalSS.getOrigin());
		}

		mapNewEdge2OldEdge(newSS, originalSS);
		return newSS;
	}

	private static List<Statement> checkLetter(final CodeBlock letter) {
		if (letter == null) {
			return Collections.emptyList();
		}
			if (letter instanceof StatementSequence) {
				final StatementSequence autTransStmts = (StatementSequence) letter;
				return autTransStmts.getStatements();
		}
				throw new UnsupportedOperationException(
						"Letter has to be a statement sequence, but is " + letter.getClass().getSimpleName());
			}

	private void mapNewEdge2OldEdge(final RCFGEdge newEdge, final RCFGEdge originalEdge) {
		mBacktranslator.mapEdges(newEdge, originalEdge);
	}

	private static AssumeStatement generateNeverClaimAssumeStatement(final Expression expr) {
		return new AssumeStatement(null, expr);
	}
}
