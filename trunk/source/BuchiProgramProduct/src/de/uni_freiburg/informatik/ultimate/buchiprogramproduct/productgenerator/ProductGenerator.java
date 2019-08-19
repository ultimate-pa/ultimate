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
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.BuchiProgramAcceptingStateAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LTLStepAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

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
	private final BoogieIcfgContainer mRcfgRoot;
	private final BoogieIcfgContainer mProductRoot;
	private final INestedWordAutomaton<CodeBlock, String> mNWA;
	private final CodeBlockFactory mCodeblockFactory;
	private final ProductLocationNameGenerator mNameGenerator;

	private final Set<BoogieIcfgLocation> mRCFGLocations;
	private final Set<BoogieIcfgLocation> mRcfgSinks;
	private final Set<BoogieIcfgLocation> mHelperProductStates;
	private final Map<DebugIdentifier, BoogieIcfgLocation> mProductLocations;
	private final Map<BoogieIcfgLocation, List<Call>> mOrigRcfgCallLocs2CallEdges;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final boolean mEverythingIsAStep;

	public ProductGenerator(final INestedWordAutomaton<CodeBlock, String> nwa, final BoogieIcfgContainer rcfg,
			final LTLPropertyCheck ltlAnnot, final IUltimateServiceProvider services,
			final ProductBacktranslator backtrans, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		// services and logger
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		// save parameters
		mNWA = nwa;
		mRcfgRoot = rcfg;
		mCodeblockFactory = mRcfgRoot.getCodeBlockFactory();
		mBacktranslator = backtrans;
		mXnfConversionTechnique = xnfConversionTechnique;
		mSimplificationTechnique = simplificationTechnique;

		// initialize state
		mRCFGLocations = new HashSet<>();
		mProductLocations = new HashMap<>();
		mOrigRcfgCallLocs2CallEdges = new HashMap<>();
		mAcceptingNodeAnnotation = new BuchiProgramAcceptingStateAnnotation();
		mRcfgSinks = new HashSet<>();
		mHelperProductStates = new HashSet<>();
		mNameGenerator = new ProductLocationNameGenerator();

		mEverythingIsAStep = new IcfgEdgeIterator(BoogieIcfgContainer.extractStartEdges(mRcfgRoot)).asStream()
				.allMatch(a -> LTLStepAnnotation.getAnnotation(a) == null);
		if (mEverythingIsAStep) {
			mLogger.info("The program has no step specification, so we assume maximum atomicity");
		}

		// create the new root node
		mProductRoot = mRcfgRoot;
		// the root annotation has to be updated to be accurate in the new RCFG
		// * getProgramPoints() will be refilled during calls to
		// createProgramPoint()
		mProductRoot.getProgramPoints().clear();
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

	public BoogieIcfgContainer getProductRcfg() {
		return mProductRoot;
	}

	/**
	 * Collect all states that are part of the RCFG into a List.
	 */
	private void collectRcfgLocations() {
		final Set<BoogieIcfgLocation> unhandledLocations = new LinkedHashSet<>();

		for (final Entry<String, BoogieIcfgLocation> entry : mRcfgRoot.getProcedureEntryNodes().entrySet()) {
			unhandledLocations.add(entry.getValue());
		}

		// collect all Nodes in the RCFG for the product
		BoogieIcfgLocation currentPoint;
		while (!unhandledLocations.isEmpty()) {
			currentPoint = unhandledLocations.iterator().next();
			unhandledLocations.remove(currentPoint);
			mRCFGLocations.add(currentPoint);
			for (final IcfgEdge p : currentPoint.getOutgoingEdges()) {
				if (!mRCFGLocations.contains(p.getTarget()) && !unhandledLocations.contains(p.getTarget())) {
					unhandledLocations.add((BoogieIcfgLocation) p.getTarget());
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
		for (final BoogieIcfgLocation origpp : mRCFGLocations) {
			if (isNonProductNode(origpp)) {
				final BoogieIcfgLocation newPP =
						createProductProgramPoint(ProductLocationNameGenerator.generateStateName(origpp), origpp);
				updateProductStates(newPP, ProductLocationNameGenerator.generateStateName(origpp));
				continue;
			}

			for (final String nwaState : mNWA.getStates()) {
				final BoogieIcfgLocation newPP = createProductProgramPoint(
						ProductLocationNameGenerator.generateStateName(origpp, nwaState), origpp);
				updateProductStates(newPP, ProductLocationNameGenerator.generateStateName(origpp, nwaState));

				// accepting states are marked with AcceptingNodeAnnotation
				if (mNWA.isFinal(nwaState)) {
					mAcceptingNodeAnnotation.annotate(newPP);
				}
			}
		}
	}

	private void updateProductStates(final BoogieIcfgLocation newPP, final DebugIdentifier statename) {
		assert statename.equals(newPP.getDebugIdentifier()) : String.format(
				"statename %s does not equal debug identifier %s of location", statename, newPP.getDebugIdentifier());
		final BoogieIcfgLocation rtr = mProductLocations.put(newPP.getDebugIdentifier(), newPP);
		if (rtr != null) {
			throw new AssertionError(
					String.format("The original RCFG had two locations with the same location name: %s of type %s",
							newPP.getDebugIdentifier(), newPP.getDebugIdentifier().getClass()));
		}
	}

	/**
	 * Sinks are always product nodes. Nodes belonging to certain procedures may not be product nodes, because we want
	 * to ignore static initialization.
	 */
	private static boolean isNonProductNode(final BoogieIcfgLocation loc) {
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
		for (final BoogieIcfgLocation origRcfgSourceLoc : mRCFGLocations) {
			for (final IcfgEdge rcfgEdge : origRcfgSourceLoc.getOutgoingEdges()) {
				if (!(rcfgEdge instanceof Return)) {
					// skip all edges that are not return edges
					continue;
				}
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Handling return edge from " + rcfgEdge.getSource() + " to " + rcfgEdge.getTarget());
				}

				final BoogieIcfgLocation origRcfgTargetLoc = (BoogieIcfgLocation) rcfgEdge.getTarget();
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
		for (final BoogieIcfgLocation origRcfgSourceLoc : mRCFGLocations) {
			for (final IcfgEdge rcfgEdge : origRcfgSourceLoc.getOutgoingEdges()) {
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

				final BoogieIcfgLocation origRcfgTargetLoc = (BoogieIcfgLocation) rcfgEdge.getTarget();
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

	private void createReturnEdgesOther(final BoogieIcfgLocation origRcfgSourceLoc, final Return returnEdge,
			final boolean isProgramStep) {
		for (final String nwaLoc : mNWA.getStates()) {
			final BoogieIcfgLocation productSourceLoc =
					mProductLocations.get(ProductLocationNameGenerator.generateStateName(origRcfgSourceLoc, nwaLoc));
			assert productSourceLoc != null;
			handleEdgeReturn(productSourceLoc, nwaLoc, returnEdge, isProgramStep);
		}
	}

	private void createReturnEdgesNonProductToProduct(final BoogieIcfgLocation origRcfgSourceLoc,
			final BoogieIcfgLocation origRcfgTargetLoc, final Return returnEdge) {
		final BoogieIcfgLocation productSourceLoc =
				mProductLocations.get(ProductLocationNameGenerator.generateStateName(origRcfgSourceLoc));
		assert productSourceLoc != null;

		// there must be exactly one corresponding call, as this is
		// a return for an original call
		assert mOrigRcfgCallLocs2CallEdges.get(returnEdge.getCallerProgramPoint()).size() == 1;

		for (final String nwaLoc : mNWA.getStates()) {
			final BoogieIcfgLocation productTargetLoc =
					mProductLocations.get(ProductLocationNameGenerator.generateStateName(origRcfgTargetLoc, nwaLoc));
			createNewReturnEdge(productSourceLoc, returnEdge, productTargetLoc,
					mOrigRcfgCallLocs2CallEdges.get(returnEdge.getCallerProgramPoint()).get(0));
		}
	}

	private void createReturnEdgesNonProduct(final BoogieIcfgLocation origRcfgSourceLoc,
			final BoogieIcfgLocation origRcfgTargetLoc, final Return returnEdge) {
		// handle all return edges in the non-product part
		final BoogieIcfgLocation productSourceLoc =
				mProductLocations.get(ProductLocationNameGenerator.generateStateName(origRcfgSourceLoc));
		final BoogieIcfgLocation productTargetLoc =
				mProductLocations.get(ProductLocationNameGenerator.generateStateName(origRcfgTargetLoc));

		assert productSourceLoc != null;
		assert productTargetLoc != null;

		// there must be exactly one corresponding call, as this is
		// a return for an original call
		assert mOrigRcfgCallLocs2CallEdges.get(returnEdge.getCallerProgramPoint()).size() == 1;
		createNewReturnEdge(productSourceLoc, returnEdge, productTargetLoc,
				mOrigRcfgCallLocs2CallEdges.get(returnEdge.getCallerProgramPoint()).get(0));
	}

	private void createEdgesProduct(final BoogieIcfgLocation origRcfgSourceLoc, final IcfgEdge rcfgEdge) {
		final boolean isProgramStep = mEverythingIsAStep || LTLStepAnnotation.getAnnotation(rcfgEdge) != null;
		// if the source is a product state, we know that the
		// target is also a product state
		// this is the normal case
		for (final String nwaLoc : mNWA.getStates()) {
			final BoogieIcfgLocation productSourceLoc =
					mProductLocations.get(ProductLocationNameGenerator.generateStateName(origRcfgSourceLoc, nwaLoc));

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

	private void createEdgesFromProductToNonProduct(final BoogieIcfgLocation origRcfgSourceLoc,
			final IcfgEdge origRcfgEdge, final BoogieIcfgLocation origRcfgTargetLoc) throws AssertionError {
		// this case can only occur if we call to a
		// non-product method to the product part.
		// therefore, only Call and Summary edges are
		// allowed

		for (final String nwaLoc : mNWA.getStates()) {
			final BoogieIcfgLocation productSourceLoc =
					mProductLocations.get(ProductLocationNameGenerator.generateStateName(origRcfgSourceLoc, nwaLoc));
			final BoogieIcfgLocation productTargetLoc =
					mProductLocations.get(ProductLocationNameGenerator.generateStateName(origRcfgTargetLoc));

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

	private void createEdgeFromNonProductToProduct(final BoogieIcfgLocation origRcfgSourceLoc, final IcfgEdge rcfgEdge)
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

		final BoogieIcfgLocation productSourceLoc =
				mProductLocations.get(ProductLocationNameGenerator.generateStateName(origRcfgSourceLoc));
		if (rcfgEdge instanceof Call) {
			handleEdgeCallFromNonProduct(productSourceLoc, (Call) rcfgEdge, origRcfgSourceLoc);
		} else if (rcfgEdge instanceof Summary) {
			handleEdgeSummaryFromNonProduct(productSourceLoc, (Summary) rcfgEdge);
		} else {
			throw new AssertionError();
		}
	}

	private void createEdgesNonProduct(final BoogieIcfgLocation origRcfgSourceLoc, final IcfgEdge rcfgEdge,
			final BoogieIcfgLocation origRcfgTargetLoc) throws AssertionError {
		// if the current node and its target belong to ignored
		// procedures, just replicate the RCFG

		final BoogieIcfgLocation productSourceLoc =
				mProductLocations.get(ProductLocationNameGenerator.generateStateName(origRcfgSourceLoc));
		final BoogieIcfgLocation productTargetLoc =
				mProductLocations.get(ProductLocationNameGenerator.generateStateName(origRcfgTargetLoc));
		assert productSourceLoc != null;
		assert productTargetLoc != null;

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

	private void pruneNonProductSinks() {
		// all helper states that have edges to non-product states receive a
		// self-loop that keeps them in the same product state as the LTL NWA

		for (final BoogieIcfgLocation helper : mHelperProductStates) {
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

	private void pruneNonProductSink(final BoogieIcfgLocation helper) {
		final List<IcfgEdge> outEdges = new ArrayList<>(helper.getOutgoingEdges());
		final Set<IcfgLocation> successors = new HashSet<>(helper.getOutgoingNodes());
		final Set<IcfgLocation> predecessors = new HashSet<>(helper.getIncomingNodes());

		for (final IcfgEdge outgoing : outEdges) {
			// remove all outgoing edges
			outgoing.disconnectSource();
			outgoing.disconnectTarget();
		}

		// remove the targets and all the nodes that can be reached from the
		// target
		for (final IcfgLocation successor : successors) {
			removeProductProgramPointAndSuccessors((BoogieIcfgLocation) successor);
		}

		// we add a self loop that will be used later
		final StatementSequence seq = mCodeblockFactory.constructStatementSequence(helper, helper,
				generateNeverClaimAssumeStatement(new BooleanLiteral(null, BoogieType.TYPE_BOOL, true)));
		mapNewEdge2OldEdge(seq, null);

		// determine what kind of loop has to be added to this state based
		// on the LTL NWA state of the predecessor
		boolean added = false;
		for (final String nwaState : mNWA.getStates()) {
			for (final IcfgLocation node : predecessors) {
				final BoogieIcfgLocation predecessor = (BoogieIcfgLocation) node;
				if (!predecessor.getDebugIdentifier().toString().endsWith(nwaState)) {
					continue;
				}

				// ok, the predecessor is from this node; now we add self loops to the helper state that keep us
				// in this NWA state
				for (final OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaState)) {
					if (autTrans.getSucc().equals(nwaState)) {
						createNewStatementSequence(helper, seq, helper, autTrans.getLetter(), false);
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

	private static boolean areAllIncomingEdgesReturn(final BoogieIcfgLocation helper) {
		for (final IcfgEdge edge : helper.getIncomingEdges()) {
			if (!(edge instanceof Return)) {
				return false;
			}
		}
		return true;
	}

	private static boolean areAllDirectPredecessorsProductNodes(final BoogieIcfgLocation helper) {
		for (final IcfgLocation node : helper.getIncomingNodes()) {
			final BoogieIcfgLocation pre = (BoogieIcfgLocation) node;
			if (isNonProductNode(pre)) {
				return false;
			}
		}
		return true;
	}

	private static boolean areAllDirectSuccessorsNonProductNodes(final BoogieIcfgLocation helper) {
		for (final IcfgLocation node : helper.getOutgoingNodes()) {
			final BoogieIcfgLocation successor = (BoogieIcfgLocation) node;
			if (!isNonProductNode(successor)) {
				return false;
			}
		}
		return true;
	}

	private void removeProductProgramPointAndSuccessors(final BoogieIcfgLocation successor) {
		// removes the given product program point and all successors

		// first, collect all points that should be removed
		final Set<BoogieIcfgLocation> toRemove = new HashSet<>();
		final Deque<BoogieIcfgLocation> work = new LinkedList<>();
		work.add(successor);
		while (!work.isEmpty()) {
			final BoogieIcfgLocation current = work.removeFirst();
			if (toRemove.contains(current)) {
				continue;
			}
			toRemove.add(current);

			for (final IcfgEdge succ : current.getOutgoingEdges()) {
				work.addFirst((BoogieIcfgLocation) succ.getTarget());
			}
		}

		final BoogieIcfgContainer rootAnnot = mProductRoot;
		for (final BoogieIcfgLocation current : toRemove) {
			final DebugIdentifier name = current.getDebugIdentifier();
			// update annotations

			final Map<DebugIdentifier, BoogieIcfgLocation> prog2programPoints =
					rootAnnot.getProgramPoints().get(current.getProcedure());
			if (prog2programPoints != null) {
				prog2programPoints.remove(name);
			}

			rootAnnot.getLoopLocations().remove(current);

			final BoogieIcfgLocation entry = rootAnnot.getProcedureEntryNodes().get(current.getProcedure());
			if (current.equals(entry)) {
				rootAnnot.getProcedureEntryNodes().remove(current.getProcedure());
			}

			final BoogieIcfgLocation exit = rootAnnot.getProcedureExitNodes().get(current.getProcedure());
			if (current.equals(exit)) {
				rootAnnot.getProcedureExitNodes().remove(current.getProcedure());
			}

			if (ProductLocationNameGenerator.isHelperState(current)) {
				mHelperProductStates.remove(current);
			}
		}
	}

	private void generateTransFormulas() {
		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(mProductRoot, mServices, mSimplificationTechnique, mXnfConversionTechnique);

		final Set<Entry<String, Map<DebugIdentifier, BoogieIcfgLocation>>> programPoints =
				mProductRoot.getProgramPoints().entrySet();
		for (final Entry<String, Map<DebugIdentifier, BoogieIcfgLocation>> pairs : programPoints) {
			for (final Entry<DebugIdentifier, BoogieIcfgLocation> loc : pairs.getValue().entrySet()) {
				for (final IcfgEdge edge : loc.getValue().getOutgoingEdges()) {
					generateTransformula(tfb, pairs.getKey(), edge);
				}
			}
		}
	}

	private static void generateTransformula(final TransFormulaBuilder tfb, final String procId, final IcfgEdge edge) {
		if (edge instanceof StatementSequence || edge instanceof Summary) {
			tfb.addTransFormula((CodeBlock) edge, procId);
		}
	}

	private void handleEdgeStatementSequence(final BoogieIcfgLocation productLoc, final String nwaLoc,
			final StatementSequence rcfgEdge, final boolean isProgramStep) {
		BoogieIcfgLocation targetpp;
		// if this is a program step encode normal (crossproduct) else
		// stay in the same buchi state and append program flow
		if (isProgramStep) {
			for (final OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaLoc)) {
				// add no edges if this is not a program step or not the program flow
				targetpp = mProductLocations.get(ProductLocationNameGenerator
						.generateStateName((BoogieIcfgLocation) rcfgEdge.getTarget(), autTrans.getSucc()));
				// append statements of rcfg and ltl
				createNewStatementSequence(productLoc, rcfgEdge, targetpp, autTrans.getLetter(), isProgramStep);
			}
		} else {
			// add no edges if this is not a program step or not the program flow
			targetpp = mProductLocations.get(
					ProductLocationNameGenerator.generateStateName((BoogieIcfgLocation) rcfgEdge.getTarget(), nwaLoc));
			// append statements of rcfg and ltl
			createNewStatementSequence(productLoc, rcfgEdge, targetpp, null, isProgramStep);
		}

	}

	private void handleEdgeReturn(final BoogieIcfgLocation productLoc, final String nwaLoc, final Return returnEdge,
			final boolean isProgramStep) {
		// The calls used for the returns are dummy calls,
		// that have nothing common with the original
		// call except the caller location, that has to be
		// popped from the stack.
		// The target pp and call statement are never used
		// and therefore left blank

		// for all possible call origins: CallPP x LTLStates
		// be able to return to the helper state
		final BoogieIcfgLocation caller = returnEdge.getCallerProgramPoint();

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

		final BoogieIcfgLocation origRcfgTargetLoc = (BoogieIcfgLocation) returnEdge.getTarget();
		final DebugIdentifier helperName =
				mNameGenerator.generateHelperStateName(origRcfgTargetLoc.getDebugIdentifier());
		final BoogieIcfgLocation helper = createProductProgramPoint(helperName, origRcfgTargetLoc);

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
			BoogieIcfgLocation targetpp = mProductLocations
					.get(ProductLocationNameGenerator.generateStateName(origRcfgTargetLoc, autTrans.getSucc()));
			if (targetpp == null) {
				// returns may connect with multiple edges to a single state
				// that is part of the non-product states
				targetpp = mProductLocations.get(ProductLocationNameGenerator.generateStateName(origRcfgTargetLoc));
			}
			createNewStatementSequence(helper, null, targetpp, autTrans.getLetter(), isProgramStep);
		}
	}

	private void handleEdgeSummary(final BoogieIcfgLocation productSourceLoc, final String nwaLoc,
			final Summary summary) {
		// the summary edge in the original program should be concatenated with
		// each outgoing letter of the NWA and the resulting edges should be
		// inserted in the new NWA (happens automatically during construction)

		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(mProductRoot, mServices, mSimplificationTechnique, mXnfConversionTechnique);

		BoogieIcfgLocation targetpp;
		for (final OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaLoc)) {
			targetpp = mProductLocations.get(ProductLocationNameGenerator
					.generateStateName((BoogieIcfgLocation) summary.getTarget(), autTrans.getSucc()));
			final List<CodeBlock> sumAndSs = new ArrayList<>();
			final StatementSequence seq = mCodeblockFactory.constructStatementSequence(productSourceLoc, targetpp,
					checkLetter(autTrans.getLetter()), Origin.IMPLEMENTATION);

			tfb.addTransFormula(seq, ((BoogieIcfgLocation) summary.getSource()).getProcedure());

			sumAndSs.add(createNewSummaryEdge(productSourceLoc, summary, targetpp));
			sumAndSs.add(seq);

			mCodeblockFactory.constructSequentialComposition(productSourceLoc, targetpp, true, true, sumAndSs,
					mXnfConversionTechnique, mSimplificationTechnique);
		}
	}

	private void handleEdgeSummaryFromNonProduct(final BoogieIcfgLocation productSourceLoc, final Summary rcfgEdge) {
		final BoogieIcfgLocation origRcfgTargetLoc = (BoogieIcfgLocation) rcfgEdge.getTarget();
		for (final String initialNWAState : mNWA.getInitialStates()) {
			final BoogieIcfgLocation productTargetLoc = mProductLocations
					.get(ProductLocationNameGenerator.generateStateName(origRcfgTargetLoc, initialNWAState));
			createNewSummaryEdge(productSourceLoc, rcfgEdge, productTargetLoc);
		}

	}

	private void handleEdgeCall(final BoogieIcfgLocation productSourceLoc, final String nwaSourceState,
			final Call origRcfgEdge, final BoogieIcfgLocation origRcfgSourceLoc, final boolean isProgramStep) {

		final DebugIdentifier helperName =
				mNameGenerator.generateHelperStateName(productSourceLoc.getDebugIdentifier());
		final BoogieIcfgLocation origRcfgTargetLoc = (BoogieIcfgLocation) origRcfgEdge.getTarget();
		final BoogieIcfgLocation helper = createProductProgramPoint(helperName, origRcfgTargetLoc);

		createNewCallEdge(origRcfgSourceLoc, productSourceLoc, origRcfgEdge, helper);

		// From the helpernode, the original call target is
		// connected with a new
		// edge with the fitting assumption of the call. The
		// edge is calculated
		// like any other edge in the graph.
		for (final OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaSourceState)) {
			final BoogieIcfgLocation targetpp = mProductLocations
					.get(ProductLocationNameGenerator.generateStateName(origRcfgTargetLoc, autTrans.getSucc()));
			// if the transition would lead into another BA state and is no program step continue
			if (!isProgramStep && !autTrans.getSucc().equals(nwaSourceState)) {
				continue;
			}
			createNewStatementSequence(helper, null, targetpp, autTrans.getLetter(), isProgramStep);
		}
	}

	private void handleEdgeCallFromNonProduct(final BoogieIcfgLocation productSourceLoc, final Call origRcfgEdge,
			final BoogieIcfgLocation origRcfgSourceLoc) {
		final BoogieIcfgLocation origRcfgTargetLoc = (BoogieIcfgLocation) origRcfgEdge.getTarget();
		for (final String initialNWAState : mNWA.getInitialStates()) {
			final BoogieIcfgLocation productTargetLoc = mProductLocations
					.get(ProductLocationNameGenerator.generateStateName(origRcfgTargetLoc, initialNWAState));
			createNewCallEdge(origRcfgSourceLoc, productSourceLoc, origRcfgEdge, productTargetLoc);
		}
	}

	private Summary createNewSummaryEdge(final BoogieIcfgLocation productSourceLoc, final Summary origSummary,
			final BoogieIcfgLocation productTargetLoc) {
		assert productSourceLoc != null;
		assert productTargetLoc != null;
		final Summary sum = mCodeblockFactory.constructSummary(productSourceLoc, productTargetLoc,
				origSummary.getCallStatement(), false);
		sum.setTransitionFormula(origSummary.getTransformula());

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Created summary edge (" + productSourceLoc + ", " + productTargetLoc + ") for call "
					+ BoogiePrettyPrinter.print(origSummary.getCallStatement()));
		}
		return sum;
	}

	private Return createNewReturnEdge(final BoogieIcfgLocation productSourceLoc, final Return origRcfgEdge,
			final BoogieIcfgLocation productTargetLoc, final Call correspondingCall) {
		assert productSourceLoc != null;
		assert productTargetLoc != null;
		final Return returnEdge =
				mCodeblockFactory.constructReturn(productSourceLoc, productTargetLoc, correspondingCall);
		returnEdge.setTransitionFormula(origRcfgEdge.getTransformula());
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Created return edge (" + productSourceLoc + ", " + productTargetLoc + ") for call from "
					+ correspondingCall.getSource());
		}
		mapNewEdge2OldEdge(returnEdge, origRcfgEdge);
		return returnEdge;
	}

	private Call createNewCallEdge(final BoogieIcfgLocation origRcfgSourceLoc,
			final BoogieIcfgLocation productSourceLoc, final Call origRcfgEdge,
			final BoogieIcfgLocation productTargetLoc) {
		assert productSourceLoc != null;
		assert productTargetLoc != null;
		final Call call =
				mCodeblockFactory.constructCall(productSourceLoc, productTargetLoc, origRcfgEdge.getCallStatement());
		call.setTransitionFormula(origRcfgEdge.getTransformula());
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

	private BoogieIcfgLocation createProductProgramPoint(final DebugIdentifier debugIdentifier,
			final BoogieIcfgLocation originalState) {
		final BoogieIcfgLocation rtr = new BoogieIcfgLocation(debugIdentifier, originalState.getProcedure(), false,
				originalState.getBoogieASTNode());

		// update metadata
		Map<DebugIdentifier, BoogieIcfgLocation> prog2programPoints =
				mProductRoot.getProgramPoints().get(originalState.getProcedure());
		if (prog2programPoints == null) {
			prog2programPoints = new HashMap<>();
			mProductRoot.getProgramPoints().put(originalState.getProcedure(), prog2programPoints);
		}
		prog2programPoints.put(debugIdentifier, rtr);

		if (mProductRoot.getLoopLocations().remove(originalState)) {
			mProductRoot.getLoopLocations().add(rtr);
		}

		if (mProductRoot.getInitialNodes().remove(originalState)) {
			mProductRoot.getInitialNodes().add(rtr);
		}

		// TODO: It may happen that we have multiple entry points because of the
		// products; but we can currently only represent one. Do we need to do
		// something about that?

		final BoogieIcfgLocation entry = mProductRoot.getProcedureEntryNodes().get(originalState.getProcedure());
		if (entry != null && originalState == entry) {
			mProductRoot.getProcedureEntryNodes().put(originalState.getProcedure(), rtr);
		}

		final BoogieIcfgLocation exit = mProductRoot.getProcedureExitNodes().get(originalState.getProcedure());
		if (exit != null && originalState == exit) {
			mProductRoot.getProcedureExitNodes().put(originalState.getProcedure(), rtr);
		}

		if (ProductLocationNameGenerator.isHelperState(rtr)) {
			mHelperProductStates.add(rtr);
		}

		return rtr;
	}

	private StatementSequence createNewStatementSequence(final BoogieIcfgLocation currentpp,
			final StatementSequence originalSS, final BoogieIcfgLocation targetpp, final CodeBlock letter,
			final boolean isProgramStep) {
		final List<Statement> stmts = new ArrayList<>();
		if (originalSS != null) {
			stmts.addAll(originalSS.getStatements());
		}
		if (isProgramStep) {
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

	private void mapNewEdge2OldEdge(final IcfgEdge newEdge, final IcfgEdge originalEdge) {
		mBacktranslator.mapEdges(newEdge, originalEdge);
	}

	private static AssumeStatement generateNeverClaimAssumeStatement(final Expression expr) {
		return new AssumeStatement(null, expr);
	}
}
