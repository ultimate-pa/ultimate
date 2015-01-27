package de.uni_freiburg.informatik.ultimate.buchiprogramproduct;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.annot.BuchiProgramAcceptingStateAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
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
import de.uni_freiburg.informatik.ultimate.result.LTLPropertyCheck;

/**
 * This class is implementing the Buchi program product, multiplying a
 * BuchiAutomaton with the CFG.
 * 
 * @see Masterarbeit TODO Titel
 * 
 * @author Langenfeld
 * 
 */
public class Product {
	// constants
	private static final String sHelperStatePrefix = "crhelper";

	// readonly state
	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;
	private final ProductBacktranslator mBacktranslator;
	private final BuchiProgramAcceptingStateAnnotation mAcceptingNodeAnnotation;
	private final RootNode mRcfgRoot;
	private final RootNode mProductRoot;
	private final HashSet<ProgramPoint> mRCFGLocations;
	private final HashSet<ProgramPoint> mRcfgSinks;
	private final HashMap<String, ProgramPoint> mProductLocations;
	private final HashSet<ProgramPoint> mRootSuccessorProgramPoints;
	private final HashMap<ProgramPoint, ArrayList<Call>> mOrigRcfgCallLocs2CallEdges;
	private final NestedWordAutomaton<CodeBlock, String> mNWA;

	private final HashSet<ProgramPoint> mHelperProductStates;

	// state
	private int mHelperUnifique;

	public Product(NestedWordAutomaton<CodeBlock, String> aut, RootNode rcfg, LTLPropertyCheck ltlAnnot,
			IUltimateServiceProvider services, ProductBacktranslator backtrans) throws Exception {
		// services and logger
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		// REMOVE: Set logging to debug while coding
//		Level oldLevel = mLogger.getLevel();
//		mLogger.setLevel(Level.DEBUG);

		// parameters
		mNWA = aut;
		mRcfgRoot = rcfg;
		mBacktranslator = backtrans;

		// state
		mHelperUnifique = 0;
		mRCFGLocations = new HashSet<ProgramPoint>();
		mProductLocations = new HashMap<String, ProgramPoint>();
		mOrigRcfgCallLocs2CallEdges = new HashMap<ProgramPoint, ArrayList<Call>>();
		mRootSuccessorProgramPoints = new HashSet<>();
		mAcceptingNodeAnnotation = new BuchiProgramAcceptingStateAnnotation();
		mRcfgSinks = new HashSet<>();
		mHelperProductStates = new HashSet<>();

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
		collectRCFGLocations();
		createProductStates();
		createEdges();

		pruneNonProductEnd();

		generateTransFormula();
//		mLogger.setLevel(oldLevel);
	}

	public RootNode getProductRCFG() {
		return mProductRoot;
	}

	/**
	 * collect all states that are part of the RCFG into a List
	 */
	private void collectRCFGLocations() {
		LinkedHashSet<ProgramPoint> unhandledLocations = new LinkedHashSet<ProgramPoint>();

		for (RCFGEdge p : ((RootNode) mRcfgRoot).getOutgoingEdges()) {
			unhandledLocations.add((ProgramPoint) p.getTarget());
		}

		// collect all Nodes in the RCFG for the product
		ProgramPoint currentPoint;
		while (!unhandledLocations.isEmpty()) {
			currentPoint = unhandledLocations.iterator().next();
			unhandledLocations.remove(currentPoint);
			mRCFGLocations.add(currentPoint);
			for (RCFGEdge p : currentPoint.getOutgoingEdges()) {
				if (!mRCFGLocations.contains(p.getTarget()) && !unhandledLocations.contains(p.getTarget())) {
					unhandledLocations.add((ProgramPoint) p.getTarget());
				}
			}
			// collect all sinks and add self loops to them
			if (currentPoint.getOutgoingEdges().size() == 0) {
				mRcfgSinks.add(currentPoint);
				mapNewEdge2OldEdge(new StatementSequence(currentPoint, currentPoint,
						generateNeverClaimAssumeStatement(new BooleanLiteral(null, true)), mLogger), null);
			}
		}
	}

	/**
	 * Multiply states and make them available in the dictionary with their new
	 * name
	 */
	private void createProductStates() {

		for (ProgramPoint origpp : mRCFGLocations) {

			if (isNonProductNode(origpp)) {
				ProgramPoint newPP = createProductProgramPoint(generateStateName(origpp, null), origpp);
				updateProductStates(origpp, newPP, generateStateName(origpp, null));
				continue;
			}

			for (String nwaState : mNWA.getStates()) {
				ProgramPoint newPP = createProductProgramPoint(generateStateName(origpp, nwaState), origpp);
				updateProductStates(origpp, newPP, generateStateName(origpp, nwaState));

				// accepting states are marked with AcceptingNodeAnnotation
				if (mNWA.isFinal(nwaState)) {
					mAcceptingNodeAnnotation.annotate(newPP);
				}
			}
		}
	}

	private void updateProductStates(ProgramPoint origpp, ProgramPoint newPP, String statename) {
		String locname = newPP.getLocationName();
		assert statename.equals(locname);
		ProgramPoint rtr = mProductLocations.put(newPP.getLocationName(), newPP);
		if (rtr != null) {
			throw new AssertionError("The original RCFG had two locations with the same location name");
		}
	}

	/**
	 * Sinks are always product nodes Nodes belonging to certain procedures may
	 * not be product nodes
	 * 
	 */
	private boolean isNonProductNode(ProgramPoint origpp) {
		String procname = origpp.getProcedure();
		return (procname.equals("ULTIMATE.init") || procname.equals("ULTIMATE.start"));
	}

	/**
	 * creates the crossproduct of all edges of every node of both automata
	 * 
	 * @throws Exception
	 */
	private void createEdges() throws Exception {

		// first, do everything except return edges
		for (ProgramPoint origRcfgSourceLoc : mRCFGLocations) {
			for (RCFGEdge rcfgEdge : origRcfgSourceLoc.getOutgoingEdges()) {
				if (rcfgEdge instanceof Summary) {
					// we ignore summaries
					// TODO: But we should not! under certain circumstances
					// summaries are important.
					// Use them like statement sequences; their transformula is
					// the place were we put the jucy stuff
					// repairing their call may be difficult
					// Summary summaryEdge = (Summary) rcfgEdge;
					// Summary annot = summaryEdge;
					// if (annot.calledProcedureHasImplementation()) {
					// //do nothing if analysis is interprocedural
					// //add summary otherwise
					// if (!m_Interprocedural) {
					// internalAlphabet.add(annot);
					// }
					// }
					// else {
					// internalAlphabet.add(annot);
					// }
					continue;
				}

				if (rcfgEdge instanceof Return) {
					// we will handle return in a second iteration
					continue;
				}

				mLogger.debug("Processing " + rcfgEdge.hashCode() + " " + rcfgEdge.getClass().getSimpleName());
				ProgramPoint origRcfgTargetLoc = (ProgramPoint) rcfgEdge.getTarget();
				if (isNonProductNode(origRcfgSourceLoc) && isNonProductNode(origRcfgTargetLoc)) {
					// if the current node and its target belong to ignored
					// procedures, just replicate the RCFG

					ProgramPoint productSourceLoc = mProductLocations.get(generateStateName(origRcfgSourceLoc, null));
					ProgramPoint productTargetLoc = mProductLocations.get(generateStateName(origRcfgTargetLoc, null));
					assert productSourceLoc != null;
					assert productTargetLoc != null;

					addRootEdgeIfNecessary(origRcfgSourceLoc, null, productSourceLoc);

					if (rcfgEdge instanceof StatementSequence) {
						createNewStatementSequence(productSourceLoc, (StatementSequence) rcfgEdge, productTargetLoc,
								null);
					} else if (rcfgEdge instanceof Call) {
						createNewCallEdge(origRcfgSourceLoc, productSourceLoc, (Call) rcfgEdge, productTargetLoc);
					} else {
						throw new AssertionError("Did not expect edge of type " + rcfgEdge.getClass().getSimpleName());
					}

				} else if (isNonProductNode(origRcfgSourceLoc)) {
					// if the source is a non-product state and the target is
					// part of a real product state, we know that it has to be a
					// call edge or an edge to a sink state.
					// if its a call edge, we generate new call edges that link
					// the non-product state with all product states that are
					// initial states (because we enter the part were we observe
					// the property)
					// if its a edge to a sink state its slightly more
					// complicated:
					//
					ProgramPoint productSourceLoc = mProductLocations.get(generateStateName(origRcfgSourceLoc, null));
					addRootEdgeIfNecessary(origRcfgSourceLoc, null, productSourceLoc);
					if (rcfgEdge instanceof Call) {
						handleEdgeCallFromNonProduct(productSourceLoc, (Call) rcfgEdge, origRcfgSourceLoc);
					} else {
						throw new AssertionError();
					}
				} else if (isNonProductNode(origRcfgTargetLoc)) {
					throw new AssertionError();
				} else {

					// if the source is a product state, we know that either the
					// target is also a product state, or the target is a non
					// product state and the edge has to be an return
					// as we ignore return edges in this run, we just make the
					// normal product
					for (String nwaLoc : mNWA.getStates()) {
						ProgramPoint productSourceLoc = mProductLocations.get(generateStateName(origRcfgSourceLoc,
								nwaLoc));
						addRootEdgeIfNecessary(origRcfgSourceLoc, nwaLoc, productSourceLoc);

						if (rcfgEdge instanceof StatementSequence) {
							handleEdgeStatementSequence(productSourceLoc, nwaLoc, (StatementSequence) rcfgEdge);
						} else if (rcfgEdge instanceof Call) {
							handleEdgeCall(productSourceLoc, nwaLoc, (Call) rcfgEdge, origRcfgSourceLoc);
						} else {
							// we encounted an unhandled edge type and have
							// to abort
							throw new UnsupportedOperationException(
									"BuchiProgramProduct does not support RCFGEdges of type "
											+ rcfgEdge.getClass().getSimpleName());
						}
					}
				}
			}
		}

		// second, handle all return edges
		for (ProgramPoint origRcfgSourceLoc : mRCFGLocations) {
			for (RCFGEdge rcfgEdge : origRcfgSourceLoc.getOutgoingEdges()) {
				if (!(rcfgEdge instanceof Return)) {
					// skip all edges that are not return edges
					continue;
				}
				mLogger.debug("Handling return edge from " + rcfgEdge.getSource() + " to " + rcfgEdge.getTarget());

				ProgramPoint origRcfgTargetLoc = (ProgramPoint) rcfgEdge.getTarget();
				if (isNonProductNode(origRcfgSourceLoc) && isNonProductNode(origRcfgTargetLoc)) {
					// handle all return edges in the non-product part
					ProgramPoint productSourceLoc = mProductLocations.get(generateStateName(origRcfgSourceLoc, null));
					ProgramPoint productTargetLoc = mProductLocations.get(generateStateName(origRcfgTargetLoc, null));
					Return returnEdge = (Return) rcfgEdge;
					ArrayList<Call> correspondingCalls = mOrigRcfgCallLocs2CallEdges.get(returnEdge
							.getCallerProgramPoint());
					// there must be exactly one corresponding call, as this is
					// a return for an original call
					assert correspondingCalls.size() == 1;
					createNewReturnEdge(productSourceLoc, returnEdge, productTargetLoc, mOrigRcfgCallLocs2CallEdges
							.get(returnEdge.getCallerProgramPoint()).get(0));
				} else if (!isNonProductNode(origRcfgSourceLoc) && !isNonProductNode(origRcfgTargetLoc)) {
					for (String nwaLoc : mNWA.getStates()) {
						ProgramPoint productSourceLoc = mProductLocations.get(generateStateName(origRcfgSourceLoc,
								nwaLoc));
						handleEdgeReturn(productSourceLoc, nwaLoc, (Return) rcfgEdge);
					}
				} else {
					// String source = "source " +
					// (isNonProductNode(origRcfgSourceLoc) ? "nonprod" :
					// "prod");
					// String target = "target " +
					// (isNonProductNode(origRcfgTargetLoc) ? "nonprod" :
					// "prod");
					// throw new AssertionError(source + " " + target);

					for (String nwaLoc : mNWA.getStates()) {
						ProgramPoint productSourceLoc = mProductLocations.get(generateStateName(origRcfgSourceLoc,
								nwaLoc));
						handleEdgeReturn(productSourceLoc, nwaLoc, (Return) rcfgEdge);
					}
				}
			}
		}
	}

	private boolean addRootEdgeIfNecessary(ProgramPoint origRcfgSourceLoc, String nwaState,
			ProgramPoint productTargetLoc) {
		if (origRcfgSourceLoc.getIncomingEdges().size() == 1
				&& origRcfgSourceLoc.getIncomingEdges().get(0) instanceof RootEdge
				&& (nwaState == null || mNWA.isInitial(nwaState))) {
			assert productTargetLoc != null;
			if (!mRootSuccessorProgramPoints.contains(productTargetLoc)) {
				mapNewEdge2OldEdge(new RootEdge(mProductRoot, productTargetLoc), null);
				mRootSuccessorProgramPoints.add(productTargetLoc);
			}
			return true;
		}
		return false;
	}

	private void pruneNonProductEnd() {
		// all helper states that have edges to non-product states receive a
		// self-loop that keeps them in the same product state as the LTL NWA

		for (ProgramPoint helper : mHelperProductStates) {

			// we only consider helpers that lead from product parts to
			// non-product parts, and those helpers have only return edges as
			// incoming edge
			if (!areAllIncomingEdgesReturn(helper) || !areAllDirectPredecessorsProductNodes(helper)
					|| !areAllDirectSuccessorsNonProductNodes(helper)) {
				continue;
			}

			ArrayList<RCFGEdge> outEdges = new ArrayList<>(helper.getOutgoingEdges());
			HashSet<RCFGNode> successors = new HashSet<>(helper.getOutgoingNodes());
			HashSet<RCFGNode> predecessors = new HashSet<>(helper.getIncomingNodes());

			for (RCFGEdge outgoing : outEdges) {
				// remove all outgoing edges
				outgoing.disconnectSource();
				outgoing.disconnectTarget();
			}

			// remove the targets and all the nodes that can be reached from the
			// target
			for (RCFGNode successor : successors) {
				removeProductProgramPointAndSuccessors((ProgramPoint) successor);
			}

			// we add a self loop that will be used later
			StatementSequence ss = new StatementSequence(helper, helper,
					generateNeverClaimAssumeStatement(new BooleanLiteral(null, true)), mLogger);
			mapNewEdge2OldEdge(ss, null);

			// determine what kind of loop has to be added to this state based
			// on the LTL NWA state of the predecessor
			boolean added = false;
			for (String nwaState : mNWA.getStates()) {
				for (RCFGNode node : predecessors) {
					ProgramPoint predecessor = (ProgramPoint) node;
					if (predecessor.getPosition().endsWith(nwaState)) {
						// ok, the predecessor is from this node; now we add
						// self
						// loops to the helper state that keep us in this NWA
						// state

						for (OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaState)) {
							if (autTrans.getSucc().equals(nwaState)) {
								createNewStatementSequence(helper, ss, helper, autTrans.getLetter());
								added = true;
							}
						}

						if (mNWA.isFinal(nwaState)) {
							// and if the nwa state is accepting, this state
							// will
							// also be accepting
							mAcceptingNodeAnnotation.annotate(helper);
						}
					}
				}
			}
			// hacky shit: the ss is now useless; we remove it
			if (added) {
				ss.disconnectSource();
				ss.disconnectTarget();
			}
		}

	}

	private boolean areAllIncomingEdgesReturn(ProgramPoint helper) {
		for (RCFGEdge edge : helper.getIncomingEdges()) {
			if (!(edge instanceof Return)) {
				return false;
			}
		}
		return true;
	}

	private boolean areAllDirectPredecessorsProductNodes(ProgramPoint helper) {
		for (RCFGNode node : helper.getIncomingNodes()) {
			ProgramPoint pre = (ProgramPoint) node;
			if (isNonProductNode(pre)) {
				return false;
			}
		}
		return true;
	}

	private boolean areAllDirectSuccessorsNonProductNodes(ProgramPoint helper) {
		for (RCFGNode node : helper.getOutgoingNodes()) {
			ProgramPoint successor = (ProgramPoint) node;
			if (!isNonProductNode(successor)) {
				return false;
			}
		}
		return true;
	}

	private void removeProductProgramPointAndSuccessors(ProgramPoint successor) {
		// removes the given product program point and all successors

		// first, collect all points that should be removed
		HashSet<ProgramPoint> toRemove = new HashSet<>();
		LinkedList<ProgramPoint> work = new LinkedList<>();
		work.add(successor);
		while (!work.isEmpty()) {
			ProgramPoint current = work.removeFirst();
			if (toRemove.contains(current)) {
				continue;
			}
			toRemove.add(current);

			for (RCFGEdge succ : current.getOutgoingEdges()) {
				work.addFirst((ProgramPoint) succ.getTarget());
			}
		}

		RootAnnot rootAnnot = mProductRoot.getRootAnnot();
		for (ProgramPoint current : toRemove) {
			String name = current.getLocationName();
			// update annotations

			Map<String, ProgramPoint> prog2programPoints = rootAnnot.getProgramPoints().get(current.getProcedure());
			if (prog2programPoints != null) {
				prog2programPoints.remove(name);
			}

			rootAnnot.getLoopLocations().remove(current);

			ProgramPoint entry = rootAnnot.getEntryNodes().get(current.getProcedure());
			if (entry == current) {
				rootAnnot.getEntryNodes().remove(current.getProcedure());
			}

			ProgramPoint exit = rootAnnot.getExitNodes().get(current.getProcedure());
			if (exit == current) {
				rootAnnot.getExitNodes().remove(current);
			}

			if (name.startsWith(sHelperStatePrefix)) {
				mHelperProductStates.remove(current);
			}
		}

	}

	private void generateTransFormula() {
		Boogie2SMT b2smt = mProductRoot.getRootAnnot().getBoogie2SMT();
		RootAnnot rootAnnot = mProductRoot.getRootAnnot();
		TransFormulaBuilder tfb = new TransFormulaBuilder(b2smt, mServices);

		for (Entry<String, Map<String, ProgramPoint>> pairs : rootAnnot.getProgramPoints().entrySet()) {
			for (ProgramPoint pp : pairs.getValue().values()) {
				for (RCFGEdge edge : pp.getOutgoingEdges()) {
					if (edge instanceof StatementSequence) {
						tfb.addTransitionFormulas((CodeBlock) edge, pairs.getKey());
						assert ((StatementSequence) edge).getTransitionFormula() != null;
					}
				}
			}
		}
	}

	private void handleEdgeStatementSequence(ProgramPoint productLoc, String nwaLoc, StatementSequence rcfgEdge) {
		ProgramPoint targetpp;
		for (OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaLoc)) {
			targetpp = mProductLocations.get(generateStateName(((ProgramPoint) rcfgEdge.getTarget()), autTrans
					.getSucc().toString()));
			// append statements of rcfg and ltl
			createNewStatementSequence(productLoc, rcfgEdge, targetpp, autTrans.getLetter());
		}
	}

	private void handleEdgeReturn(ProgramPoint productLoc, String nwaLoc, Return returnEdge) {
		// The calls used for the returns are dummy calls,
		// that have nothing common with the original
		// call except the caller location, that has to be
		// popped from the stack.
		// The target pp and call statement are never used
		// and therefore left blank
		ProgramPoint origRcfgTargetLoc = (ProgramPoint) returnEdge.getTarget();
		String helperName = generateHelperStateName(origRcfgTargetLoc.getPosition());
		ProgramPoint helper = createProductProgramPoint(helperName, origRcfgTargetLoc);

		// for all possible call origins: CallPP x LTLStates
		// be able to return to the helper state
		ProgramPoint caller = ((ProgramPoint) returnEdge.getCallerProgramPoint());

		assert (caller != null);
		assert (mOrigRcfgCallLocs2CallEdges != null);

		if (mOrigRcfgCallLocs2CallEdges.get(caller) == null) {
			// this seems to be a pathological case; we inspect it closer, but
			// we do not add a return edge!
			Call correspondingCall = returnEdge.getCorrespondingCall();
			mLogger.warn("Ignoring return edge from " + returnEdge.getSource() + " to " + returnEdge.getTarget()
					+ " (Corresponding call: " + correspondingCall + " from " + correspondingCall.getSource() + ")");

			return;
		}

		for (Call call : mOrigRcfgCallLocs2CallEdges.get(caller)) {
			createNewReturnEdge(productLoc, returnEdge, helper, call);
		}

		// From the helpernode, the original call target is
		// connected with a new
		// edge with the fitting assumption of the call. The
		// edge is calculated
		// like any other edge in the graph.
		for (OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaLoc)) {
			ProgramPoint targetpp = mProductLocations.get(generateStateName(origRcfgTargetLoc, autTrans.getSucc()
					.toString()));
			if (targetpp == null) {
				// returns may connect with multiple edges to a single state
				// that is part of the non-product states
				targetpp = mProductLocations.get(generateStateName(origRcfgTargetLoc, null));
			}
			createNewStatementSequence(helper, null, targetpp, autTrans.getLetter());
		}
	}

	private void handleEdgeCall(ProgramPoint productSourceLoc, String nwaSourceState, Call origRcfgEdge,
			ProgramPoint origRcfgSourceLoc) {

		String helperName = generateHelperStateName(productSourceLoc.getPosition());
		ProgramPoint origRcfgTargetLoc = (ProgramPoint) origRcfgEdge.getTarget();
		ProgramPoint helper = createProductProgramPoint(helperName, origRcfgTargetLoc);

		createNewCallEdge(origRcfgSourceLoc, productSourceLoc, origRcfgEdge, helper);

		// From the helpernode, the original call target is
		// connected with a new
		// edge with the fitting assumption of the call. The
		// edge is calculated
		// like any other edge in the graph.
		for (OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaSourceState)) {
			ProgramPoint targetpp = mProductLocations.get(generateStateName(origRcfgTargetLoc, autTrans.getSucc()
					.toString()));
			createNewStatementSequence(helper, null, targetpp, autTrans.getLetter());
		}
	}

	private void handleEdgeCallFromNonProduct(ProgramPoint productSourceLoc, Call origRcfgEdge,
			ProgramPoint origRcfgSourceLoc) {

		ProgramPoint origRcfgTargetLoc = (ProgramPoint) origRcfgEdge.getTarget();
		for (String initialNWAState : mNWA.getInitialStates()) {
			ProgramPoint productTargetLoc = mProductLocations
					.get(generateStateName(origRcfgTargetLoc, initialNWAState));
			createNewCallEdge(origRcfgSourceLoc, productSourceLoc, origRcfgEdge, productTargetLoc);
		}
	}

	private Return createNewReturnEdge(ProgramPoint productSourceLoc, Return origRcfgEdge,
			ProgramPoint productTargetLoc, Call correspondingCall) {
		assert productSourceLoc != null;
		assert productTargetLoc != null;
		Return r = new Return(productSourceLoc, productTargetLoc, correspondingCall, mLogger);
		r.setTransitionFormula(origRcfgEdge.getTransitionFormula());
		mLogger.debug("Created return edge (" + productSourceLoc + ", " + productTargetLoc + ") for call from "
				+ correspondingCall.getSource());

		mapNewEdge2OldEdge(r, origRcfgEdge);
		return r;
	}

	private Call createNewCallEdge(ProgramPoint origRcfgSourceLoc, ProgramPoint productSourceLoc, Call origRcfgEdge,
			ProgramPoint productTargetLoc) {
		assert productSourceLoc != null;
		assert productTargetLoc != null;
		Call call = new Call(productSourceLoc, productTargetLoc, origRcfgEdge.getCallStatement(), mLogger);
		call.setTransitionFormula(origRcfgEdge.getTransitionFormula());
		mapNewEdge2OldEdge(call, origRcfgEdge);

		// store all call edges in hashmap for the handling of return edges
		// later on
		ArrayList<Call> calls = mOrigRcfgCallLocs2CallEdges.get(origRcfgSourceLoc);
		if (calls == null) {
			calls = new ArrayList<>();
			mOrigRcfgCallLocs2CallEdges.put(origRcfgSourceLoc, calls);
		}
		mLogger.debug("Adding call to " + call + " for " + productSourceLoc + ", " + productTargetLoc + " under "
				+ origRcfgSourceLoc);
		calls.add(call);

		return call;
	}

	private ProgramPoint createProductProgramPoint(String stateName, ProgramPoint originalState) {
		ProgramPoint rtr = new ProgramPoint(stateName, originalState.getProcedure(), false,
				originalState.getBoogieASTNode());

		// update annotations
		RootAnnot rootAnnot = mProductRoot.getRootAnnot();
		Map<String, ProgramPoint> prog2programPoints = rootAnnot.getProgramPoints().get(originalState.getProcedure());
		if (prog2programPoints == null) {
			prog2programPoints = new HashMap<>();
			rootAnnot.getProgramPoints().put(originalState.getProcedure(), prog2programPoints);
		}
		prog2programPoints.put(stateName, rtr);

		ILocation currentLoopLoc = mProductRoot.getRootAnnot().getLoopLocations().remove(originalState);
		if (currentLoopLoc != null) {
			rootAnnot.getLoopLocations().put(rtr, currentLoopLoc);
		}

		// TODO: It may happen that we have multiple entry points because of the
		// products; but we can currently only represent one. Do we need to do
		// something about that?

		ProgramPoint entry = rootAnnot.getEntryNodes().get(originalState.getProcedure());
		if (entry != null) {
			rootAnnot.getEntryNodes().put(originalState.getProcedure(), rtr);
		}

		ProgramPoint exit = rootAnnot.getExitNodes().get(originalState.getProcedure());
		if (exit != null) {
			rootAnnot.getExitNodes().put(originalState.getProcedure(), rtr);
		}

		if (stateName.startsWith(sHelperStatePrefix)) {
			mHelperProductStates.add(rtr);
		}

		return rtr;
	}

	private StatementSequence createNewStatementSequence(ProgramPoint currentpp, StatementSequence originalSS,
			ProgramPoint targetpp, CodeBlock letter) {
		ArrayList<Statement> stmts = new ArrayList<Statement>();
		if (originalSS != null) {
			stmts.addAll(originalSS.getStatements());
		}
		if (letter != null) {
			if (letter instanceof StatementSequence) {
				StatementSequence autTransStmts = (StatementSequence) letter;
				stmts.addAll(autTransStmts.getStatements());
			} else {
				throw new UnsupportedOperationException("Letter has to be a statement sequence, but is "
						+ letter.getClass().getSimpleName());
			}
		}

		// create the edge
		StatementSequence newSS;
		assert currentpp != null;
		assert targetpp != null;
		if (originalSS != null) {
			newSS = new StatementSequence(currentpp, targetpp, stmts, originalSS.getOrigin(), mLogger);
		} else {
			newSS = new StatementSequence(currentpp, targetpp, stmts, Origin.IMPLEMENTATION, mLogger);
		}

		mapNewEdge2OldEdge(newSS, originalSS);
		return newSS;
	}

	private void mapNewEdge2OldEdge(RCFGEdge newEdge, RCFGEdge originalEdge) {
		mBacktranslator.mapEdges(newEdge, originalEdge);
	}

	private AssumeStatement generateNeverClaimAssumeStatement(Expression expr) {
		AssumeStatement neverClaimStmt = new AssumeStatement(null, expr);
		return neverClaimStmt;
	}

	/**
	 * Central method to create the product state's names form: P_name __
	 * Aut_name
	 * 
	 * @param rcfgName
	 *            Name of the state in the RCFG
	 * @param nwaName
	 *            Name of the state in the BA / NWA
	 * @return
	 */
	private String generateStateName(ProgramPoint pp, String nwaName) {
		// TODO: It seems that there is a bug in the rcfg builder routine s.t.
		// some locations can have the same name
		return generateStateName(String.valueOf(pp.hashCode()), nwaName);
		// return generateStateName(pp.getLocationName(), nwaName);
	}

	private String generateStateName(String rcfgName, String nwaName) {
		assert nwaName == null || !nwaName.isEmpty();
		if (nwaName == null) {
			return "NP" + "__" + rcfgName;
		} else if (rcfgName.equals("ULTIMATE.startENTRY") && mNWA.isInitial(nwaName)) {
			return "ULTIMATE.start";
		} else {
			return rcfgName + "__" + nwaName;
		}
	}

	private String generateHelperStateName(String location) {
		mHelperUnifique++;
		return sHelperStatePrefix + Integer.toString(mHelperUnifique) + "__" + location;
	}

}
