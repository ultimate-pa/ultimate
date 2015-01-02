package de.uni_freiburg.informatik.ultimate.buchiprogramproduct;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;

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

	private final NestedWordAutomaton<CodeBlock, String> mNWA;
	private final RootNode mRCFG;
	private final HashSet<ProgramPoint> mRCFGLocations;

	private HashMap<String, ProgramPoint> mProductLocations;

	private RootNode mRootNode;

	private int mHelperUnifique = 0;

	private HashMap<ProgramPoint, ArrayList<Call>> mOrigRcfgCallLocs2CallEdges;

	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;
	private final ProductBacktranslator mBacktranslator;
	private HashSet<ProgramPoint> mRootSuccessorProgramPoints;

	public Product(NestedWordAutomaton<CodeBlock, String> aut, RootNode rcfg, LTLPropertyCheck ltlAnnot,
			IUltimateServiceProvider services, ProductBacktranslator backtrans) throws Exception {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mRCFGLocations = new HashSet<ProgramPoint>();
		mProductLocations = new HashMap<String, ProgramPoint>();
		mOrigRcfgCallLocs2CallEdges = new HashMap<ProgramPoint, ArrayList<Call>>();
		mRootSuccessorProgramPoints = new HashSet<>();
		mNWA = aut;
		mRCFG = rcfg;
		mBacktranslator = backtrans;

		// create the new root node
		mRootNode = new RootNode(mRCFG.getPayload().getLocation(), mRCFG.getRootAnnot());
		// the root annotation has to be updated to be accurate in the new RCFG
		// * getProgramPoints() will be refilled during calls to
		// createProgramPoint()
		mRootNode.getRootAnnot().getProgramPoints().clear();
		// * getLoopLocations(), getEntryNodes() and getExitNodes() will be
		// replaced during calls to
		// createProgramPoint(), so we just let it be

		// mark the root node with the current LTL property for possible counter
		// examples
		ltlAnnot.annotate(mRootNode);

		collectRCFGLocations();
		createProductStates();
		createEdges();
		generateTransFormula();
	}

	public RootNode getProductRCFG() {
		return mRootNode;
	}

	/**
	 * collect all states that are part of the RCFG into a List
	 */
	private void collectRCFGLocations() {
		LinkedHashSet<ProgramPoint> unhandledLocations = new LinkedHashSet<ProgramPoint>();

		for (RCFGEdge p : ((RootNode) mRCFG).getOutgoingEdges()) {
			unhandledLocations.add((ProgramPoint) p.getTarget());
		}
		// collect all Nodes in the RCFG for the product
		ProgramPoint currentPoint;
		while (!unhandledLocations.isEmpty()) {
			currentPoint = unhandledLocations.iterator().next();
			unhandledLocations.remove(currentPoint);
			mRCFGLocations.add(currentPoint);
			for (RCFGEdge p : currentPoint.getOutgoingEdges()) {
				if (p instanceof Summary) {
					continue;
				}
				if (!mRCFGLocations.contains(p.getTarget()) && !unhandledLocations.contains(p.getTarget())) {
					unhandledLocations.add((ProgramPoint) p.getTarget());
				}
			}
			// append selfloops to leafs of the rcfg
			if (currentPoint.getOutgoingEdges().size() == 0) {
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
		final BuchiProgramAcceptingStateAnnotation acceptingNodeAnnotation = new BuchiProgramAcceptingStateAnnotation();

		for (ProgramPoint origpp : mRCFGLocations) {

			if (isNonProductNode(origpp)) {
				ProgramPoint newPP = createProgramPoint(generateStateName(origpp.getLocationName(), null), origpp);
				mProductLocations.put(generateStateName(origpp.getLocationName(), null), newPP);
				continue;
			}

			for (String nwaState : mNWA.getStates()) {
				ProgramPoint newPP = createProgramPoint(generateStateName(origpp.getLocationName(), nwaState), origpp);
				mProductLocations.put(generateStateName(origpp.getLocationName(), nwaState), newPP);

				// accepting states (just check for AcceptingNodeAnnotation)
				if (mNWA.isFinal(nwaState)) {
					acceptingNodeAnnotation.annotate(newPP);
				}
			}
		}
	}

	private boolean isNonProductNode(ProgramPoint origpp) {
		String procname = origpp.getProcedure();
		return procname.equals("ULTIMATE.init") || procname.equals("ULTIMATE.start");
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
				mLogger.debug("Processing " + rcfgEdge.hashCode() + " " + rcfgEdge.getClass().getSimpleName());
				ProgramPoint origRcfgTargetLoc = (ProgramPoint) rcfgEdge.getTarget();
				if (isNonProductNode(origRcfgSourceLoc) && isNonProductNode(origRcfgTargetLoc)) {
					// if the current node and its target belong to ignored
					// procedures, just replicate the RCFG

					ProgramPoint productSourceLoc = mProductLocations.get(generateStateName(
							origRcfgSourceLoc.getLocationName(), null));
					ProgramPoint productTargetLoc = mProductLocations.get(generateStateName(
							origRcfgTargetLoc.getLocationName(), null));

					assert productSourceLoc != null;
					assert productTargetLoc != null;

					addRootEdgeIfNecessary(origRcfgSourceLoc, null, productSourceLoc);

					if (rcfgEdge instanceof StatementSequence) {
						createNewStatementSequence(productSourceLoc, (StatementSequence) rcfgEdge, productTargetLoc,
								null);
					} else if (rcfgEdge instanceof Call) {
						createNewCallEdge(origRcfgSourceLoc, productSourceLoc, (Call) rcfgEdge, productTargetLoc);
					} else if (rcfgEdge instanceof Return) {
						// we will handle return in a second iteration
					} else if (rcfgEdge instanceof Summary) {
						// we ignore summaries
					} else {
						throw new AssertionError("Did not expect edge of type " + rcfgEdge.getClass().getSimpleName());
					}

				} else if (isNonProductNode(origRcfgSourceLoc)) {
					// if the source is a non-product state and the target is
					// part of a real product state, we know that it has to be a
					// call edge
					// for this edge, we generate new call edges that link the
					// non-product state with all product states that are
					// initial states
					//
					ProgramPoint productSourceLoc = mProductLocations.get(generateStateName(
							origRcfgSourceLoc.getLocationName(), null));
					addRootEdgeIfNecessary(origRcfgSourceLoc, null, productSourceLoc);
					if (rcfgEdge instanceof Call) {
						handleEdgeCallFromNonProduct(productSourceLoc, (Call) rcfgEdge, origRcfgSourceLoc);
					} else {
						throw new AssertionError();
					}
				} else {
					// if the source is a product state, we know that either the
					// target is also a product state, or the target is a non
					// product state and the edge has to be an return
					// as we ignore return edges in this run, we just make the normal product
					for (String nwaLoc : mNWA.getStates()) {
						ProgramPoint productSourceLoc = mProductLocations.get(generateStateName(
								origRcfgSourceLoc.getLocationName(), nwaLoc));
						addRootEdgeIfNecessary(origRcfgSourceLoc, nwaLoc, productSourceLoc);

						if (rcfgEdge instanceof StatementSequence) {
							handleEdgeStatementSequence(productSourceLoc, nwaLoc, (StatementSequence) rcfgEdge);
						} else if (rcfgEdge instanceof Call) {
							handleEdgeCall(productSourceLoc, nwaLoc, (Call) rcfgEdge, origRcfgSourceLoc);
						} else if (rcfgEdge instanceof Return) {
							// we will handle return in a second iteration
						} else if (rcfgEdge instanceof Summary) {
							// we ignore summaries
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

				ProgramPoint origRcfgTargetLoc = (ProgramPoint) rcfgEdge.getTarget();
				if (isNonProductNode(origRcfgSourceLoc) && isNonProductNode(origRcfgTargetLoc)) {
					ProgramPoint productSourceLoc = mProductLocations.get(generateStateName(
							origRcfgSourceLoc.getLocationName(), null));
					ProgramPoint productTargetLoc = mProductLocations.get(generateStateName(
							origRcfgTargetLoc.getLocationName(), null));
					Return returnEdge = (Return) rcfgEdge;
					ArrayList<Call> correspondingCalls = mOrigRcfgCallLocs2CallEdges.get(returnEdge
							.getCallerProgramPoint());
					// there must be exactly one coressponding call, as this is
					// a return for an original call
					assert correspondingCalls.size() == 1;
					createNewReturnEdge(productSourceLoc, returnEdge, productTargetLoc, mOrigRcfgCallLocs2CallEdges
							.get(returnEdge.getCallerProgramPoint()).get(0));
				} else {
					for (String nwaLoc : mNWA.getStates()) {
						ProgramPoint productSourceLoc = mProductLocations.get(generateStateName(
								origRcfgSourceLoc.getLocationName(), nwaLoc));
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
				mapNewEdge2OldEdge(new RootEdge(mRootNode, productTargetLoc), null);
				mRootSuccessorProgramPoints.add(productTargetLoc);
			}
			return true;
		}
		return false;
	}

	private void generateTransFormula() {
		Boogie2SMT b2smt = mRootNode.getRootAnnot().getBoogie2SMT();
		RootAnnot rootAnnot = mRootNode.getRootAnnot();
		TransFormulaBuilder tfb = new TransFormulaBuilder(b2smt, mServices);

		for (String procIdent : rootAnnot.getBoogieDeclarations().getProcImplementation().keySet()) {
			// Procedure proc =
			// rootAnnot.getBoogieDeclarations().getProcImplementation().get(procIdent);
			// b2smt.declareLocals(proc);

			for (ProgramPoint node : rootAnnot.getProgramPoints().get(procIdent).values()) {
				if (node.getLocationName().startsWith("h_")) {
					mLogger.debug(node.getLocationName());
				}
				for (RCFGEdge edge : node.getOutgoingEdges()) {
					if (edge instanceof StatementSequence) {
						tfb.addTransitionFormulas((CodeBlock) edge, procIdent);
					}
				}
			}
			// b2smt.removeLocals(proc);
		}
	}

	private void handleEdgeStatementSequence(ProgramPoint productLoc, String nwaLoc, StatementSequence rcfgEdge) {
		ProgramPoint targetpp;
		for (OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaLoc)) {
			targetpp = mProductLocations.get(generateStateName(((ProgramPoint) rcfgEdge.getTarget()).getLocationName(),
					autTrans.getSucc().toString()));
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
		ProgramPoint helper = createProgramPoint(helperName, origRcfgTargetLoc);

		// for all possible call origins: CallPP x LTLStates
		// be able to return to the helper state
		ProgramPoint caller = ((ProgramPoint) returnEdge.getCallerProgramPoint());

		assert (caller != null);
		assert (mOrigRcfgCallLocs2CallEdges != null);
		assert (mOrigRcfgCallLocs2CallEdges.get(caller) != null);
		for (Call call : mOrigRcfgCallLocs2CallEdges.get(caller)) {
			createNewReturnEdge(productLoc, returnEdge, helper, call);
		}

		// From the helpernode, the original call target is
		// connected with a new
		// edge with the fitting assumption of the call. The
		// edge is calculated
		// like any other edge in the graph.
		for (OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaLoc)) {
			ProgramPoint targetpp = mProductLocations.get(generateStateName(origRcfgTargetLoc.getLocationName(),
					autTrans.getSucc().toString()));
			if (targetpp == null) {
				// returns may connect with multiple edges to a single state
				// that is part of the non-product states
				targetpp = mProductLocations.get(generateStateName(origRcfgTargetLoc.getLocationName(), null));
			}
			createNewStatementSequence(helper, null, targetpp, autTrans.getLetter());
		}
	}

	private void handleEdgeCall(ProgramPoint productSourceLoc, String nwaSourceState, Call origRcfgEdge,
			ProgramPoint origRcfgSourceLoc) {

		String helperName = generateHelperStateName(productSourceLoc.getPosition());
		ProgramPoint origRcfgTargetLoc = (ProgramPoint) origRcfgEdge.getTarget();
		ProgramPoint helper = createProgramPoint(helperName, origRcfgTargetLoc);

		createNewCallEdge(origRcfgSourceLoc, productSourceLoc, origRcfgEdge, helper);

		// From the helpernode, the original call target is
		// connected with a new
		// edge with the fitting assumption of the call. The
		// edge is calculated
		// like any other edge in the graph.
		for (OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaSourceState)) {
			ProgramPoint targetpp = mProductLocations.get(generateStateName(origRcfgTargetLoc.getLocationName(),
					autTrans.getSucc().toString()));
			createNewStatementSequence(helper, null, targetpp, autTrans.getLetter());
		}
	}

	private void handleEdgeCallFromNonProduct(ProgramPoint productSourceLoc, Call origRcfgEdge,
			ProgramPoint origRcfgSourceLoc) {

		ProgramPoint origRcfgTargetLoc = (ProgramPoint) origRcfgEdge.getTarget();
		for (String initialNWAState : mNWA.getInitialStates()) {
			ProgramPoint productTargetLoc = mProductLocations.get(generateStateName(
					origRcfgTargetLoc.getLocationName(), initialNWAState));
			createNewCallEdge(origRcfgSourceLoc, productSourceLoc, origRcfgEdge, productTargetLoc);
		}
	}

	private Return createNewReturnEdge(ProgramPoint productSourceLoc, Return origRcfgEdge,
			ProgramPoint productTargetLoc, Call correspondingCall) {
		assert productSourceLoc != null;
		assert productTargetLoc != null;
		Return r = new Return(productSourceLoc, productTargetLoc, correspondingCall, mLogger);
		r.setTransitionFormula(origRcfgEdge.getTransitionFormula());
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
		calls.add(call);

		return call;
	}

	private ProgramPoint createProgramPoint(String helperName, ProgramPoint originalState) {
		ProgramPoint rtr = new ProgramPoint(helperName, originalState.getProcedure(), false,
				originalState.getBoogieASTNode());

		// update annotations
		RootAnnot rootAnnot = mRootNode.getRootAnnot();
		Map<String, ProgramPoint> prog2programPoints = rootAnnot.getProgramPoints().get(originalState.getProcedure());
		if (prog2programPoints == null) {
			prog2programPoints = new HashMap<>();
			rootAnnot.getProgramPoints().put(originalState.getProcedure(), prog2programPoints);
		}
		prog2programPoints.put(helperName, rtr);

		ILocation currentLoopLoc = mRootNode.getRootAnnot().getLoopLocations().remove(originalState);
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

		// TODO: map the new statement sequence to the one from which it
		// originated (for backtranslation)
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
	private String generateStateName(String rcfgName, String nwaName) {
		if (nwaName == null) {
			return rcfgName;
		} else if (rcfgName.equals("ULTIMATE.startENTRY") && mNWA.isInitial(nwaName)) {
			return "ULTIMATE.start";
		} else {
			return rcfgName + "__" + nwaName;
		}
	}

	private String generateHelperStateName(String location) {
		mHelperUnifique++;
		return "crhelper" + Integer.toString(mHelperUnifique) + "_" + location;
	}

}
