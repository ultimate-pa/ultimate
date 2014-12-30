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

	private HashMap<ProgramPoint, ArrayList<Call>> mCallEdges;

	private final Logger mLogger;
	private final IUltimateServiceProvider mServices;
	private final ProductBacktranslator mBacktranslator;

	public Product(NestedWordAutomaton<CodeBlock, String> aut, RootNode rcfg, LTLPropertyCheck ltlAnnot,
			IUltimateServiceProvider services, ProductBacktranslator backtrans) throws Exception {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mRCFGLocations = new HashSet<ProgramPoint>();
		mProductLocations = new HashMap<String, ProgramPoint>();
		mCallEdges = new HashMap<ProgramPoint, ArrayList<Call>>();
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
			for (String nwaState : mNWA.getStates()) {
				ProgramPoint newPP = createProgramPoint(generateStateName(origpp.getLocationName(), nwaState), origpp);
				mProductLocations.put(generateStateName(origpp.getLocationName(), nwaState), newPP);

				// accepting states (just check for AcceptingNodeAnnotation)
				if (mNWA.isFinal(nwaState)) {
					acceptingNodeAnnotation.annotate(newPP);
				}

				// inital states
				if (origpp.getLocationName().equals("ULTIMATE.startENTRY") && mNWA.isInitial(nwaState)) {
					mapNewEdge2OldEdge(new RootEdge(mRootNode, newPP), null);
					mRootNode.getRootAnnot().getEntryNodes().put("ULTIMATE.start", newPP);
				}
			}
		}
	}

	/**
	 * creates the crossproduct of all edges of every node of both automata
	 * 
	 * @throws Exception
	 */
	private void createEdges() throws Exception {

		// first, do everything except return edges
		for (ProgramPoint origRcfgLoc : mRCFGLocations) {
			for (String nwaLoc : mNWA.getStates()) {
				ProgramPoint productLoc = mProductLocations
						.get(generateStateName(origRcfgLoc.getLocationName(), nwaLoc));
				// For Edge of Node x Edge of node
				for (RCFGEdge rcfgEdge : origRcfgLoc.getOutgoingEdges()) {
					if (rcfgEdge instanceof Call) {
						handleEdgeCall(productLoc, (Call) rcfgEdge, origRcfgLoc, nwaLoc);
					} else if (rcfgEdge instanceof StatementSequence) {
						handleEdgeStatementSequence(productLoc, nwaLoc, (StatementSequence) rcfgEdge);
					} else if (rcfgEdge instanceof Summary) {
						// we ignore summaries
						continue;
					} else if (rcfgEdge instanceof Return) {
						// we will handle return in a second iteration
						continue;
					} else {
						// we encounted an unhandled edge type and have to abort
						throw new UnsupportedOperationException(
								"BuchiProgramProduct does not support RCFGEdges of type "
										+ rcfgEdge.getClass().getSimpleName());
					}
				}
			}
		}

		// second, handle all return edges
		for (ProgramPoint origRcfgLoc : mRCFGLocations) {
			for (String nwaLoc : mNWA.getStates()) {
				ProgramPoint productLoc = mProductLocations
						.get(generateStateName(origRcfgLoc.getLocationName(), nwaLoc));
				// For Edge of Node x Edge of node
				for (RCFGEdge rcfgEdge : origRcfgLoc.getOutgoingEdges()) {
					if (rcfgEdge instanceof Return) {
						handleEdgeReturn((Return) rcfgEdge, productLoc, nwaLoc);
					}
				}
			}
		}
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
			createNewStatementSequence(productLoc, rcfgEdge, targetpp, autTrans);
		}
	}

	private void handleEdgeReturn(Return returnEdge, ProgramPoint productLoc, String nwaLoc) {
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
		assert (mCallEdges != null);
		assert (mCallEdges.get(caller) != null);
		for (Call call : mCallEdges.get(caller)) {
			Return r = new Return(productLoc, helper, call, mLogger);
			r.setTransitionFormula(returnEdge.getTransitionFormula());
			mapNewEdge2OldEdge(r, returnEdge);
		}

		// From the helpernode, the original call target is
		// connected with a new
		// edge with the fitting assumption of the call. The
		// edge is calculated
		// like any other edge in the graph.
		for (OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaLoc)) {
			ProgramPoint targetpp = mProductLocations.get(generateStateName(origRcfgTargetLoc.getLocationName(),
					autTrans.getSucc().toString()));
			createNewStatementSequence(helper, null, targetpp, autTrans);
		}
	}

	private void handleEdgeCall(ProgramPoint productLoc, Call rcfgEdge, ProgramPoint origRcfgLoc, String nwaState) {

		String helperName = generateHelperStateName(mHelperUnifique + productLoc.getPosition());
		ProgramPoint origRcfgTargetLoc = (ProgramPoint) rcfgEdge.getTarget();
		ProgramPoint helper = createProgramPoint(helperName, origRcfgTargetLoc);

		Call call = new Call(productLoc, helper, rcfgEdge.getCallStatement(), mLogger);
		call.setTransitionFormula(rcfgEdge.getTransitionFormula());
		mapNewEdge2OldEdge(call, rcfgEdge);

		// store all call edges in hashmap for the handling of return edges
		// later on
		ArrayList<Call> calls = mCallEdges.get(origRcfgLoc);
		if (calls == null) {
			calls = new ArrayList<>();
			mCallEdges.put(origRcfgLoc, calls);
		}
		calls.add(call);

		// From the helpernode, the original call target is
		// connected with a new
		// edge with the fitting assumption of the call. The
		// edge is calculated
		// like any other edge in the graph.
		for (OutgoingInternalTransition<CodeBlock, String> autTrans : mNWA.internalSuccessors(nwaState)) {
			ProgramPoint targetpp = mProductLocations.get(generateStateName(origRcfgTargetLoc.getLocationName(),
					autTrans.getSucc().toString()));
			createNewStatementSequence(helper, null, targetpp, autTrans);
		}
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

	private void createNewStatementSequence(ProgramPoint currentpp, StatementSequence originalSS,
			ProgramPoint targetpp, OutgoingInternalTransition<CodeBlock, String> autTrans) {
		ArrayList<Statement> stmts = new ArrayList<Statement>();
		if (originalSS != null) {
			stmts.addAll(originalSS.getStatements());
		}
		if (autTrans != null) {
			if (autTrans.getLetter() instanceof StatementSequence) {
				StatementSequence autTransStmts = (StatementSequence) autTrans.getLetter();
				stmts.addAll(autTransStmts.getStatements());
			} else {
				if (autTrans.getLetter() == null) {
					throw new NullPointerException("Letter has to be a statement sequence, but is null");
				} else {
					throw new UnsupportedOperationException("Letter has to be a statement sequence, but is "
							+ autTrans.getLetter().getClass().getSimpleName());
				}
			}

			// TODO: autTrans is a codeblock, aka a statement sequence
			// stmts.add(generateNeverClaimAssumeStatement(autTrans));
		}

		// create the edge
		StatementSequence newSS;
		if (originalSS != null) {
			newSS = new StatementSequence(currentpp, targetpp, stmts, originalSS.getOrigin(), mLogger);
		} else {
			newSS = new StatementSequence(currentpp, targetpp, stmts, Origin.IMPLEMENTATION, mLogger);
		}

		// TODO: map the new statement sequence to the one from which it
		// originated (for backtranslation)
		mapNewEdge2OldEdge(newSS, originalSS);
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
	 * @param name1
	 *            Name of the state in the RCFG
	 * @param name2
	 *            Name of the state in the BA
	 * @return
	 */
	private String generateStateName(String name1, String name2) {
		if (name1.equals("ULTIMATE.startENTRY") && mNWA.isInitial(name2)) {
			return "ULTIMATE.start";
		} else {
			return name1 + "__" + name2;
		}
	}

	private String generateHelperStateName(String location) {
		mHelperUnifique++;
		return "h_" + Integer.toString(mHelperUnifique) + location;
	}

}
