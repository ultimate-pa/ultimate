/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.BuchiProgramProduct;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

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

	private NestedWordAutomaton<BoogieASTNode, String> mNWA;
	private RootNode mRCFG;
	private List<ProgramPoint> mRCFGLocations;

	private HashMap<String, ProgramPoint> mProductLocations;

	private RootNode mRootNode;

	private int mHelperUnifique = 0;

	private HashMap<ProgramPoint, ArrayList<Call>> mCallEdges;

	private Logger mLogger;

	public Product(NestedWordAutomaton<BoogieASTNode, String> aut, RootNode rcfg) throws Exception {
		mLogger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
		mRCFGLocations = new ArrayList<ProgramPoint>();
		mProductLocations = new HashMap<String, ProgramPoint>();
		mCallEdges = new HashMap<ProgramPoint, ArrayList<Call>>();

		mNWA = aut;
		mRCFG = rcfg;

		/*
		 * Can't acces the items in general so just making a copy and clearing
		 * the maps.
		 */
		// TODO: make deep copy of rootannot
		mRootNode = new RootNode(mRCFG.getRootAnnot());
		// will be refilled when generating product nodes
		mRootNode.getRootAnnot().getProgramPoints().clear();
		// note: used only for iterating procedures in automaizer, so
		// may or may not work empty...
		mRootNode.getRootAnnot().getEntryNodes().clear();
		mRootNode.getRootAnnot().getExitNodes().clear();
		mRootNode.getRootAnnot().getLoopLocations().clear();
		mRootNode.getPayload().getAnnotations().put(Activator.PLUGIN_ID, new AcceptingNodeAnnotation());

		collectRCFGLocations();
		createProductStates();
		createEdges();
		generateTransFormula();
	}

	private void generateTransFormula() {
		Boogie2SMT b2smt = mRootNode.getRootAnnot().getBoogie2SMT();
		RootAnnot rootAnnot = mRootNode.getRootAnnot();
		TransFormulaBuilder tfb = new TransFormulaBuilder(b2smt, rootAnnot);

		for (String procIdent : rootAnnot.getBoogieDeclarations().getProcImplementation().keySet()) {
			Procedure proc = rootAnnot.getBoogieDeclarations().getProcImplementation().get(procIdent);
//			b2smt.declareLocals(proc);

			for (ProgramPoint node : rootAnnot.getProgramPoints().get(procIdent).values()) {
				if (node.getLocationName().startsWith("h_")) {
					mLogger.debug(node.getLocationName());
				}
				for (RCFGEdge edge : node.getOutgoingEdges()) {
					if (edge instanceof StatementSequence) {
						tfb.addTransitionFormulas(edge, procIdent);
					}
				}
			}

//			b2smt.removeLocals(proc);
		}

	}

	/**
	 * creates the crossproduct of all edges of every node of both automata
	 * 
	 * @throws Exception
	 */
	private void createEdges() throws Exception {
		ProgramPoint targetpp, currentpp;

		TransFormulaBuilder transFormulaBuilder = new TransFormulaBuilder(mRootNode.getRootAnnot().getBoogie2SMT(),
				mRootNode.getRootAnnot());

		// for Node x Node
		for (int mode = 0; mode < 2; mode++)
			for (ProgramPoint pp : mRCFGLocations) {
				mLogger.debug(pp.toString());
				for (String n : mNWA.getStates()) {
					currentpp = mProductLocations.get(stateNameGenerator(pp.getLocationName(), n));
					// For Edge of Node x Edge of node
					for (RCFGEdge rcfgEdge : pp.getOutgoingEdges())
						// distinguish between the different Edges of the RCFG
						// in the input
						if (rcfgEdge instanceof Call) {
							if (mode == 1)
								continue;
							// Call has to have a helper node, so that first the
							// call can target
							// the helper node
							String helperName = getHelperLoc(mHelperUnifique + currentpp.getPosition());
							ProgramPoint helper = new ProgramPoint(helperName, currentpp.getProcedure(), false,
									currentpp.getBoogieASTNode());
							mRootNode.getRootAnnot().getProgramPoints().get(currentpp.getProcedure())
									.put(helperName, helper);

							Call c = new Call(currentpp, helper, ((Call) rcfgEdge).getCallStatement());
							c.setTransitionFormula(((Call) rcfgEdge).getTransitionFormula());

							// store all call edge s in hashmap for later return
							// edge generation

							if (!mCallEdges.containsKey(pp)) {
								mCallEdges.put(pp, new ArrayList<Call>());
							}
							mCallEdges.get(pp).add(c);

							// From the helpernode, the original call target is
							// connected with a new
							// edge with the fitting assumption of the call. The
							// edge is calculated
							// like any other edge in the graph.
							for (OutgoingInternalTransition<BoogieASTNode, String> autTrans : mNWA
									.internalSuccessors(n)) {
								targetpp = mProductLocations.get(stateNameGenerator(((ProgramPoint) rcfgEdge
										.getTarget()).getLocationName(), autTrans.getSucc().toString()));

								ArrayList<Statement> stmts = new ArrayList<Statement>();
								stmts.add(new AssumeStatement(null, ((Expression) autTrans.getLetter())));
								// edge
								StatementSequence s = new StatementSequence(helper, targetpp, stmts,
										Origin.IMPLEMENTATION);

							}
						} else if (rcfgEdge instanceof Return) {
							if (mode == 0)
								continue;
							// The calls used for the returns are dummy calls,
							// that have nothing common with the original
							// call except the caller location, that has to be
							// popped from the stack.
							// The target pp and call statement are never used
							// and therefore left blank

							String helperName = getHelperLoc(((ProgramPoint) rcfgEdge.getTarget()).getPosition());
							ProgramPoint helper = new ProgramPoint(helperName,
									((ProgramPoint) rcfgEdge.getTarget()).getProcedure(), false,
									((ProgramPoint) rcfgEdge.getTarget()).getBoogieASTNode());
							// add helper node to procedures nodes
							// note that this node is already behin the return
							// and in the NEXT procedure
							mRootNode.getRootAnnot().getProgramPoints()
									.get(((ProgramPoint) rcfgEdge.getTarget()).getProcedure()).put(helperName, helper);
							// for all possible call origins: CallPP x LTLStates
							// be able to return to the helper state

							/*
							 * for(String nn: aut.getStates()){ targetpp =
							 * productLocations.get( stateNameGenerator(
							 * ((ProgramPoint)rcfgEdge.getTarget
							 * ()).getLocationName(),n)); Call call = new Call(
							 * productLocations.get( //source state
							 * stateNameGenerator(
							 * ((ProgramPoint)((Return)rcfgEdge
							 * ).getSource()).getLocationName(), nn)), null,
							 * ((Return)rcfgEdge).getCallStatement() );
							 * call.setTransitionFormula
							 * (((Return)rcfgEdge).getCorrespondingCall
							 * ().getTransitionFormula());
							 */
							ProgramPoint key = ((ProgramPoint) ((Return) rcfgEdge).getCallerProgramPoint());

							assert (key != null);
							assert (mCallEdges != null);
							assert (mCallEdges.get(key) != null);
							for (Call call : mCallEdges.get(key)) {
								Return r = new Return(currentpp, helper, call);
								r.setTransitionFormula(((Return) rcfgEdge).getTransitionFormula());
								// remove call from originating node,
								// because
								// new Call(... will automaticcaly attatch
								// the
								// edge to
								// the location it is originating from....
								/*
								 * productLocations.get( //source state
								 * stateNameGenerator( ((ProgramPoint)((Return
								 * )rcfgEdge).getSource ()).getLocationName(),
								 * nn)).removeOutgoing(call);
								 */
							}

							// From the helpernode, the original call target is
							// connected with a new
							// edge with the fitting assumption of the call. The
							// edge is calculated
							// like any other edge in the graph.
							for (OutgoingInternalTransition<BoogieASTNode, String> autTrans : mNWA
									.internalSuccessors(n)) {
								targetpp = mProductLocations.get(stateNameGenerator(((ProgramPoint) rcfgEdge
										.getTarget()).getLocationName(), autTrans.getSucc().toString()));

								ArrayList<Statement> stmts = new ArrayList<Statement>();
								stmts.add(new AssumeStatement(null, ((Expression) autTrans.getLetter())));
								// edge
								StatementSequence s = new StatementSequence(helper, targetpp, stmts,
										Origin.IMPLEMENTATION);

							}
						} else if (rcfgEdge instanceof Summary) {
							// Summary summarizes a call compuation and return
							// from another procedure
							// It - like calls and returns that also can take no
							// assumtion edge on
							// its own - is handled like a call edge, first the
							// summary to a helper node
							// then the helper node x Loc_psi to the original
							// target
							/*
							 * ProgramPoint helper = new ProgramPoint(
							 * "h_summary_"+currentpp.getPosition(),
							 * currentpp.getProcedure(), false,
							 * currentpp.getAstNode());
							 * 
							 * Summary summary = new Summary( currentpp, helper,
							 * ((Summary) rcfgEdge).getCallStatement(), false );
							 * summary.setTransitionFormula(((Summary)
							 * rcfgEdge).getTransitionFormula()); //From the
							 * helpernode, the original summary target is
							 * connected with a new //edge with the fitting
							 * assumption of the call. The edge is calculated
							 * //like any other edge in the graph.
							 * for(OutgoingInternalTransition<ASTNode, String>
							 * autTrans: aut.internalSuccessors(n)){ targetpp =
							 * productLocations.get( stateNameGenerator(
							 * ((ProgramPoint)rcfgEdge.getTarget
							 * ()).getLocationName(),
							 * autTrans.getSucc().toString() ));
							 * 
							 * ArrayList<Statement> stmts = new
							 * ArrayList<Statement>(); stmts.add(new
							 * AssumeStatement(null,
							 * ((Expression)autTrans.getLetter()))); //edge
							 * StatementSequence s = new StatementSequence(
							 * helper, targetpp, stmts, Origin.IMPLEMENTATION);
							 * 
							 * transFormulaBuilder.addTransitionFormulas(s); }
							 */
						} else if (rcfgEdge instanceof StatementSequence) {
							if (mode == 1)
								continue;
							for (OutgoingInternalTransition<BoogieASTNode, String> autTrans : mNWA
									.internalSuccessors(n)) {
								targetpp = mProductLocations.get(stateNameGenerator(((ProgramPoint) rcfgEdge
										.getTarget()).getLocationName(), autTrans.getSucc().toString()));
								// append statements of rcfg and ltl
								ArrayList<Statement> stmts = new ArrayList<Statement>();
								stmts.addAll(((StatementSequence) rcfgEdge).getStatements());
								stmts.add(new AssumeStatement(null, ((Expression) autTrans.getLetter())));
								// edge
								StatementSequence s = new StatementSequence(currentpp, targetpp, stmts,
										Origin.IMPLEMENTATION);

							}
						} else
							throw new Exception("RCFG Edgetype " + rcfgEdge.getClass() + " is currently not supported.");
				}
			}

	}

	/**
	 * Multiply states and make them available in the dictionary with their new
	 * name
	 */
	private void createProductStates() {
		Map<String, Map<String, ProgramPoint>> productLocations = mRootNode.getRootAnnot().getProgramPoints();

		ProgramPoint productNode;
		final AcceptingNodeAnnotation acceptingNodeAnnotation = new AcceptingNodeAnnotation();

		for (ProgramPoint pp : mRCFGLocations) {
			if (!productLocations.containsKey(pp.getProcedure())) {
				productLocations.put(pp.getProcedure(), new HashMap<String, ProgramPoint>());
				mLogger.debug(pp.getProcedure());
			}
			for (String n : mNWA.getStates()) {
				productNode = new ProgramPoint(stateNameGenerator(pp.getLocationName(), n), pp.getProcedure(), false,
						pp.getBoogieASTNode());

				mProductLocations.put(stateNameGenerator(pp.getLocationName(), n), productNode);

				// accepting states (just check for AcceptingNodeAnnotation)
				if (mNWA.isFinal(n)) {
					productNode.getPayload().getAnnotations().put(Activator.PLUGIN_ID, acceptingNodeAnnotation);
				}

				// inital states
				if (pp.getLocationName().equals("ULTIMATE.startENTRY"))
					if (mNWA.isInitial(n)) {
						new RootEdge(mRootNode, productNode);
						mRootNode.getRootAnnot().getEntryNodes().put("ULTIMATE.start", productNode);
					}

				// add to annotation
				productLocations.get(pp.getProcedure()).put(stateNameGenerator(pp.getLocationName(), n), productNode);
			}

		}

	}

	/**
	 * collect all states that are part of the RCFG into a List
	 */
	private void collectRCFGLocations() {
		Queue<ProgramPoint> unhandledLocations = new ArrayDeque<ProgramPoint>();

		for (RCFGEdge p : ((RootNode) mRCFG).getOutgoingEdges())
			unhandledLocations.offer((ProgramPoint) p.getTarget());
		// collect all Nodes in the RCFG for the product
		ProgramPoint cp;
		while (unhandledLocations.peek() != null) {
			cp = unhandledLocations.poll();
			// if (!RCFGLocations.contains(cp))
			mRCFGLocations.add(cp);
			for (RCFGEdge p : cp.getOutgoingEdges()) {
				if (p instanceof Summary)
					continue;
				if (!(mRCFGLocations.contains(p.getTarget()) || unhandledLocations.contains(p.getTarget())))
					unhandledLocations.offer((ProgramPoint) p.getTarget());
			}
			// append selfloopst o leafs of the rcfg
			if (cp.getOutgoingEdges().size() == 0) {
				new StatementSequence(cp, cp, new AssumeStatement(null, new BooleanLiteral(null, true)));
			}
		}
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
	private String stateNameGenerator(String name1, String name2) {
		if (name1.equals("ULTIMATE.startENTRY") && mNWA.isInitial(name2)) {
			return "ULTIMATE.start";
		} else {
			return name1 + "__" + name2;
		}
	}

	public RootNode getProductRCFG() {
		return mRootNode;
	}

	private String getHelperLoc(String location) {
		mHelperUnifique++;
		return "h_" + Integer.toString(mHelperUnifique) + location;
	}

}
