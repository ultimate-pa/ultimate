/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.BuchiProgramProduct;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
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

/**
 * This class is implementing the Buchi program product, multiplying
 * a BuchiAutomaton with the CFG. 
 * @see Masterarbeit TODO Titel
 * 
 * @author Langenfeld
 *
 */
public class Product {
	
	private NestedWordAutomaton<ASTNode, String> aut;
	private RootNode rcfg;	
	private List<ProgramPoint> rcfgLocations = new ArrayList<ProgramPoint>();
	
	private HashMap<String,ProgramPoint> productLocations = new HashMap<String, ProgramPoint>();
	
	private RootNode rootNode;
	
	private int helperUnifique = 0;

	HashMap< ProgramPoint, ArrayList<Call>> callEdges = new HashMap< ProgramPoint, ArrayList<Call>>();
	
	public Product(NestedWordAutomaton<ASTNode, String> aut, RootNode rcfg) throws Exception 
	{
		this.aut = aut;
		this.rcfg = rcfg;
		
		/*
		 * Can't acces the items in general so just making a copy and
		 * clearing the maps.
		 */
		//TODO: make deep copy of rootannot 
		this.rootNode = new RootNode(this.rcfg.getRootAnnot());
		//will be refilled when generating product nodes
		this.rootNode.getRootAnnot().getProgramPoints().clear();
		//note: used only for iterating procedures in automaizer, so 
		//may or may not work empty...
		this.rootNode.getRootAnnot().getEntryNodes().clear();
		this.rootNode.getRootAnnot().getExitNodes().clear();
		this.rootNode.getRootAnnot().getLoopLocations().clear();
		
		
		final AcceptingNodeAnnotation acceptingNodeAnnotation = new AcceptingNodeAnnotation();
		this.rootNode.getPayload().getAnnotations().put(Activator.PLUGIN_ID, acceptingNodeAnnotation);
		
		
		this.collectRCFGLocations();
		this.createProductStates();
		this.createEdges();
		this.generateTransFormula();
	}
	
	
	private void generateTransFormula()
	{
		Boogie2SMT b2smt = this.rootNode.getRootAnnot().getBoogie2SMT();
		RootAnnot rootAnnot = this.rootNode.getRootAnnot();
		TransFormulaBuilder tfb = new TransFormulaBuilder(b2smt, rootAnnot);

		for (String procIdent : rootAnnot.getImplementations().keySet()) {
			Procedure proc = rootAnnot.getImplementations().get(procIdent);
			b2smt.declareLocals(proc);
		
			for (ProgramPoint node : rootAnnot.getProgramPoints().get(procIdent).values()){
				if (node.getLocationName().startsWith("h_"))
					System.out.println(node.getLocationName());
				for(RCFGEdge edge: node.getOutgoingEdges())
					if(edge instanceof StatementSequence)
						tfb.addTransitionFormulas(edge);
			}
		
			b2smt.removeLocals(proc);
		}
		
	}
	
	/**
	 * creates the crossproduct of all edges of every node of both automata
	 * @throws Exception
	 */
	private void createEdges() throws Exception
	{
		ProgramPoint targetpp, currentpp;
		
		TransFormulaBuilder transFormulaBuilder = new TransFormulaBuilder(
				this.rootNode.getRootAnnot().getBoogie2SMT(),
				this.rootNode.getRootAnnot()
				);
		
		//for Node x Node 
		for(int mode = 0; mode < 2; mode ++)
		for(ProgramPoint pp: this.rcfgLocations){
			System.out.println(pp.toString());
			for(String n: this.aut.getStates()){
				currentpp = this.productLocations.get(this.stateNameGenerator(pp.getLocationName(), n));
				// For Edge of Node x Edge of node
				for(RCFGEdge rcfgEdge: pp.getOutgoingEdges())
						//distinguish between the different Edges of the RCFG in the input
						if (rcfgEdge instanceof Call){ 
							if (mode == 1) continue; 
							//Call has to have a helper node, so that first the call can targeta
							//the helper node	
							String helperName = this.getHelperLoc(this.helperUnifique+currentpp.getPosition());
							ProgramPoint helper = new ProgramPoint(
										helperName,
										currentpp.getProcedure(), 
										false, 
										currentpp.getAstNode());
							this.rootNode.getRootAnnot().getProgramPoints().get(currentpp.getProcedure()).put(helperName, helper);
							
			
							Call c = new Call(
									currentpp, 
									helper,
									((Call) rcfgEdge).getCallStatement()
									);
							c.setTransitionFormula(((Call) rcfgEdge).getTransitionFormula());
							
							//store all call edge s in hashmap for later return edge generation
							if (!this.callEdges.containsKey(pp))
								this.callEdges.put(pp,new ArrayList<Call>());
							this.callEdges.get(pp).add(c);
							
							
							//From the helpernode, the original call target is connected with a new
							//edge with the fitting assumption of the call. The edge is calculated 
							//like any other edge in the graph.
							for(OutgoingInternalTransition<ASTNode, String> autTrans: this.aut.internalSuccessors(n)){
								targetpp = this.productLocations.get(
										this.stateNameGenerator(
												((ProgramPoint)rcfgEdge.getTarget()).getLocationName(),
												autTrans.getSucc().toString()
												));
							
								ArrayList<Statement> stmts = new ArrayList<Statement>();
								stmts.add(new AssumeStatement(null, ((Expression)autTrans.getLetter())));
								//edge
								StatementSequence s = new StatementSequence(
										helper, 
										targetpp, 
										stmts,
										Origin.IMPLEMENTATION);	
								
							}
						} else if (rcfgEdge instanceof Return) {
							if (mode == 0) continue; 
							//The calls used for the returns are dummy calls, that have nothing common with the original 
							//call except the caller location, that has to be popped from the stack.
							//The target pp and call statement are never used and therefore left blank
							
							String helperName = this.getHelperLoc(((ProgramPoint)rcfgEdge.getTarget()).getPosition());
							ProgramPoint helper = new ProgramPoint(
									helperName,
									((ProgramPoint)rcfgEdge.getTarget()).getProcedure(), 
									false, 
									((ProgramPoint)rcfgEdge.getTarget()).getAstNode());
							//add helper node to procedures nodes
							//note that this node is already behin the return and in the NEXT procedure
							this.rootNode.getRootAnnot().getProgramPoints().get(
									((ProgramPoint)rcfgEdge.getTarget()).getProcedure())
										.put(helperName, helper);
							//for all possible call origins: CallPP x LTLStates be able to return to the helper state
							
							
							
							
							/*for(String nn: this.aut.getStates()){
								targetpp = this.productLocations.get(
										this.stateNameGenerator(
												((ProgramPoint)rcfgEdge.getTarget()).getLocationName(),n));
								Call call = new Call(
										this.productLocations.get(                   //source state
												this.stateNameGenerator(
														((ProgramPoint)((Return)rcfgEdge).getSource()).getLocationName(),
														nn)), 
												null,
												((Return)rcfgEdge).getCallStatement()
												);
								call.setTransitionFormula(((Return)rcfgEdge).getCorrespondingCall().getTransitionFormula());*/
							ProgramPoint key = 	((ProgramPoint)((Return)rcfgEdge).getCallerProgramPoint());
							for(Call call: this.callEdges.get(key)){
								Return r = new Return(
										currentpp,
										helper,
										call
										);
							r.setTransitionFormula(((Return) rcfgEdge).getTransitionFormula());
								//remove call from originating node, because new Call(... will automaticcaly attatch the edge to 
								//the location it is originating from....
								/*this.productLocations.get(                   //source state
										this.stateNameGenerator(
												((ProgramPoint)((Return)rcfgEdge).getSource()).getLocationName(),
												nn)).removeOutgoing(call);*/
							}
							//From the helpernode, the original call target is connected with a new
							//edge with the fitting assumption of the call. The edge is calculated 
							//like any other edge in the graph.
							for(OutgoingInternalTransition<ASTNode, String> autTrans: this.aut.internalSuccessors(n)){
								targetpp = this.productLocations.get(
										this.stateNameGenerator(
												((ProgramPoint)rcfgEdge.getTarget()).getLocationName(),
												autTrans.getSucc().toString()
												));
							
								ArrayList<Statement> stmts = new ArrayList<Statement>();
								stmts.add(new AssumeStatement(null, ((Expression)autTrans.getLetter())));
								//edge
								StatementSequence s = new StatementSequence(
										helper, 
										targetpp, 
										stmts,
										Origin.IMPLEMENTATION);	
								
							}
						} else if (rcfgEdge instanceof Summary) {
							//Summary summarizes a call compuation and return from another procedure
							//It - like calls and returns that also can take no assumtion edge on
							//its own - is handled like a call edge, first the summary to a helper node
							//then the helper node x Loc_psi to the original target
							/*ProgramPoint helper = new ProgramPoint(
									"h_summary_"+currentpp.getPosition(),
									currentpp.getProcedure(), 
									false, 
									currentpp.getAstNode());

							Summary summary = new Summary(
									currentpp, 
									helper,
									((Summary) rcfgEdge).getCallStatement(),
									false
									);
							summary.setTransitionFormula(((Summary) rcfgEdge).getTransitionFormula());
							//From the helpernode, the original summary target is connected with a new
							//edge with the fitting assumption of the call. The edge is calculated 
							//like any other edge in the graph.
							for(OutgoingInternalTransition<ASTNode, String> autTrans: this.aut.internalSuccessors(n)){
								targetpp = this.productLocations.get(
										this.stateNameGenerator(
												((ProgramPoint)rcfgEdge.getTarget()).getLocationName(),
												autTrans.getSucc().toString()
												));
							
								ArrayList<Statement> stmts = new ArrayList<Statement>();
								stmts.add(new AssumeStatement(null, ((Expression)autTrans.getLetter())));
								//edge
								StatementSequence s = new StatementSequence(
										helper, 
										targetpp, 
										stmts,
										Origin.IMPLEMENTATION);
								
								transFormulaBuilder.addTransitionFormulas(s);
							}*/
						} else if(rcfgEdge instanceof StatementSequence){
							if (mode == 1) continue; 
							for(OutgoingInternalTransition<ASTNode, String> autTrans: this.aut.internalSuccessors(n)){
								targetpp = this.productLocations.get(
										this.stateNameGenerator(
												((ProgramPoint)rcfgEdge.getTarget()).getLocationName(),
												autTrans.getSucc().toString()
												));
								//append statements of rcfg and ltl
								ArrayList<Statement> stmts = new ArrayList<Statement>();
								stmts.addAll(((StatementSequence)rcfgEdge).getStatements());
								stmts.add(new AssumeStatement(null, ((Expression)autTrans.getLetter())));
								//edge
								StatementSequence s = new StatementSequence(
										currentpp, 
										targetpp, 
										stmts,
										Origin.IMPLEMENTATION);
								
							}
						} else
							throw new Exception("RCFG Edgetype " + rcfgEdge.getClass() + " is currently not supported.");		
					}
			}
				
	}
	
	/**
	 * Multiply states and make them available in the dictionary 
	 * with their new name 
	 */
	private void createProductStates()
	{
		Map<String, Map<String, ProgramPoint>> productLocations = this.rootNode.getRootAnnot().getProgramPoints();
		
		ProgramPoint productNode;
		final AcceptingNodeAnnotation acceptingNodeAnnotation = new AcceptingNodeAnnotation();
		
		for(ProgramPoint pp: this.rcfgLocations){
			if (!productLocations.containsKey(pp.getProcedure())){
				productLocations.put(pp.getProcedure(), new HashMap<String, ProgramPoint>());
				System.out.println(pp.getProcedure());
			}
			for(String n: this.aut.getStates()){ 
				productNode = new ProgramPoint
									(		
									this.stateNameGenerator(pp.getLocationName(), n),
									pp.getProcedure(),
									false,
									pp.getAstNode());
				
				this.productLocations.put(this.stateNameGenerator(pp.getLocationName(), n), productNode);
					
				//accepting states (just check for AcceptingNodeAnnotation)
				if(this.aut.isFinal(n)){
					productNode.getPayload().getAnnotations().put(Activator.PLUGIN_ID, acceptingNodeAnnotation);
				}
					
				//inital states
				if (pp.getLocationName().equals("ULTIMATE.startENTRY"))
					if (this.aut.isInitial(n))
					{
						new RootEdge(this.rootNode, productNode);
						this.rootNode.getRootAnnot().getEntryNodes().put("ULTIMATE.start", productNode);
					}
				
				//add to annotation
				productLocations.get(pp.getProcedure()).put(this.stateNameGenerator(pp.getLocationName(), n), productNode);
			}
				
		}
	
	}
	
	/**
	 * collect all states that are part of the RCFG into a List
	 */
	private void  collectRCFGLocations()
	{
		Queue<ProgramPoint> unhandledLocations = new ArrayDeque<ProgramPoint>();
		
		for (RCFGEdge p: ((RootNode)this.rcfg).getOutgoingEdges())
			unhandledLocations.offer((ProgramPoint) p.getTarget());
		//collect all Nodes in the RCFG for the product
		ProgramPoint cp;
		while( unhandledLocations.peek() != null)
		{
			cp = unhandledLocations.poll();
			//if (!this.RCFGLocations.contains(cp))
				this.rcfgLocations.add(cp);
			for (RCFGEdge p: cp.getOutgoingEdges())
			{
				if (p instanceof Summary) continue;
				if(!(this.rcfgLocations.contains(p.getTarget()) || unhandledLocations.contains(p.getTarget())))
					unhandledLocations.offer((ProgramPoint)p.getTarget());
			}
			//append selfloopst o leafs of the rcfg
			if (cp.getOutgoingEdges().size() == 0)
			{
				new StatementSequence(cp, cp, new AssumeStatement(null, new BooleanLiteral(null, true)));
			}
		}
	}

	
	/**
	 * Central method to create the product sate's names
	 * form: P_name __ Aut_name
	 * @param name1 Name of the state in the RCFG
	 * @param name2 Name of the state in the BA
	 * @return
	 */
	private String stateNameGenerator(String name1, String name2)
	{
		if (name1.equals("ULTIMATE.startENTRY") && this.aut.isInitial(name2))
			return "ULTIMATE.start";
		else
			return name1 + "__" + name2;
	}
	
	public RootNode getRCFG()
	{
		return this.rootNode;
	}
	
	private String getHelperLoc(String location)
	{
		this.helperUnifique++;
		return "h_" + Integer.toString(this.helperUnifique) + location;
	}

}




























