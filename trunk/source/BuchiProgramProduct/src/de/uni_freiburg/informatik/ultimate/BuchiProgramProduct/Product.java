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
import java.util.Queue;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
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
	private List<ProgramPoint> RCFGLocations = new ArrayList<ProgramPoint>();
	
	private HashMap<String,ProgramPoint> nodes = new HashMap<String, ProgramPoint>();
	
	private RootNode main = new RootNode(null);

	
	
	public Product(NestedWordAutomaton<ASTNode, String> aut, RootNode rcfg) throws Exception 
	{
		this.aut = aut;
		this.rcfg = rcfg;
		
		this.collectRCFGLocations();
		this.createProductStates();
		this.createEdges();
	}
	
	/**
	 * creates the crossproduct of all edges of every node of both automata
	 * @throws Exception
	 */
	private void createEdges() throws Exception
	{
		ProgramPoint targetpp, currentpp;
		
		//for Node x Node 
		for(ProgramPoint pp: this.RCFGLocations){
			for(String n: this.aut.getStates()){
				currentpp = this.nodes.get(this.StateNameGenerator(pp.getLocationName(), n));
				// For Edge of Node x Edge of node
				for(RCFGEdge rcfgEdge: pp.getOutgoingEdges())								
						//distinguish between the different Edges of the RCFG in the input
						if (rcfgEdge instanceof Call){
							//Call does not change anything on the global variables, therefore  we can just
							//take the call from the original program, the logical autaton is paused on 
							//that edges.
							targetpp = this.nodes.get(
									this.StateNameGenerator(
											((ProgramPoint)rcfgEdge.getTarget()).getLocationName(),n));
							new Call(
									currentpp, 
									targetpp,
									((Call) rcfgEdge).getCallStatement()
									);
						} else if (rcfgEdge instanceof Return) {
							//The calls used for the returns are dummy calls, that have nothing common with the original 
							//call except the caller location, that has to be popped from the stack.
							//The target pp and call statement are never used and therefore left blank
							
							//for all possible call origins: CallPP x LTLStates be able to return
							for(String nn: this.aut.getStates()){
								targetpp = this.nodes.get(
										this.StateNameGenerator(
												((ProgramPoint)rcfgEdge.getTarget()).getLocationName(),n));
								new Return(
										currentpp,
										targetpp,
										new Call(
												this.nodes.get(
															this.StateNameGenerator(
																	((ProgramPoint)((Return)rcfgEdge).getSource()).getLocationName(),
																	nn)), 
												null,
												null)
										);
							}
						} else if (rcfgEdge instanceof Summary) {
							//Summary summarizes a call compuation and return from another procedure
							//therefore it is handled like another procedure by ignoring its influence on
							//the program state and skipping the step on the logical autoamton.
							targetpp = this.nodes.get(
									this.StateNameGenerator(
											((ProgramPoint)rcfgEdge.getTarget()).getLocationName(),n));
							new Summary(
									currentpp, 
									targetpp,
									((Summary) rcfgEdge).getCallStatement(),
									false
									);
							
						} else if(rcfgEdge instanceof StatementSequence){
							for(OutgoingInternalTransition<ASTNode, String> autTrans: this.aut.internalSuccessors(n)){
								targetpp = this.nodes.get(
										this.StateNameGenerator(
												((ProgramPoint)rcfgEdge.getTarget()).getLocationName(),
												autTrans.getSucc().toString()
												));
								//append statements of rcfg and ltl
								ArrayList<Statement> stmts = new ArrayList<Statement>();
								stmts.addAll(((StatementSequence)rcfgEdge).getStatements());
								stmts.add(new AssumeStatement(null, ((Expression)autTrans.getLetter())));
								//edge
								new StatementSequence(
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
		ProgramPoint ncp;
		
		for(ProgramPoint pp: this.RCFGLocations){
			for(String n: this.aut.getStates()){
				this.nodes.put(this.StateNameGenerator(pp.getLocationName(), n), 
					ncp = new ProgramPoint
									(		
									pp.getPosition(),
									pp.getPosition(),
									false,
									pp.getAstNode(),
									null,
									null 
									));
				
			// acceptance and inital states
			if (pp.getLocationName() == "mainENTRY" && this.aut.getInitialStates().contains(n))
				new RootEdge(this.main, ncp);
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
				this.RCFGLocations.add(cp);
			for (RCFGEdge p: cp.getOutgoingEdges())
				if(!(this.RCFGLocations.contains(p.getTarget()) || unhandledLocations.contains(p.getTarget())))
					unhandledLocations.offer((ProgramPoint)p.getTarget());
			
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
	private String StateNameGenerator(String name1, String name2)
	{
		return name1 + "__" + name2;
	}
	
	public RootNode getRCFG()
	{
		return this.main;
	}

}




























