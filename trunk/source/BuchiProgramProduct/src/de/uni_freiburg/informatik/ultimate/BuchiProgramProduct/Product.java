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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

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
	
	private ProgramPoint main;

	
	
	public Product(NestedWordAutomaton<ASTNode, String> aut, RootNode rcfg) throws Exception 
	{
		this.aut = aut;
		this.rcfg = rcfg;
		
		this.collectRCFGLocations();
		this.createProductStates();
		this.createEdges();
	}
	
	private void createEdges() throws Exception
	{
		String key;		//name of product node per iteration
		ProgramPoint ncp;
		ProgramPoint targetpp, currentpp;
		
		//for Node x Node 
		for(ProgramPoint pp: this.RCFGLocations){
			for(String n: this.aut.getStates()){
				currentpp = this.nodes.get(this.StateNameGenerator(pp.getLocationName(), n));
				// For Edge of Node x Edge of node
				for(RCFGEdge rcfgEdge: pp.getOutgoingEdges())
					for(OutgoingInternalTransition<ASTNode, String> autTrans: this.aut.internalSuccessors(n)){
						targetpp = this.nodes.get(
								this.StateNameGenerator(
										((ProgramPoint)rcfgEdge.getTarget()).getLocationName(),
										autTrans.getSucc().toString()
										));
						//distinguish between the different Edges of the RCFG in the input
						if(rcfgEdge instanceof StatementSequence) {
							ArrayList<Statement> stmts = new ArrayList<Statement>();
							stmts.addAll(((StatementSequence)rcfgEdge).getStatements());
							stmts.add(new AssumeStatement(null, ((Expression)autTrans.getLetter())));
							new StatementSequence(
									currentpp, 
									targetpp, 
									stmts,
									null);
						} else if (rcfgEdge instanceof Call)
							continue;
						else if (rcfgEdge instanceof Return)
							continue;
						else
							throw new Exception("RCFG Edgetype " + rcfgEdge.getClass() + " wird aktuell noch nicht unterstützt...");
							
					}
			}
				
		}
	}
	
	/**
	 * Multiply states and make them available in the dictionary 
	 * with their new name 
	 */
	private void createProductStates()
	{
		String key;		//name of product node per iteration
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
				this.main = ncp;
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
				if(!(this.RCFGLocations.contains(cp) || unhandledLocations.contains(cp)))
					unhandledLocations.offer(cp);
		}
		
		/*Collection<String> autNodes = this.aut.getStates();
		HashSet<String> done = new HashSet<String>();
		
		Queue<ProgramPoint> unhandledLocations = new ArrayDeque<ProgramPoint>();
		//initialize queue with everything node following the root node
		for (RCFGEdge p: ((RootNode)this.rcfg).getOutgoingEdges())
			unhandledLocations.offer((ProgramPoint) p.getTarget());
		
		//as long as there are unmultiplied nodes
		ProgramPoint cp; 
		String key;		//name of product node per iteration
		ProgramPoint ncp;
		while( unhandledLocations.peek() != null)
		{
			cp = unhandledLocations.poll();
			for(String an: autNodes){
				key = this.StateNameGenerator(cp.getLocationName(), an);
				if (!this.nodes.containsKey(key)){
					//create new ProgramPoint conserving the properties of the old
					ncp = new ProgramPoint
									(		
									cp.getPosition(),
									cp.getPosition(),
									false,
									cp.getAstNode(),
									null,
									null 
									);
					this.nodes.put(key, ncp);
				}
				//create all outgoing Nodes from the current node
				for (RCFGEdge p: cp.getOutgoingEdges())
					if (!this.nodes.containsKey(key)){
						unhandledLocations.offer((ProgramPoint) p.getTarget());
				//create all edges
			}
				
		}*/
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
	
	public ProgramPoint getRCFG()
	{
		return this.main;
	}

}




























