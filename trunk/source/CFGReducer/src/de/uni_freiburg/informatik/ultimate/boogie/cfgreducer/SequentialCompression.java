package de.uni_freiburg.informatik.ultimate.boogie.cfgreducer;

import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTEdgeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;

public class SequentialCompression {

	boolean m_makeIdTags = false;
	
	public void run(CFGEdge edge) {
		mergeNodes(edge);
		CFGExplicitNode target = (CFGExplicitNode) edge.getTarget();
		//Iterate through all edges of the target and concatenate them with edge coming from source
		for (IEdge isucc_edge: target.getOutgoingEdges()){
			CFGEdge succ_edge = (CFGEdge)isucc_edge;
			//concatenates the edges
			concatEdges(edge, succ_edge);
		}
		//delete target and all edges that lead to and from it
		delete_Node(target);
	}
	
	private void mergeNodes(CFGEdge edge) {
		Script script = edge.getScript();
//		HashMap<Term, Term> subTermMapping = new HashMap<Term, Term>();
//		SubstituteTermTransformer subTermTransformer = new SubstituteTermTransformer();
		
		Logger.getLogger(Activator.PLUGIN_ID).debug("Merging nodes of edge " + edge.getPayload().getName());
		//get all formulas and variables of the edge and its source and target
		CFGExplicitNode node1 = (CFGExplicitNode) edge.getSource();
		CFGExplicitNode node2 = (CFGExplicitNode) edge.getTarget();
		HashMap<BoogieVar, TermVariable> e_invars	= edge.getSMTAnnotations().getInVars();
		HashMap<BoogieVar, TermVariable> e_outvars = edge.getSMTAnnotations().getOutVars();
		
		HashMap<BoogieVar, TermVariable> n1_invars = node1.getSMTAnnotations().getInVars();
		HashMap<BoogieVar, TermVariable> n2_invars = node2.getSMTAnnotations().getInVars();
		
		HashSet<TermVariable> e_vars	= edge.getSMTAnnotations().getVars();
		HashSet<TermVariable> n1_vars	= node1.getSMTAnnotations().getVars();
		HashSet<TermVariable> n2_vars	= node2.getSMTAnnotations().getVars();
			
		HashMap<BoogieVar, TermVariable>	new_invars	= new HashMap<BoogieVar, TermVariable>();
		HashSet<TermVariable> 				new_vars		= new HashSet<TermVariable>();
		
		Term n1_assertion	= node1.getAssertion();
		Term e_assumption	= edge.getAssumption();
		
		Term new_assertion		= node2.getAssertion();
		
		new_vars.addAll(n1_vars);
		new_vars.addAll(n2_vars);
		new_vars.addAll(e_vars);
		
		node1.addSubstitution(edge.getSubstitutionMap());
		node1.addSubstitution(node2.getSubstitutionMap());
		
		//all in coming variables of the source node will also be in coming variables of the merged result node
		// no, that not true!!! Therefore added n1_invars.
		new_invars.putAll(n1_invars);
		new_invars.putAll(e_invars);
		
		//iterate through all in coming variables of the target node and map them if possible
		for (BoogieVar boogieVar: n2_invars.keySet()){
			TermVariable n2_invar	= n2_invars.get(boogieVar);
			TermVariable e_outvar	= e_outvars.get(boogieVar);
			TermVariable e_invar	= e_invars.get(boogieVar);
			if (e_outvar != null){
				node1.addSubstitution(n2_invar, e_outvar);
//				subTermMapping.put(n2_invar, e_outvar);
//				n_assertion = m_subTermTransformer.substitute(n_assertion, n2_invar, e_outvar);
				new_vars.remove(n2_invar);
			} else if (e_invar != null){
				//node1 can have an in coming variable vname since it can obtain it from a previous merge with another node
				node1.addSubstitution(n2_invar, e_invar);
//				subTermMapping.put(n2_invar, e_invar);
//				n_assertion = m_subTermTransformer.substitute(n_assertion, n2_invar, n1_invar);	
				new_vars.remove(n2_invar);
			} else {
				new_invars.put(boogieVar, n2_invar);
			}
		}
//		new_assertion = subTermTransformer.substitute(new_assertion, subTermMapping);
//		subTermMapping.clear();
		
		//append the formulas of the edge and the target node
//		new_assertion = Util.and(m_Script, e_assumption, new_assertion);
		new_assertion = Util.implies(script, e_assumption, new_assertion);

		//iterate through all in coming variables of the edge and map them to in coming variables of the source node
		for (BoogieVar boogieVar: new_invars.keySet()){
			TermVariable e_invar	= new_invars.get(boogieVar);
			TermVariable n1_invar	= n1_invars.get(boogieVar);
			if (n1_invar != null){
				if(n1_invar != e_invar){
					node1.addSubstitution(e_invar, n1_invar);
//					subTermMapping.put(e_invar, n1_invar);
//					n_assertion = m_subTermTransformer.substitute(n_assertion, e_invar, n1_invar);
					new_vars.remove(e_invar);
					new_invars.put(boogieVar, n1_invar);
				}
			}
		}
//		new_assertion = subTermTransformer.substitute(new_assertion, subTermMapping);
//		subTermMapping.clear();
		
		//append the formulas of the source and current assertion
		new_assertion = Util.and(script,  n1_assertion, new_assertion);
		
		node1.setAssertion(new_assertion);
		node1.getSMTAnnotations().setInVars(new_invars);
		node1.getSMTAnnotations().setVars(new_vars);
		ILocation locNode1 = node1.getPayload().getLocation();
		ILocation locNode2 = node2.getPayload().getLocation();
		
		BoogieLocation newLoc = new BoogieLocation(locNode1.getFileName(),
								locNode1.getStartLine(), locNode2.getEndLine(),
								locNode1.getStartColumn(), locNode2.getEndColumn(),
								false); //TODO not really checked whether loop entry or not
		node1.getPayload().setLocation(newLoc);
		Logger.getLogger(Activator.PLUGIN_ID).debug("Done merging nodes of edge " + edge.getPayload().getName());
		return;
	}

	private CFGEdge concatEdges(CFGEdge edge1, CFGEdge edge2) {
		Script script = edge1.getScript();
		Logger.getLogger(Activator.PLUGIN_ID).debug("Concatenating edges " +
	edge1.getPayload().getName() + " and " + edge1.getPayload().getName());
		SMTEdgeAnnotations edge1Annotation = edge1.getSMTAnnotations();
		SMTEdgeAnnotations edge2Annotation = edge2.getSMTAnnotations();
		
		HashMap<BoogieVar, TermVariable> edge1InVars		= edge1Annotation.getInVars();
		HashMap<BoogieVar, TermVariable> edge2InVars		= edge2Annotation.getInVars();
		
			
		HashMap<BoogieVar, TermVariable> newInVars			= new HashMap<BoogieVar, TermVariable>();
		
		HashMap<BoogieVar, TermVariable> edge1OutVars	= edge1Annotation.getOutVars();
		HashMap<BoogieVar, TermVariable> edge2OutVars	= edge2Annotation.getOutVars();
		HashMap<BoogieVar, TermVariable> newOutVars	= new HashMap<BoogieVar, TermVariable>();
		
		HashSet<TermVariable> edge1Vars				= edge1Annotation.getVars();
		HashSet<TermVariable> edge2Vars				= edge2Annotation.getVars();
		HashSet<TermVariable> newVars				= new HashSet<TermVariable>();
		
		Term edge1Assumption	= edge1.getAssumption();
		Term edge2Assumption	= edge2.getAssumption();
		Term newAssumption	= edge2Assumption;
		
		//first fill all variables in n_vars, later delete each variable that is mapped by a let-statement and therefore not visible anymore
		newVars.addAll(edge1Vars);
		newVars.addAll(edge2Vars);
		
		newInVars.putAll(edge1InVars);
		newOutVars.putAll(edge2OutVars);
		
		//this loop handles all out variables of e1
		for (BoogieVar boogieVar: edge1OutVars.keySet()){
			TermVariable e1_outvar	= edge1OutVars.get(boogieVar);
			TermVariable e2_invar	= edge2InVars.get(boogieVar);
			
			if (e2_invar != null){
				newAssumption = Util.and(script,  script.term("=", e2_invar, e1_outvar), newAssumption);
				newVars.add(e2_invar);
				newVars.add(e1_outvar);
			} else {
				if (!edge2OutVars.containsKey(boogieVar)) {
					newOutVars.put(boogieVar, e1_outvar);
				} else {
					newVars.add(e1_outvar);
				}
			}
		}
		
		//this loop handles all in variables of e2 that could not be mapped to any out variable of e1
		for (BoogieVar boogieVar: edge2InVars.keySet()){
			TermVariable edge1Outvar	= edge1OutVars.get(boogieVar);
			TermVariable edge2Invar	= edge2InVars.get(boogieVar);
			if (edge1Outvar == null){
				newInVars.put(boogieVar, edge2Invar);
			}
		}
		
		//append formulas
		newAssumption = Util.and(script,  edge1Assumption, newAssumption);
		
		//put everything in a new CFG edge and return it
		CFGEdge newEdge = new CFGEdge(script, newAssumption, edge1.getSource(), edge2.getTarget());

		SMTEdgeAnnotations newAnnotation = newEdge.getSMTAnnotations();
		
		if(edge1.useIdTags()) {
			Term edge1_positiveEdgeIdFormula = edge1Annotation.getPositiveEdgeIdFormula();
			Term edge2_positiveEdgeIdFormula = edge2Annotation.getPositiveEdgeIdFormula();
			HashSet<TermVariable> edge1_EdgeIds = edge1Annotation.getEdgeIds();
			HashSet<TermVariable> edge2_EdgeIds = edge2Annotation.getEdgeIds();
			
			newAnnotation.setEdgeIdFormula(edge1_positiveEdgeIdFormula,
					edge1_EdgeIds);
			newAnnotation.addAndEdgeId(edge2_positiveEdgeIdFormula,
					edge2_EdgeIds);
		}
		
		//fill new edge with new annotations
		newAnnotation.setInVars(newInVars);
		newAnnotation.setOutVars(newOutVars);
		newAnnotation.setVars(newVars);

		ILocation locEdge1 = edge1.getPayload().getLocation();
		ILocation locEdge2 = edge2.getPayload().getLocation();
		
		int startLine, endLine, startColumn, endColumn;
		if (locEdge1.getStartLine() < locEdge2.getStartLine()) {
			startLine	= locEdge1.getStartLine();
			endLine		= locEdge2.getEndLine();
			startColumn	= locEdge1.getStartColumn();
			endColumn	= locEdge2.getEndColumn();
		} else {
			startLine	= locEdge2.getStartLine();
			endLine		= locEdge1.getEndLine();
			startColumn	= locEdge2.getStartColumn();
			endColumn	= locEdge1.getEndColumn();
		}
		BoogieLocation newLocation = new BoogieLocation(locEdge1.getFileName(),
										startLine, endLine, startColumn, endColumn, false);
		newEdge.addSubstitution(edge1.getSubstitutionMap());
		newEdge.addSubstitution(edge2.getSubstitutionMap());
		newEdge.getPayload().setLocation(newLocation);
		Logger.getLogger(Activator.PLUGIN_ID).debug("Done concatenating edges " +
				edge1.getPayload().getName() + " and " + edge1.getPayload().getName());
		return newEdge;
	}
	
	//deletes node and all its edges
	private void delete_Node(CFGExplicitNode node) {
		Logger.getLogger(Activator.PLUGIN_ID).debug("Deleting node " + node.getPayload().getName());
		//go to all predecessor and remove pointer to incoming edges of node
		for (IEdge iedge: node.getIncomingEdges()){
			CFGEdge edge = (CFGEdge)iedge;
			edge.getSource().getOutgoingEdges().remove(edge);
		}
		//go to all successors and remove pointer to outgoing edges of node
		for (IEdge iedge: node.getOutgoingEdges()){
			CFGEdge edge = (CFGEdge)iedge;
			edge.getTarget().getIncomingEdges().remove(edge);
		}
		//clear the list of in and out going edges of this node
		node.removeAllIncoming();
		node.removeAllOutgoing();
		Logger.getLogger(Activator.PLUGIN_ID).debug("Done deleting node " + node.getPayload().getName());
	}
}
