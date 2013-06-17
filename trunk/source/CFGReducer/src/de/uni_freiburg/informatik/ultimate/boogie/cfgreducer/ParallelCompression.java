package de.uni_freiburg.informatik.ultimate.boogie.cfgreducer;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTEdgeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableSSAManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;

public class ParallelCompression {

	public boolean run(CFGEdge edge) {
		boolean result = false;
		Logger.getLogger(Activator.PLUGIN_ID).debug("Merging parallel edges of edge " + edge.getPayload().getName());
		ArrayDeque<CFGEdge> parallelEdges = new ArrayDeque<CFGEdge>();
		for (IEdge outEdge: edge.getSource().getOutgoingEdges()){
			if ((outEdge.getTarget() == edge.getTarget()) && (outEdge != edge)){
				parallelEdges.add((CFGEdge)outEdge);
			}
		}
		if(!parallelEdges.isEmpty()) {
			result = true;
		}
		while(!parallelEdges.isEmpty()) {
			edge = createMergedEdgeWith(edge, parallelEdges.pop());
		}
		
		Logger.getLogger(Activator.PLUGIN_ID).debug("Done merging parallel edges of edge " + edge.getPayload().getName());
		return result;
	}
	
	public boolean run(CFGExplicitNode node) {
		boolean result = false;
		Logger.getLogger(Activator.PLUGIN_ID).debug("Merging parallel edges of node " + node.getPayload().getName());
		HashMap<CFGEdge, ArrayDeque<CFGEdge>> allParallelEdges = new HashMap<CFGEdge, ArrayDeque<CFGEdge>>(); 
		for (IEdge outEdge: node.getOutgoingEdges()){
			boolean hasNewTarget = true;
			for(Entry<CFGEdge, ArrayDeque<CFGEdge>> entry: allParallelEdges.entrySet()) {
				if ((outEdge.getTarget() == entry.getKey().getTarget()) && (outEdge != entry.getKey())){
					entry.getValue().add((CFGEdge)outEdge);
					hasNewTarget = false;
					break;
				}
			}
			if (hasNewTarget) {
				allParallelEdges.put((CFGEdge)outEdge, new ArrayDeque<CFGEdge>());
			}
		}
		for(CFGEdge edge: allParallelEdges.keySet()) {
			ArrayDeque<CFGEdge> parallelEdges = allParallelEdges.get(edge);
			if(!parallelEdges.isEmpty()) {
				result = true;
			}
			while(!parallelEdges.isEmpty()) {
				edge = createMergedEdgeWith(edge, parallelEdges.pop());
			}
		}
		
		Logger.getLogger(Activator.PLUGIN_ID).debug("Done merging parallel edges of node " + node.getPayload().getName());
		return result;
	}
	
	public CFGEdge createMergedEdgeWith(CFGEdge edge1, CFGEdge edge2){
		Script script = edge1.getScript();
		
		Logger.getLogger(Activator.PLUGIN_ID).debug("Merging edge " + edge1.getPayload().getName() + " with " +
				edge2.getPayload().getName());
		CFGEdge newEdge = edge1.copyWithoutNodes();
		newEdge.setSource(edge1.getSource());
		newEdge.setTarget(edge1.getTarget());
		newEdge.setSubstitution(edge1.getSubstitutionMap());
		newEdge.addSubstitution(edge2.getSubstitutionMap());
		
		SMTEdgeAnnotations					annotation	= newEdge.getSMTAnnotations();
		HashMap<BoogieVar, TermVariable> 	in_vars		= annotation.getInVars(); 
		HashMap<BoogieVar, TermVariable> 	out_vars	= annotation.getOutVars();
		HashSet<TermVariable> 				vars		= annotation.getVars();
		SMTEdgeAnnotations					e_annotation= (SMTEdgeAnnotations)edge2.getPayload().getAnnotations().get("SMT");
		HashMap<BoogieVar, TermVariable> 	e_in_vars	= e_annotation.getInVars();
		HashMap<BoogieVar, TermVariable> 	e_out_vars	= e_annotation.getOutVars();
		HashSet<TermVariable> 				e_vars		= e_annotation.getVars();
		
		HashMap<BoogieVar, TermVariable>	newInvars	= new HashMap<BoogieVar, TermVariable>();
		HashMap<BoogieVar, TermVariable>	newOutvars	= new HashMap<BoogieVar, TermVariable>();
		HashSet<TermVariable>				newVars		= new HashSet<TermVariable>();
		
		Term assumption		= annotation.getAssumption();
		Term e_assumption	= e_annotation.getAssumption();
				
		if (annotation.hasIds()) {
			Term negativeEdgeIdFormula 	= annotation.getNegativeEdgeIdFormula(e_annotation.getEdgeIds());
			Term e_negativeEdgeIdFormula = e_annotation.getNegativeEdgeIdFormula(annotation.getEdgeIds());
			assumption = Util.and(script,
					assumption, e_negativeEdgeIdFormula);
			e_assumption = Util.and(script,
					e_assumption, negativeEdgeIdFormula);	
		}
		
		HashSet<BoogieVar> allOutBoogieVars = new HashSet<BoogieVar>();
		allOutBoogieVars.addAll(out_vars.keySet());
		allOutBoogieVars.addAll(e_out_vars.keySet());
		newVars.addAll(vars);
		newVars.addAll(e_vars);
		
		for (BoogieVar boogieVar : allOutBoogieVars) {
			TermVariable invar		= in_vars.get(boogieVar);
			TermVariable outvar		= out_vars.get(boogieVar);
			TermVariable e_invar	= e_in_vars.get(boogieVar);
			TermVariable e_outvar	= e_out_vars.get(boogieVar);
			
			if (edge1.getAllEdgeIds().keySet().contains(boogieVar)){
				TermVariable n_outvar = outvar!=null?outvar:e_outvar;
				newOutvars.put(boogieVar, n_outvar);
				continue;
			}
			
			if (outvar != null){
				if (outvar.equals(e_outvar)){
					/* if the two edges have an identical out going variable,
					 * that means that they inherited it from an predecessor node
					 * and therefore no mapping is needed
					 */
					if (invar != null) {
						if (e_invar != null) {
							if (invar != e_invar){
								newEdge.addSubstitution(e_invar, invar);
								newVars.remove(e_invar);
							}
						}
						newInvars.put(boogieVar, invar);
					} else if (e_invar != null) {
						newInvars.put(boogieVar, e_invar);
					}
					newOutvars.put(boogieVar, outvar);
					continue;
				}	
			}
			
			if (outvar != invar) {
				//variable is changed, check other edge.
				if (e_outvar == e_invar) {
					if (e_invar == null) {
						e_invar = VariableSSAManager.getFreshTermVariable(boogieVar, outvar.getSort());
						newVars.add(e_invar);
					} 
					Term equality = script.term("=", outvar, e_invar);
					e_assumption = Util.and(script,  e_assumption, equality);
					newOutvars.put(boogieVar, outvar);
				} else {
					if (e_vars.contains(outvar)){
						newEdge.addSubstitution(outvar, e_outvar);
						newVars.remove(outvar);
						newOutvars.put(boogieVar, e_outvar);
						newOutvars.remove(outvar);
					} else {
						newEdge.addSubstitution(e_outvar, outvar);
						newVars.remove(e_outvar);
						newOutvars.put(boogieVar, outvar);
					}
				}
			} else if (e_outvar != e_invar) {
				//other variable is changed, this edge is unchanged.
				if (invar == null) {
					invar = VariableSSAManager.getFreshTermVariable(boogieVar, e_outvar.getSort());
					newVars.add(invar);
				}
				Term equality = script.term("=", e_outvar, invar);
				assumption = Util.and(script,  assumption, equality);
				newOutvars.put(boogieVar, e_outvar);
			} else if (outvar != null) {
				newOutvars.put(boogieVar, outvar);
			} else {
				assert (e_outvar != null);
				newOutvars.put(boogieVar, e_outvar);
			}

			if (invar != null) {
				if (e_invar != null) {
					if (invar != e_invar){
						newEdge.addSubstitution(e_invar, invar);
						newVars.remove(e_invar);
					}
				}
				newInvars.put(boogieVar, invar);
			} else if (e_invar != null) {
				newInvars.put(boogieVar, e_invar);
			}
		}

		Term newAssumption = Util.or(script,
				assumption, e_assumption);
		
		
		annotation.setInVars(newInvars);
		annotation.setOutVars(newOutvars);
		annotation.setVars(newVars);
		annotation.setAssumption(newAssumption);
		if (annotation.hasIds()) {
			Term e_positiveEdgeIdFormula = e_annotation.getPositiveEdgeIdFormula();
			annotation.addOrEdgeId(e_positiveEdgeIdFormula,
					e_annotation.getEdgeIds());
		}((CFGEdge)edge2).deleteEdge();
		edge1.deleteEdge();
		return newEdge;
	}
}
