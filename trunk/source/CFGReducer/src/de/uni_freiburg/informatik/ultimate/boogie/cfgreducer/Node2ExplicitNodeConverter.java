package de.uni_freiburg.informatik.ultimate.boogie.cfgreducer;

import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.CFGNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGNode;

public class Node2ExplicitNodeConverter {

	private Logger logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	private HashMap<CFGNode, CFGExplicitNode> m_explicitNodeMap = new HashMap<CFGNode, CFGExplicitNode>();
	
	@SuppressWarnings("unchecked")
	public CFGExplicitNode convert(CFGNode node, Script script, boolean makeIdTags){
		if (m_explicitNodeMap.containsKey(node)) {
			logger.debug("Already made explicit node for " + node.getPayload().getName());
			return m_explicitNodeMap.get(node);
		}
		CFGNodeAnnotations cfgNodeAnnotations = node.getCFGAnnotations();
		logger.debug("Starting to make explicit node for " + node.getPayload().getName());
		CFGExplicitNode explicitNode			= new CFGExplicitNode(script, cfgNodeAnnotations.getAssertion());
		logger.debug("Adding variable information from " + node.getPayload().getName());
		HashMap<BoogieVar, TermVariable> inVars	= cfgNodeAnnotations.getInVars();
		HashMap<BoogieVar, TermVariable> outVars= cfgNodeAnnotations.getOutVars();
		HashSet<TermVariable> vars				= cfgNodeAnnotations.getVars();
		explicitNode.getPayload().getAnnotations().put("CFGBuilder", cfgNodeAnnotations);
		
		m_explicitNodeMap.put(node, explicitNode);
		explicitNode.getPayload().setLocation(node.getPayload().getLocation());
		explicitNode.getPayload().setName(node.getPayload().getName());
		//__________________________________________________________________//
		// remove unnecessary variables from invars and vars of node		//
//		TermVariable[] freeVarsAssertion = explicitNode.getAssertion().getFreeVars();
//		HashMap<BoogieVar, TermVariable> finalInvarsAssertion = new HashMap<BoogieVar, TermVariable>();
//		HashSet<TermVariable> finalVarsAssertion = new HashSet<TermVariable>();
//		for(TermVariable freeVar: freeVarsAssertion) {
//			finalVarsAssertion.add(freeVar);
//		}
//		for(Entry<BoogieVar, TermVariable> entry: inVars.entrySet()) {
//			if (finalVarsAssertion.contains(entry.getValue())) {
//				finalInvarsAssertion.put(entry.getKey(), entry.getValue());
//			}
//		}
//		explicitNode.getSMTAnnotations().setInVars(finalInvarsAssertion);
//		explicitNode.getSMTAnnotations().setVars(finalVarsAssertion);
		//__________________________________________________________________//
		//																	//
		explicitNode.getSMTAnnotations().setInVars((HashMap<BoogieVar, TermVariable>)inVars.clone());
		explicitNode.getSMTAnnotations().setVars((HashSet<TermVariable>)vars.clone());

		for (INode successor: node.getOutgoingNodes()){
			CFGExplicitNode explicitSuccessor =  convert((CFGNode) successor, script, makeIdTags);
			CFGEdge edge = new CFGEdge(script, cfgNodeAnnotations.getAssumption(), explicitNode, explicitSuccessor);
//			edge.getPayload().getAnnotations().put("CFGBuilder", cfgNodeAnnotations);
			
			//__________________________________________________________________//
			// remove unnecessary variables from invars, vars and outvars of edge/
			
//			TermVariable[] freeVars = edge.getAssumption().getFreeVars();
//			HashMap<BoogieVar, TermVariable> finalInvarsAssumption = new HashMap<BoogieVar, TermVariable>();
//			HashMap<BoogieVar, TermVariable> finalOutvarsAssumption = new HashMap<BoogieVar, TermVariable>();
//			HashSet<TermVariable> finalVarsAssumption = new HashSet<TermVariable>();
//			
//			for(TermVariable freeVar: freeVars) {
//				finalVarsAssumption.add(freeVar);
//			}
//			
//			for(Entry<BoogieVar, TermVariable> entry: inVars.entrySet()) {
//				if (finalVarsAssumption.contains(entry.getValue())) {
//					finalInvarsAssumption.put(entry.getKey(), entry.getValue());
//				}
//			}
//			
//			for(Entry<BoogieVar, TermVariable> entry: outVars.entrySet()) {
//				if (finalVarsAssumption.contains(entry.getValue())) {
//					finalOutvarsAssumption.put(entry.getKey(), entry.getValue());
//				}
//			}
//			
//			edge.getSMTAnnotations().setInVars(finalInvarsAssumption);
//			edge.getSMTAnnotations().setOutVars(finalOutvarsAssumption);
//			edge.getSMTAnnotations().setVars(finalVarsAssumption);
			//__________________________________________________________________//
			//																	//
			
			edge.getSMTAnnotations().setInVars((HashMap<BoogieVar, TermVariable>)inVars.clone());
			edge.getSMTAnnotations().setOutVars((HashMap<BoogieVar, TermVariable>)outVars.clone());
			edge.getSMTAnnotations().setVars((HashSet<TermVariable>)vars.clone());
			edge.getPayload().setLocation(node.getPayload().getLocation());
			if (makeIdTags) {
				edge.makeId();
			}
		}
		logger.debug("Done making explicit node for " + node.getPayload().getName());
		return explicitNode;
	}
	
}
