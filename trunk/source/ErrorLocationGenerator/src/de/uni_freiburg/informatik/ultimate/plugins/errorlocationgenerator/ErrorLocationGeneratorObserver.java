package de.uni_freiburg.informatik.ultimate.plugins.errorlocationgenerator;

import java.util.ArrayList;
import java.util.HashMap;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableSSAManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.SubstituteTermTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.errorlocationgenerator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.errorlocationgenerator.preferences.PreferenceValues;

/**
 * This class checks all transitions for feasibility, creates error-nodes accordingly, and removes all non-error-nodes with no successor.
 * 
 */

public class ErrorLocationGeneratorObserver implements IUnmanagedObserver {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	private CFGExplicitNode m_Graphroot		= null;
	private CFGExplicitNode m_OldGraphroot	= null;
	private Script			m_Script		= null;
//	private SMTInterface	m_SMTInterface	= null;
	private Boolean 		m_checkValidity	= true;
	private Boolean 		m_checkDeadCode	= true;
//	private static HashMap<BoogieVar, CFGEdge> s_edge2IdMapping = null;
	private static ArrayList<BoogieVar> s_edgeIds = null;
	private BoogieVar		m_currentlyObservedEdgeId = null;
//	private Term			m_idWildCard	= null; 
	private boolean			m_checkReachabilityOfHybridSystem = false;
	
	HashMap<CFGExplicitNode, CFGExplicitNode>	m_NodeMapping		= new HashMap<CFGExplicitNode, CFGExplicitNode>();
	HashMap<CFGExplicitNode, CFGExplicitNode>	m_ErrorLocations	= new HashMap<CFGExplicitNode, CFGExplicitNode>();
	HashMap<CFGExplicitNode, CFGExplicitNode>	m_reachabilityCheckNodes	= new HashMap<CFGExplicitNode, CFGExplicitNode>();
//	HashMap<String, TermVariable>				m_OldVars 			= new HashMap<String, TermVariable>();
	int											m_TheoremProverCalls= 0;

//	private CFGExplicitNode m_deadCodeNode = null;
	
	public IElement getRoot(){
		return m_Graphroot;
	}
	
	@Override
	public boolean process(IElement root) {
		clearHistory();
		if (root instanceof CFGExplicitNode){
			m_OldGraphroot = (CFGExplicitNode)root;
			m_Script = m_OldGraphroot.getScript();
			
			IEclipsePreferences prefs = ConfigurationScope.INSTANCE.getNode(Activator.PLUGIN_ID);
			m_checkValidity = prefs.getBoolean(PreferenceValues.NAME_CHECKVALIDITYOFERROREDGE, PreferenceValues.VALUE_CHECKVALIDITYOFERROREDGE_DEFAULT);
			m_checkDeadCode = prefs.getBoolean(PreferenceValues.NAME_CHECKFORDEADCODE, PreferenceValues.VALUE_CHECKFORDEADCODE_DEFAULT);
			m_checkReachabilityOfHybridSystem = prefs.getBoolean(PreferenceValues.NAME_CHECKREACHABILITY, PreferenceValues.VALUE_CHECKREACHABILITY_DEFAULT);
			
			if (m_checkDeadCode){
				initializeDeadCodeAnalysis();
			}
			
			// If model is an EFG
			IEdge efgProcedureEdge = null;
			for (IEdge edge: m_OldGraphroot.getOutgoingEdges()) {
				if (edge.getPayload().getName().contains("EFG_Procedure")) {
					efgProcedureEdge = edge;
				}
			}
			if (efgProcedureEdge != null) {
				CFGExplicitNode newGraphroot = m_OldGraphroot.copyWithoutEdges();
				newGraphroot.addOutgoingEdge(efgProcedureEdge);
				m_OldGraphroot = newGraphroot;
			}
			
			try {
				m_Graphroot = makeProcedureCFG(m_OldGraphroot);
			} catch (SMTLIBException e) {
				s_Logger.info("SMT solver returned an error message: " + e.getMessage());
				throw e;
			}
			
			if (m_checkDeadCode){
				setAssumptionForDeadCodeAnalysis();
			}
			
			//---------Benchmark data collection---------------
			s_Logger.info("BMdata:(Error Location Generator) >(3)ELG:TPC#=" + m_TheoremProverCalls);
		}
		return false;
	}
	
	private void clearHistory() {
		m_Graphroot		= null;
		m_OldGraphroot	= null;
		m_Script		= null;
		m_checkValidity	= true;
		m_checkDeadCode	= true;
		m_checkReachabilityOfHybridSystem = false;
		
		m_NodeMapping		= new HashMap<CFGExplicitNode, CFGExplicitNode>();
		m_ErrorLocations	= new HashMap<CFGExplicitNode, CFGExplicitNode>();
		//m_OldVars 			= new HashMap<String, TermVariable>();
		m_TheoremProverCalls= 0;
		
		m_currentlyObservedEdgeId = null;
	}
	
	private LBool checkValidity(CFGEdge edge) {
		LBool result;
		if (edge.getSource() != m_OldGraphroot && 
				((edge.getSource() == m_OldGraphroot && edge.getTarget().getOutgoingEdges().size() < 1))){
			result = LBool.SAT;
		} else if (m_checkValidity) {
			try {
				result = edge.checkValidity();
				m_TheoremProverCalls++;
			} catch (SMTLIBException e) {
				throw e;
			}
		} else {
			if (((CFGExplicitNode)edge.getTarget()).getAssertion().equals(m_Script.term("true"))) {
				result = LBool.UNSAT;
			} else {
				result = LBool.SAT;
			}
		}
		return result;
	}
	
	private CFGExplicitNode makeProcedureCFG(CFGExplicitNode source){
		if (m_NodeMapping.containsKey(source)){
			return m_NodeMapping.get(source);
		} else if (source.getOutgoingEdges().size() < 1){
			return null;
		} else {
			CFGExplicitNode source_Copy = source.copyWithoutEdges();
			m_NodeMapping.put(source, source_Copy);
			source_Copy.getPayload().setName(source.getPayload().getName());
			
			for (IEdge iedge: source.getOutgoingEdges()){
				CFGEdge edge = (CFGEdge)iedge;
				LBool validityCheck = checkValidity(edge);
				
				if (!(validityCheck == LBool.UNSAT)){
					CFGEdge errorEdge = makeErrorPath(edge);
					errorEdge.setSource(source_Copy);
					replaceIDWildCard((CFGExplicitNode)errorEdge.getTarget());
					replaceIDWildCard(source_Copy);
				}
				
				//--------------------------------------
//				CFGEdge errorEdge = makeErrorPath(edge);
//				errorEdge.setSource(source_Copy);
				//--------------------------------------
				
				CFGExplicitNode successor_Copy = null;
				if (edge.getTarget() == source){
					successor_Copy = source_Copy;
				} else{
					successor_Copy = makeProcedureCFG((CFGExplicitNode)edge.getTarget());
				}
				
				if (successor_Copy != null){
					CFGEdge edge_Copy = edge.copyWithoutNodes();
					edge_Copy.setSource(source_Copy);
					edge_Copy.setTarget(successor_Copy);
				}
			}
			if (m_checkReachabilityOfHybridSystem && source != m_OldGraphroot) {
				makeNodeForReachabilityCheck(source_Copy);
			}
			if (source_Copy.getOutgoingEdges().isEmpty()){
				return null;
			} else {
				return source_Copy;
			}
		}
	}
	
	// makes an error node and its ingoing edge, which is returned
	private CFGEdge makeErrorPath(CFGEdge edge){
		CFGExplicitNode target 		= (CFGExplicitNode)edge.getTarget();
		CFGEdge		 	errorEdge	= null;
		CFGExplicitNode errorNode	= null;

		if (m_ErrorLocations.containsKey(target)){
			errorNode = m_ErrorLocations.get(target);
		} else {
			errorNode = target.copyWithoutEdgesWithSSA();
			errorNode.setAssertion(Util.not(m_Script, errorNode.getAssertion()));
			errorNode.getPayload().setName("ERROR_LOCATION" + target.getPayload().getName());
			m_ErrorLocations.put(target, errorNode);
		}
		errorEdge = edge.copyWithoutNodes();
		errorEdge.setTarget(errorNode);
		return errorEdge;
	}

	private void makeNodeForReachabilityCheck(CFGExplicitNode node) {
		CFGExplicitNode errorNode	= null;

		if (m_reachabilityCheckNodes.containsKey(node)){
			errorNode = m_reachabilityCheckNodes.get(node);
		} else {
			errorNode = new CFGExplicitNode(m_Script, null);
			errorNode.getPayload().setName("ERROR_If_Reached_" + node.getPayload().getName());
			m_reachabilityCheckNodes.put(node, errorNode);
		}
		CFGEdge errorEdge = new CFGEdge(m_Script, null, node, errorNode);
		node.addOutgoingEdge(errorEdge);
		return;
	}
	
	private void replaceIDWildCard(CFGExplicitNode node) {
		if (m_checkDeadCode)
		{
			if (node.getSMTAnnotations().getInVars().containsKey("LOC_ID"))
			{
				TermVariable wildCard = node.getSMTAnnotations().getInVars().get("LOC_ID");
				TermVariable freshIdVar = node.getSMTAnnotations().getInVars().get(m_currentlyObservedEdgeId);
				if (freshIdVar == null) {
					//TODO either label is part of left hand of implication or ... well, not sure but seems to act correctly
					node.setAssertion(m_Script.term("true"));
				} else {
					node.setAssertion(Util.and(m_Script,  m_Script.term("=", wildCard, freshIdVar), node.getAssertion()));
				}
				if (freshIdVar == null) {
					freshIdVar	= VariableSSAManager.getFreshTermVariable(m_currentlyObservedEdgeId, m_Script.sort("Bool"));
					
					node.getSMTAnnotations().getInVars().put(m_currentlyObservedEdgeId, freshIdVar);
					node.getSMTAnnotations().getVars().add(freshIdVar);
				}
				SubstituteTermTransformer subTermTransformer = new SubstituteTermTransformer();
				subTermTransformer.substitute(node.getAssertion(), wildCard, freshIdVar);
//				node.setAssertion(m_Script.let(wildCard, freshIdVar, node.getAssertion()));
				node.getSMTAnnotations().getInVars().remove("LOC_ID");
			}
		}
	}
	
	private void initializeDeadCodeAnalysis() {
		if (s_edgeIds == null) {
			s_edgeIds = new ArrayList<BoogieVar>();
			s_edgeIds.addAll(((CFGEdge)m_OldGraphroot.getOutgoingEdges().get(0)).getAllEdgeIds().keySet());
		}
//		m_currentlyObservedEdgeId = VariableSSAManager.getBoogieVariable(s_edgeIds.remove(0));
		m_currentlyObservedEdgeId = s_edgeIds.remove(0);
		s_Logger.info("Checking if block " + m_currentlyObservedEdgeId.toString() + " is dead code... if SC returns SAFE then block is dead code!");
	}
	
	private void setAssumptionForDeadCodeAnalysis() {
		for (IEdge e1: m_Graphroot.getOutgoingEdges()){
			for (IEdge e2: e1.getTarget().getOutgoingEdges()) {
				CFGEdge procNodeEdges = (CFGEdge)e2;

				if (!procNodeEdges.getSMTAnnotations().getOutVars().containsKey(m_currentlyObservedEdgeId)) {
					TermVariable freshIdVar = VariableSSAManager.getFreshTermVariable(m_currentlyObservedEdgeId, m_Script.sort("Bool"));
					procNodeEdges.getSMTAnnotations().getVars().add(freshIdVar);
					procNodeEdges.getSMTAnnotations().getOutVars().put(m_currentlyObservedEdgeId, freshIdVar);
					Term assumption = m_Script.term("=", freshIdVar, m_Script.term("false")); //TODO was 0, is 0 false or true?
					procNodeEdges.setAssumption(m_Script.term("and", procNodeEdges.getAssumption(),assumption));
				}
			}
		}
	}
	
	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		if (s_edgeIds != null)
			return (s_edgeIds.size() > 0);
		return true;
	}
	
}