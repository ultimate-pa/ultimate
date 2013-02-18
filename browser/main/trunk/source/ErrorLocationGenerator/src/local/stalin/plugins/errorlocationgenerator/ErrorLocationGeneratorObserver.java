package local.stalin.plugins.errorlocationgenerator;

import java.util.HashMap;

import org.apache.log4j.Logger;
import local.stalin.SMTInterface.SMTInterface;
import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.boogie.cfgreducer.CFGEdge;
import local.stalin.boogie.cfgreducer.CFGExplicitNode;
import local.stalin.core.api.StalinServices;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.model.IEdge;
import local.stalin.model.IElement;

/**
 * This class checks all transitions for feasibility, creates error-nodes accordingly, and removes all non-error-nodes with no successor.
 * 
 */

public class ErrorLocationGeneratorObserver implements IUnmanagedObserver {

	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);

	private CFGExplicitNode m_Graphroot		= null;
	private CFGExplicitNode m_OldGraphroot	= null;
	private Theory			m_Theory		= null;
	private SMTInterface	m_SMTInterface	= null;

	HashMap<CFGExplicitNode, CFGExplicitNode>	m_NodeMapping		= new HashMap<CFGExplicitNode, CFGExplicitNode>();
	HashMap<CFGExplicitNode, CFGExplicitNode>	m_ErrorLocations	= new HashMap<CFGExplicitNode, CFGExplicitNode>();
	HashMap<String, TermVariable>				m_OldVars 			= new HashMap<String, TermVariable>();
	int											m_TheoremProverCalls= 0;
	public IElement getRoot(){
		return m_Graphroot;
	}
	
	@Override
	public boolean process(IElement root) {
		if (root instanceof CFGExplicitNode){
			m_OldGraphroot = (CFGExplicitNode)root;
			m_Theory = m_OldGraphroot.getTheory();
			m_SMTInterface = new SMTInterface(m_Theory, SMTInterface.SOLVER_GROUNDIFY);
			StalinServices.getInstance().putInToolchainStore("groundifier", m_SMTInterface);
			if (StalinServices.getInstance().getStoredObject("groundifier") == null)
				s_Logger.debug("StalinServices failed to store solver object!");
			m_Graphroot = makeProcedureCFG(m_OldGraphroot);
			//---------Benchmark data collection---------------
			s_Logger.info("BMdata:(Error Location Generator) >(3)ELG:TPC#=" + m_TheoremProverCalls);
		}
		return false;
	}
	
	private CFGExplicitNode makeProcedureCFG(CFGExplicitNode source){		
		if (source.getOutgoingEdges().size() < 1){
			return null;
		} else if (m_NodeMapping.containsKey(source)){
			return m_NodeMapping.get(source);
		} else {
			CFGExplicitNode source_Copy = source.copyWithoutEdges();
			m_NodeMapping.put(source, source_Copy);
			source_Copy.getPayload().setName(source.getPayload().getName());
			
			for (IEdge iedge: source.getOutgoingEdges()){
				CFGEdge edge = (CFGEdge)iedge;
				int validityCheck;
				if (source == m_OldGraphroot && edge.getTarget().getOutgoingEdges().size() < 1){
					validityCheck = SMTInterface.SMT_SAT;
				} else {
					validityCheck = edge.checkValidity();
					m_TheoremProverCalls++;
				}
				
//				validityCheck = edge.checkValidity();
				m_TheoremProverCalls++;
				
				if (!(validityCheck == SMTInterface.SMT_UNSAT)){
					CFGEdge errorEdge = makeErrorPath(edge);
					errorEdge.setSource(source_Copy);
				} else if (validityCheck == SMTInterface.SMT_ERROR){
					s_Logger.info("SMT solver returned an error message!");
					return null;
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
			errorNode.setAssertion(m_Theory.not(errorNode.getAssertion()));
			errorNode.getPayload().setName("ERROR_LOCATION" + target.getPayload().getName());
			m_ErrorLocations.put(target, errorNode);
		}
		errorEdge = edge.copyWithoutNodes();
		errorEdge.setTarget(errorNode);
		return errorEdge;
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
		return false;
	}
	
}