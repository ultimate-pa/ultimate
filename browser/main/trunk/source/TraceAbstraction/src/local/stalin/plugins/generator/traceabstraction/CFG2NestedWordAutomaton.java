package local.stalin.plugins.generator.traceabstraction;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.core.api.StalinServices;
import local.stalin.logic.Atom;
import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.boogie.ast.AssumeStatement;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.plugins.generator.rcfgbuilder.CallEdge;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.InternalEdge;
import local.stalin.plugins.generator.rcfgbuilder.LocNode;
import local.stalin.plugins.generator.rcfgbuilder.ProgramPoint;
import local.stalin.plugins.generator.rcfgbuilder.RStateFormula;
import local.stalin.plugins.generator.rcfgbuilder.ReturnEdge;
import local.stalin.plugins.generator.rcfgbuilder.RootNode;
import local.stalin.plugins.generator.rcfgbuilder.RCfgState;
import local.stalin.plugins.generator.rcfgbuilder.StateFormula;
//import local.stalin.plugins.generator.rcfgbuilder.StateFormula;
import local.stalin.plugins.generator.rcfgbuilder.SummaryEdge;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;
import local.stalin.plugins.generator.rcfgbuilder.TransEdge;
import local.stalin.plugins.generator.rcfgbuilder.TransFormula;

import org.apache.log4j.Logger;

public class CFG2NestedWordAutomaton {
	
	private boolean m_Interprocedural;
	
	private static Logger s_Logger = 
					StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	public CFG2NestedWordAutomaton(boolean interprocedural) {
		m_Interprocedural = interprocedural;
	}
	
	
//	public static CState getCState(IProgramState iProgramState) {
//		CState rstate = new CState();
//		rstate.setProcedureName(iProgramState.getProcedureName());
//		rstate.setLocationName(iProgramState.getLocationName());
//		return rstate;
//	}

	
	public NestedWordAutomaton<TransAnnot,IProgramState>
									getNestedWordAutomaton(RootNode rootNode,
														   ContentFactory<IProgramState> tAContentFactory) {
		Set<LocNode> initialNodes = new HashSet<LocNode>();
		Set<LocNode> allNodes = new HashSet<LocNode>();
		
		Map<LocNode,IState<TransAnnot,IProgramState>>
			nodes2States = new HashMap<LocNode, IState<TransAnnot, IProgramState>>();
		
		Map<String, Procedure> implementations = 
			rootNode.getRootAnnot().getImplementations();
		
		s_Logger.debug("Step: put all LocationNodes into m_Nodes");
		
		// put all LocationNodes into m_Nodes
		LinkedList<LocNode> queue = new LinkedList<LocNode>();
		for (INode node : rootNode.getOutgoingNodes()) {
			LocNode locNode = (LocNode) node;
			// add only LocationNodes of implementations
			String procName = locNode.getStateAnnot().getProgramPoint().getProcedure();

			if (implementations.containsKey(procName)) {
				initialNodes.add(locNode);
				allNodes.add(locNode);
				queue.add(locNode);
			}
		}
		while (!queue.isEmpty()) {
			LocNode currentNode = queue.removeFirst();
			
			if (currentNode.getOutgoingNodes() != null)
				for (INode node : currentNode.getOutgoingNodes()) {
					LocNode nextNode = (LocNode) node;
					if ( !allNodes.contains(nextNode)) {
						allNodes.add(nextNode);
						queue.add(nextNode);
					}
				}
		}
		
		
		s_Logger.debug("Step: determine the alphabet");
		// determine the alphabet
		Set<TransAnnot> internalAlphabet = new HashSet<TransAnnot>();
		Set<TransAnnot> callAlphabet = new HashSet<TransAnnot>();
		Set<TransAnnot> returnAlphabet = new HashSet<TransAnnot>();
		
		for (LocNode locNode : allNodes) {
			if (locNode.getOutgoingNodes() != null)
			for (IEdge edge : locNode.getOutgoingEdges()) {
				if (edge instanceof InternalEdge) {
					internalAlphabet.add(
							((InternalEdge) edge).getInternalAnnotations());
				}
				if (edge instanceof SummaryEdge) {
					SummaryEdge summaryEdge = (SummaryEdge) edge;
					String procName = 
								summaryEdge.getCallStatement().getMethodName();
					if (m_Interprocedural && 
										implementations.containsKey(procName)) {
						//do noting
					}
					else {
						internalAlphabet.add(
										summaryEdge.getInternalAnnotations());
					}
				}
				if (m_Interprocedural && edge instanceof CallEdge) {
					callAlphabet.add( ((CallEdge) edge).getCallAnnotations());
				}
				if (m_Interprocedural && edge instanceof ReturnEdge) {
					returnAlphabet.add( 
							((ReturnEdge) edge).getReturnAnnotations());
				}
			}
		}
		
		s_Logger.debug("Step: construct the automaton");
		// construct the automaton
		NestedWordAutomaton<TransAnnot, IProgramState> nwa =
			new NestedWordAutomaton<TransAnnot, IProgramState>(
					internalAlphabet,
					callAlphabet,
					returnAlphabet,
					tAContentFactory);
		
		s_Logger.debug("Step: add states");
		// add states
		for (LocNode locNode : allNodes) {
			boolean isInitial = initialNodes.contains(locNode);
			boolean isErrorLocation = 
				locNode.getProgramPoint().isErrorLocation();
			IState<TransAnnot, IProgramState> automatonState;
			IProgramState programState;
			if (m_Interprocedural) {
				programState = new RStateFormula(rootNode.getRootAnnot().getTheory(),locNode.getProgramPoint());
				}
			else {
				programState = new StateFormula(locNode.getProgramPoint());
			}
			automatonState = nwa.addState(isInitial,
						 		 isErrorLocation,
						 		programState);
			nodes2States.put(locNode, automatonState);
			
//			// add transitions to the error location if correctness of the
//			// program can be violated at locNode
//			Map<AssumeStatement, TransFormula> violations = 
//					locNode.getStateAnnot().getViolations();
//			if (violations !=null) {
//				for (AssumeStatement st : violations.keySet()) {
//					TransAnnot transAnnot = new TransAnnot();
//					transAnnot.addStatement(st);
//					transAnnot.setTransitionFormula(violations.get(st));
//					internalAlphabet.add(transAnnot);
//					nwa.addInternalTransition(automatonState,transAnnot,automatonErrorState);
//				}
//			}
		}
		
		
		s_Logger.debug("Step: add transitions");
		// add transitions
		for (LocNode locNode : allNodes) {
			IState<TransAnnot, IProgramState> state = 
				nodes2States.get(locNode);
			if (locNode.getOutgoingNodes() != null)
			for (IEdge edge : locNode.getOutgoingEdges()) {
				LocNode succLoc = (LocNode) edge.getTarget();
				IState<TransAnnot, IProgramState> succState = 
					nodes2States.get(succLoc); 
				if (edge instanceof InternalEdge) {
					TransAnnot symbol = 
						((InternalEdge) edge).getInternalAnnotations();
					nwa.addInternalTransition(state,symbol, succState);
				}
				if (edge instanceof SummaryEdge) {
					SummaryEdge summaryEdge = (SummaryEdge) edge;
					String procName = 
								summaryEdge.getCallStatement().getMethodName();
					if (m_Interprocedural && 
										implementations.containsKey(procName)) {
						//do noting
					}
					else {
						TransAnnot symbol= summaryEdge.getInternalAnnotations();
						nwa.addInternalTransition(state,symbol, succState);
					}
				}
				if (m_Interprocedural && edge instanceof CallEdge) {
					TransAnnot symbol = 
						((CallEdge) edge).getCallAnnotations();
					nwa.addCallTransition(state,symbol, succState);

				}
				if (m_Interprocedural && edge instanceof ReturnEdge) {
					ReturnEdge returnEdge = (ReturnEdge) edge;
					TransAnnot symbol = returnEdge.getReturnAnnotations();
					LocNode callerLocNode = returnEdge.getCallerNode();
					nwa.addReturnTransition(state,nodes2States.get(callerLocNode), symbol, succState);
				}
			}
		}
		return nwa;
		
	}
}
