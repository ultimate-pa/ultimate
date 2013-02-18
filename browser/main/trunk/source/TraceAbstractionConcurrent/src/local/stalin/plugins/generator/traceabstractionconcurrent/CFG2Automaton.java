package local.stalin.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import local.stalin.automata.nwalibrary.ConcurrentProduct;
import local.stalin.automata.nwalibrary.ContentFactory;
import local.stalin.automata.nwalibrary.INestedWordAutomaton;
import local.stalin.automata.nwalibrary.IState;
import local.stalin.automata.nwalibrary.NestedWordAutomaton;
import local.stalin.automata.petrinet.jan.PetriNet;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.plugins.generator.rcfgbuilder.CallEdge;
import local.stalin.plugins.generator.rcfgbuilder.IProgramState;
import local.stalin.plugins.generator.rcfgbuilder.InternalEdge;
import local.stalin.plugins.generator.rcfgbuilder.LocNode;
import local.stalin.plugins.generator.rcfgbuilder.ReturnEdge;
import local.stalin.plugins.generator.rcfgbuilder.RootNode;
import local.stalin.plugins.generator.rcfgbuilder.StateFormula;
import local.stalin.plugins.generator.rcfgbuilder.SummaryEdge;
import local.stalin.plugins.generator.rcfgbuilder.TransAnnot;
import local.stalin.plugins.generator.rcfgbuilder.TransEdge;

import org.apache.log4j.Logger;

public abstract class CFG2Automaton {
	
	private static Logger s_Logger = 
				StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private final RootNode m_RootNode;
	private final ContentFactory<IProgramState> m_ContentFactory;
	
	private List<IProgramState> m_InitializeSharedVarsLocations =
		new LinkedList<IProgramState>();
	private List<TransAnnot> m_InitializeSharedVarsTransAnnots =
		new LinkedList<TransAnnot>();
	protected ArrayList<NestedWordAutomaton<TransAnnot,IProgramState>> m_Automata;
	
	
	public CFG2Automaton(RootNode rootNode,
			ContentFactory<IProgramState> contentFactory) {
		m_RootNode = rootNode;
		m_ContentFactory = contentFactory;
	}

	
	public abstract Object getResult();
		
	protected void constructProcedureAutomata() {
		Map<String, Procedure> implementations = 
			m_RootNode.getRootAnnot().getImplementations();
		
		if (!implementations.containsKey("InitializeSharedVariables")) {
			throw new IllegalArgumentException("Concurrent program needs" +
					" procedures that initializes sharedVariables");
		}
		
		LocNode initSharedVarsInitNode = m_RootNode.getRootAnnot().
							getInitialNodes().get("InitializeSharedVariables");
		extractSharedVarsInitialization(initSharedVarsInitNode);
		
		int numberOfProcedures = implementations.keySet().size()-1;
		
		m_Automata = 
			new ArrayList<NestedWordAutomaton<TransAnnot,IProgramState>>(numberOfProcedures);
		
		for (INode node : m_RootNode.getOutgoingNodes()) {
			LocNode initialNode = (LocNode) node;
			// add only LocationNodes of implementations
			String procName = initialNode.getStateAnnot().getProgramPoint().getProcedure();

			if (implementations.containsKey(procName) && 
					procName != "InitializeSharedVariables") {
				m_Automata.add(getNestedWordAutomaton(initialNode));
			}
		}
		assert (m_Automata.size() == numberOfProcedures);
	}
		

	
	private void extractSharedVarsInitialization(LocNode initialNode) {
		LocNode currentLocNode = initialNode;
		InternalEdge currentTransEdge;
		while (currentLocNode.getOutgoingEdges().size()>0) {
			if (currentLocNode.getOutgoingEdges().size()>1) {
				throw new IllegalArgumentException("InitializeSharedVars" +
						"procedure must be a sequence of assignments");
			}
			currentTransEdge = 
				(InternalEdge) currentLocNode.getOutgoingEdges().get(0);
			m_InitializeSharedVarsLocations.add(currentLocNode.getStateAnnot());
			currentLocNode = (LocNode) currentTransEdge.getTarget();
			m_InitializeSharedVarsTransAnnots.add(
									currentTransEdge.getInternalAnnotations());
		}
		if (m_InitializeSharedVarsLocations.isEmpty()) {
			throw new IllegalArgumentException("InitializeSharedVars" +
			"procedure must contain at least one statement");
		}
	}
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	private NestedWordAutomaton<TransAnnot,IProgramState> getNestedWordAutomaton(LocNode initialNode) {
		
		s_Logger.debug("Step: Collect all LocNodes corresponding to" +
				" this procedure");
		
		LinkedList<LocNode> queue = new LinkedList<LocNode>();
		Set<LocNode> allNodes = new HashSet<LocNode>();
		queue.add(initialNode);
		allNodes.add(initialNode);

		while (!queue.isEmpty()) {
			LocNode currentNode = queue.removeFirst();
			
			if (currentNode.getOutgoingNodes() != null) {
				for (INode node : currentNode.getOutgoingNodes()) {
					LocNode nextNode = (LocNode) node;
					if ( !allNodes.contains(nextNode)) {
						allNodes.add(nextNode);
						queue.add(nextNode);
					}
				}
			}
		}
		
		
		
		s_Logger.debug("Step: determine the alphabet");
		// determine the alphabet
		Set<TransAnnot> internalAlphabet = new HashSet<TransAnnot>();
		Set<TransAnnot> callAlphabet = new HashSet<TransAnnot>(0);
		Set<TransAnnot> returnAlphabet = new HashSet<TransAnnot>(0);
		
		// add transAnnot from sharedVars initialization
		for (TransAnnot transAnnot : m_InitializeSharedVarsTransAnnots) {
			internalAlphabet.add(transAnnot);
		}
		
		for (LocNode locNode : allNodes) {
			if (locNode.getOutgoingNodes() != null)
			for (IEdge edge : locNode.getOutgoingEdges()) {
				if (edge instanceof InternalEdge) {
					internalAlphabet.add(
							((InternalEdge) edge).getInternalAnnotations());
				}
				else if (edge instanceof SummaryEdge) {
					throw new IllegalArgumentException("Procedure calls not" +
							" supported by concurrent trace abstraction");
				}
				else if (edge instanceof CallEdge) {
					throw new IllegalArgumentException("Procedure calls not" +
							" supported by concurrent trace abstraction");
				}
				else if (edge instanceof ReturnEdge) {
					throw new IllegalArgumentException("Procedure calls not" +
							" supported by concurrent trace abstraction");
				}
				else {
					throw new  IllegalArgumentException("unknown type of edge");
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
					m_ContentFactory);
		
		IState<TransAnnot,IProgramState> procedureInitialState = null;
		
		s_Logger.debug("Step: add states");
		Map<LocNode,IState<TransAnnot,IProgramState>>
		nodes2States = new HashMap<LocNode, IState<TransAnnot, IProgramState>>();
		// add states
		for (LocNode locNode : allNodes) {
			boolean isErrorLocation = 
				locNode.getProgramPoint().isErrorLocation();
			IState<TransAnnot, IProgramState> automatonState;
			IProgramState programState = 
				new StateFormula(locNode.getProgramPoint());

			automatonState = nwa.addState(false,
						 		 isErrorLocation,
						 		programState);
			nodes2States.put(locNode, automatonState);
			if (locNode == initialNode) {
				assert (procedureInitialState == null) : "Procedure must have" +
				"only one initial state";
				procedureInitialState = automatonState;
			}
			
		}
		
		s_Logger.debug("Step: add transitions");
		// add transitions
		for (LocNode locNode : allNodes) {
			IState<TransAnnot, IProgramState> state = 
				nodes2States.get(locNode);
			if (locNode.getOutgoingNodes() != null) {
				for (IEdge edge : locNode.getOutgoingEdges()) {
					LocNode succLoc = (LocNode) edge.getTarget();
					IState<TransAnnot, IProgramState> succState = 
						nodes2States.get(succLoc); 
					if (edge instanceof InternalEdge) {
						TransAnnot symbol = 
							((InternalEdge) edge).getInternalAnnotations();
						nwa.addInternalTransition(state,symbol, succState);
					}
					else {
						throw new IllegalArgumentException(
													"unknown type of edge");
					}
				}
			}			
		}
		
		s_Logger.debug("Step: SharedVarsInit part");
		IProgramState initialContent = new StateFormula(
					m_InitializeSharedVarsLocations.get(0).getProgramPoint());
		IState<TransAnnot, IProgramState> automatonState = nwa.addState(true,
		 		 										false, initialContent);
		IState<TransAnnot, IProgramState> automatonSuccState;
		for (int i=0; i<m_InitializeSharedVarsLocations.size()-1; i++) {
			IProgramState succContent = new StateFormula(				
					m_InitializeSharedVarsLocations.get(i+1).getProgramPoint());
			automatonSuccState = nwa.addState(false, false, succContent);
			TransAnnot transAnnot = m_InitializeSharedVarsTransAnnots.get(i);
			nwa.addInternalTransition(automatonState, transAnnot, 
															automatonSuccState);
			automatonState = automatonSuccState;
		}
		automatonSuccState = procedureInitialState;
		TransAnnot transAnnot = m_InitializeSharedVarsTransAnnots.get(
									m_InitializeSharedVarsLocations.size()-1);
		nwa.addInternalTransition(automatonState,transAnnot,automatonSuccState);
		
		return nwa;
	}
			
			
			
			
			
			
		
		

}
