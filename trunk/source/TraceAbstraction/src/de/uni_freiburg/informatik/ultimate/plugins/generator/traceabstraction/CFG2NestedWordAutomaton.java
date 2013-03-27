package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.structure.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.model.structure.IMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

public class CFG2NestedWordAutomaton {
	
	private final SmtManager m_SmtManager;
	private boolean m_StoreHistory = false;
	private TAPreferences m_Pref;
	private boolean m_MainMode;
	private final String m_StartProcedure = "ULTIMATE.start";
	
	private static Logger s_Logger = 
					UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	public CFG2NestedWordAutomaton(TAPreferences pref, SmtManager predicateFactory) {
		m_SmtManager = predicateFactory;
		m_Pref = pref;
	}
	
	
	/**
	 * Construct the control automata (see Trace Abstraction) for the program
	 * of rootNode.
	 * If m_Pref.interprocedural()==false we construct an automaton for each procedure
	 * otherwise we construct one nested word automaton for the whole program.
	 * @param errorLoc error location of the program. If null, each state that
	 * corresponds to an error location will be accepting. Otherwise only the
	 * state corresponding to errorLoc will be accepting.
	 */
	public NestedWordAutomaton<CodeBlock,IPredicate> getNestedWordAutomaton(
							RootNode rootNode,
							StateFactory<IPredicate> tAContentFactory,
							Collection<ProgramPoint> errorLocs) {
		Set<ProgramPoint> initialNodes = new HashSet<ProgramPoint>();
		Set<ProgramPoint> allNodes = new HashSet<ProgramPoint>();
		
		Map<ProgramPoint,IPredicate> nodes2States = 
					new HashMap<ProgramPoint, IPredicate>();
		
		Map<String, Procedure> implementations = 
			rootNode.getRootAnnot().getImplementations();
		
		if (implementations.containsKey(m_StartProcedure)) {
			m_MainMode = true;
			s_Logger.info("Mode: main mode - execution starts in main procedure");
		}
		else {
			m_MainMode = false;
			s_Logger.info("Mode: library - executation can start in any procedure");
		}
				
		s_Logger.debug("Step: put all LocationNodes into m_Nodes");
		
		// put all LocationNodes into m_Nodes
		LinkedList<ProgramPoint> queue = new LinkedList<ProgramPoint>();
		for (RCFGNode node : rootNode.getOutgoingNodes()) {
			ProgramPoint locNode = (ProgramPoint) node;
			// add only LocationNodes of implementations
			String procName = locNode.getProcedure();

			if (implementations.containsKey(procName)) {
				if (!m_MainMode || procName.equals(m_StartProcedure)) {
					initialNodes.add(locNode);
				}
				allNodes.add(locNode);
				queue.add(locNode);
			}
		}
		while (!queue.isEmpty()) {
			ProgramPoint currentNode = queue.removeFirst();
			
			if (currentNode.getOutgoingNodes() != null)
				for (RCFGNode node : currentNode.getOutgoingNodes()) {
					ProgramPoint nextNode = (ProgramPoint) node;
					if ( !allNodes.contains(nextNode)) {
						allNodes.add(nextNode);
						queue.add(nextNode);
					}
				}
		}
		
		
		s_Logger.debug("Step: determine the alphabet");
		// determine the alphabet
		Set<CodeBlock> internalAlphabet = new HashSet<CodeBlock>();
		Set<CodeBlock> callAlphabet = new HashSet<CodeBlock>();
		Set<CodeBlock> returnAlphabet = new HashSet<CodeBlock>();
		
		for (ProgramPoint locNode : allNodes) {
			if (locNode.getOutgoingNodes() != null)
			for (RCFGEdge edge : locNode.getOutgoingEdges()) {
				if (edge instanceof Call) {
					if (m_Pref.interprocedural()) {
						callAlphabet.add( ((Call) edge));
					}
				} else if (edge instanceof Return) {
					if (m_Pref.interprocedural()) {
						returnAlphabet.add( 
								((Return) edge));
					}
				} else if (edge instanceof Summary) {
					Summary summaryEdge = (Summary) edge;
					Summary annot = summaryEdge;
					if (annot.calledProcedureHasImplementation()) {
						//do nothing if analysis is interprocedural
						//add summary otherwise
						if (!m_Pref.interprocedural()) {
							internalAlphabet.add(annot);
						}
					}
					else {
						internalAlphabet.add(annot);
					}
				} else if (edge instanceof CodeBlock) {
					internalAlphabet.add(((CodeBlock) edge));
				} else {
					throw new UnsupportedOperationException("unknown edge" + edge);
				}
			}
		}
		
		s_Logger.debug("Step: construct the automaton");
		// construct the automaton
		NestedWordAutomaton<CodeBlock, IPredicate> nwa =
			new NestedWordAutomaton<CodeBlock, IPredicate>(
					internalAlphabet,
					callAlphabet,
					returnAlphabet,
					tAContentFactory);
		
		s_Logger.debug("Step: add states");
		// add states
		for (ProgramPoint locNode : allNodes) {
			boolean isInitial = initialNodes.contains(locNode);
			boolean isErrorLocation = errorLocs.contains(locNode);

			IPredicate automatonState;
			if (m_StoreHistory) {
				automatonState = m_SmtManager.newTrueSLPredicateWithHistory(locNode);
			} else {
				automatonState = m_SmtManager.newTrueSLPredicate(locNode); 
			}
					
			nwa.addState(isInitial, isErrorLocation, automatonState);
			nodes2States.put(locNode, automatonState);
			
//			// add transitions to the error location if correctness of the
//			// program can be violated at locNode
//			Map<AssumeStatement, TransFormula> violations = 
//					locNode.getStateAnnot().getViolations();
//			if (violations !=null) {
//				for (AssumeStatement st : violations.keySet()) {
//					TransAnnot transAnnot = new TransAnnot();
//					transAnnot.addStatement(st);
//					transAnnot.setTransitionTerm(violations.get(st));
//					internalAlphabet.add(transAnnot);
//					nwa.addInternalTransition(automatonState,transAnnot,automatonErrorState);
//				}
//			}
		}
		
		
		s_Logger.debug("Step: add transitions");
		// add transitions
		for (ProgramPoint locNode : allNodes) {
			IPredicate state = 
				nodes2States.get(locNode);
			if (locNode.getOutgoingNodes() != null)
			for (RCFGEdge edge : locNode.getOutgoingEdges()) {
				ProgramPoint succLoc = (ProgramPoint) edge.getTarget();
				IPredicate succState = 
					nodes2States.get(succLoc); 
				if (edge instanceof Call) {
					if (m_Pref.interprocedural()) {
						CodeBlock symbol = 
								((Call) edge);
							nwa.addCallTransition(state,symbol, succState);
					}
				} else if (edge instanceof Return) {
					if (m_Pref.interprocedural()) {
						Return returnEdge = (Return) edge;
						CodeBlock symbol = returnEdge;
						ProgramPoint callerLocNode = returnEdge.getCallerNode();
						nwa.addReturnTransition(state,
								nodes2States.get(callerLocNode), symbol, succState);
					}
				} else if (edge instanceof Summary) {
					Summary summaryEdge = (Summary) edge;
					if (summaryEdge.calledProcedureHasImplementation()) {
						if (!m_Pref.interprocedural()) {
							nwa.addInternalTransition(state,summaryEdge, succState);
						}
					}
					else {
						nwa.addInternalTransition(state, summaryEdge, succState);
					}
				} else if (edge instanceof CodeBlock) {
					CodeBlock symbol = ((CodeBlock) edge);
						nwa.addInternalTransition(state,symbol, succState);
				} else {
					throw new UnsupportedOperationException("unknown edge" + edge);
				}
			}
		}
		return nwa;	
	}
}
