/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class CFG2NestedWordAutomaton {
	private final IUltimateServiceProvider m_Services;
	
	private final SmtManager m_SmtManager;
	private static final boolean m_StoreHistory = false;
	private final boolean m_Interprocedural;
	private boolean m_MainMode;
	private static final String m_StartProcedure = "ULTIMATE.start";
	
	private final Logger mLogger;
	
	public CFG2NestedWordAutomaton(IUltimateServiceProvider services, boolean interprocedural, SmtManager predicateFactory, Logger logger) {
		m_Services = services;
		mLogger = logger;
		m_SmtManager = predicateFactory;
		m_Interprocedural = interprocedural;
	}
	
	
	/**
	 * Construct the control automata (see Trace Abstraction) for the program
	 * of rootNode.
	 * If m_Interprocedural==false we construct an automaton for each procedure
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
			rootNode.getRootAnnot().getBoogieDeclarations().getProcImplementation();
		
		if (implementations.containsKey(m_StartProcedure)) {
			m_MainMode = true;
			mLogger.info("Mode: main mode - execution starts in main procedure");
		}
		else {
			m_MainMode = false;
			mLogger.info("Mode: library - executation can start in any procedure");
		}
				
		mLogger.debug("Step: put all LocationNodes into m_Nodes");
		
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
			if (currentNode.getOutgoingNodes() != null) {
				for (RCFGNode node : currentNode.getOutgoingNodes()) {
					ProgramPoint nextNode = (ProgramPoint) node;
					if ( !allNodes.contains(nextNode)) {
						allNodes.add(nextNode);
						queue.add(nextNode);
					}
				}
			}
		}
		
		
		mLogger.debug("Step: determine the alphabet");
		// determine the alphabet
		Set<CodeBlock> internalAlphabet = new HashSet<CodeBlock>();
		Set<CodeBlock> callAlphabet = new HashSet<CodeBlock>();
		Set<CodeBlock> returnAlphabet = new HashSet<CodeBlock>();
		
		for (ProgramPoint locNode : allNodes) {
			if (locNode.getOutgoingNodes() != null)
			for (RCFGEdge edge : locNode.getOutgoingEdges()) {
				if (edge instanceof Call) {
					if (m_Interprocedural) {
						callAlphabet.add( ((Call) edge));
					}
				} else if (edge instanceof Return) {
					if (m_Interprocedural) {
						returnAlphabet.add( 
								((Return) edge));
					}
				} else if (edge instanceof Summary) {
					Summary summaryEdge = (Summary) edge;
					Summary annot = summaryEdge;
					if (annot.calledProcedureHasImplementation()) {
						//do nothing if analysis is interprocedural
						//add summary otherwise
						if (!m_Interprocedural) {
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
		
		mLogger.debug("Step: construct the automaton");
		// construct the automaton
		NestedWordAutomaton<CodeBlock, IPredicate> nwa =
			new NestedWordAutomaton<CodeBlock, IPredicate>(new AutomataLibraryServices(m_Services), 
					internalAlphabet,
					callAlphabet,
					returnAlphabet,
					tAContentFactory);
		
		mLogger.debug("Step: add states");
		// add states
		for (ProgramPoint locNode : allNodes) {
			boolean isInitial = initialNodes.contains(locNode);
			boolean isErrorLocation = errorLocs.contains(locNode);

			IPredicate automatonState;
			TermVarsProc trueTvp = m_SmtManager.getPredicateFactory().constructTrue();
			if (m_StoreHistory) {
				automatonState = m_SmtManager.getPredicateFactory().newPredicateWithHistory(locNode, trueTvp, new HashMap<Integer, Term>());
			} else {
				automatonState = m_SmtManager.getPredicateFactory().newSPredicate(locNode, trueTvp); 
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
		
		
		mLogger.debug("Step: add transitions");
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
					if (m_Interprocedural) {
						CodeBlock symbol = 
								((Call) edge);
							nwa.addCallTransition(state,symbol, succState);
					}
				} else if (edge instanceof Return) {
					if (m_Interprocedural) {
						Return returnEdge = (Return) edge;
						CodeBlock symbol = returnEdge;
						ProgramPoint callerLocNode = returnEdge.getCallerProgramPoint();
						if (nodes2States.containsKey(callerLocNode)) {
							nwa.addReturnTransition(state,
								nodes2States.get(callerLocNode), symbol, succState);
						} else {
							mLogger.debug("Ommited insertion of " + symbol + 
									" because callerNode" + callerLocNode + " is deadcode");
						}
					}
				} else if (edge instanceof Summary) {
					Summary summaryEdge = (Summary) edge;
					if (summaryEdge.calledProcedureHasImplementation()) {
						if (!m_Interprocedural) {
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
