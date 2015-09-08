/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Thomas Lang
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.AutomatonSccComputation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * TODO: comment
 * 
 * 
 * @author Thomas Lang
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class LoopComplexity<LETTER, STATE> implements IOperation<LETTER, STATE> {	
	
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Operand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Graph;
	private final Integer m_Result;
	
	private HashMap<Set<STATE>, Integer> statesToLC = new HashMap<Set<STATE>, Integer>();
	
	
	public LoopComplexity(IUltimateServiceProvider services,
			INestedWordAutomaton<LETTER, STATE> operand) throws AutomataLibraryException {
		super();
		
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		
		if (operand instanceof NestedWordAutomatonReachableStates) {
			m_Operand = (NestedWordAutomatonReachableStates<LETTER, STATE>) operand;
		} else {
			m_Operand = (new RemoveUnreachable<LETTER, STATE>(m_Services, operand)).getResult();
		}
		
		// Build graph from m_Operand.
		HashSet<LETTER> singletonLetter = new HashSet<LETTER>();
		LETTER internalLetter = m_Operand.getInternalAlphabet().iterator().next();
		singletonLetter.add(internalLetter);
		NestedWordAutomaton<LETTER, STATE> graph = new NestedWordAutomaton<LETTER, STATE>(m_Services, singletonLetter, singletonLetter, singletonLetter, m_Operand.getStateFactory());
		Set<STATE> states = m_Operand.getStates();
				
		for (STATE q : states) {
			graph.addState(true, true, q);
		}
				
		for (LETTER l : m_Operand.getInternalAlphabet()) {
			for (STATE q1 : states) {
				// Check for cancel button.
				if (!m_Services.getProgressMonitorService().continueProcessing()) {
					throw new OperationCanceledException(this.getClass());
				}
				for (STATE q2 : states) {
					if (m_Operand.containsInternalTransition(q1, l, q2)) {
						if (!graph.containsInternalTransition(q1, internalLetter, q2)) {
							graph.addInternalTransition(q1, internalLetter, q2);
						}
					}
				}
			}
		}
				
		m_Graph = (new RemoveUnreachable<LETTER, STATE>(m_Services, graph)).getResult();
		
		m_Logger.info(this.startMessage());
		
		m_Result = compute(m_Graph.getStates());
		m_Logger.info(this.exitMessage());
	}

	// Compute the loop complexity of the subgraph of m_Graph specified by 'states'.
	private Integer compute(Set<STATE> states) throws AutomataLibraryException {

		AutomatonSccComputation<LETTER, STATE> sccComputer = new AutomatonSccComputation<LETTER, STATE>(m_Graph, m_Services, states, states);
		
     	Collection<StronglyConnectedComponent<STATE>> balls = sccComputer.getBalls();

     	for (StronglyConnectedComponent<STATE> scc : balls) {
			scc.getNodes();
		}
     	
		// Graph contains no balls.
		if (balls.isEmpty()) {
			return 0;
		} else if (balls.size() == 1) { // Graph itself is a ball.
			// Consider all subgraphs differing from original graph by one vertex.
			
			Collection<STATE> peakStates = new ArrayList<STATE>();
			
			// Determine number of predecessors and successors for each state.
			for (STATE q : states) {
				int pCount = 0;
				int sCount = 0;
				
				Iterable<IncomingInternalTransition<LETTER, STATE>> preds = m_Graph.internalPredecessors(q);
				Iterable<OutgoingInternalTransition<LETTER, STATE>> succs = m_Graph.internalSuccessors(q);
				
				for (@SuppressWarnings("unused") IncomingInternalTransition<LETTER, STATE> p : preds) {
					++pCount;
				}
				
				for (@SuppressWarnings("unused") OutgoingInternalTransition<LETTER, STATE> s : succs) {
					++sCount;
				}
				
				// Add all those states with the maximum number of edges to peakStates.
				if (pCount != 1 || sCount != 1) {
				  peakStates.add(q);
				}
			}
			
			// If every state has one predecessor and one successor, the ball is a cycle.
			if (peakStates.isEmpty()) {
				return 1;
			}
			
			Collection<Integer> subGraphLoopComplexities = new ArrayList<Integer>();

			// Create a copy since 'peakStates' itself should not be modified.
			Set<STATE> copyStates = new HashSet<STATE>(states);

			for (STATE stateOut : peakStates) {
				// Check for cancel button.
				if (!m_Services.getProgressMonitorService().continueProcessing()) {
					throw new OperationCanceledException(this.getClass());
				}
				
				copyStates.remove(stateOut);
				
				if (statesToLC.containsKey(copyStates)) {
					subGraphLoopComplexities.add(statesToLC.get(copyStates));
				} else {
					Integer i = this.compute(copyStates);
					
					// Create another copy to prevent HashMap from not
					// recognizing sets of states after they have been modified.
					Set<STATE> keyStates = new HashSet<STATE>(copyStates);
					statesToLC.put(keyStates, i);
					
					subGraphLoopComplexities.add(i);
				}
				
				copyStates.add(stateOut);
			}
			
			return 1 + Collections.min(subGraphLoopComplexities);
		} else { // Graph itself is not a ball.		
			Collection<Integer> ballLoopComplexities = new ArrayList<Integer>();

			// Compute Loop Complexity for each ball.
		    for (StronglyConnectedComponent<STATE> scc : balls) {
		    	if (statesToLC.containsKey(scc.getNodes())) {
				  ballLoopComplexities.add(statesToLC.get(scc.getNodes()));
			    } else {
			      Integer i = this.compute(scc.getNodes());
					
			      Set<STATE> keyStates = new HashSet<STATE>(scc.getNodes());
			      statesToLC.put(keyStates, i);
					
			      ballLoopComplexities.add(i);
			    }
		     }
			
			 return Collections.max(ballLoopComplexities);
		}
	}

	@Override
	public String operationName() {
		return "loopComplexity";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand " + 
				m_Operand.sizeInformation();	
	}

	@Override
	public String exitMessage() {
		return "test";
	}

	@Override
	public Integer getResult() throws AutomataLibraryException {
		return m_Result;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// TODO Auto-generated method stub
		return true;
	}
}
