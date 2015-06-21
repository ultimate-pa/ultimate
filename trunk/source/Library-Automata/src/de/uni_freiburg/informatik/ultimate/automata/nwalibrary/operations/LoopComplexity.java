/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.AcceptingComponentsAnalysis.StronglyConnectedComponentWithAcceptanceInformation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

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
		
		m_Logger.info(this.startMessage());
		
		m_Result = compute(m_Operand.getStates());
		m_Logger.info(this.exitMessage());
	}

	private Integer compute(Set<STATE> states) throws AutomataLibraryException {

		Set<STATE> allStates = states;
		Set<STATE> initialStates = states;
     	Collection<StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE>> balls = m_Operand.computeBalls(allStates, initialStates);

     	for (StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE> scc : balls) {
			scc.getNodes();
		}
     	
		// Graph contains no balls.
		if (balls.isEmpty()) {
			return 0;
		} else if (balls.size() == 1) { // Graph itself is a ball.
			// Consider all subgraphs differing from original graph by one vertex.
			
			int maxEdges = 0;	
			Collection<STATE> allstates = new ArrayList<STATE>();
			
			// Determine number of predecessors and successors for each state.
			for (STATE q : states) {
				int pCount = 0;
				int sCount = 0;
				
				Iterable<IncomingInternalTransition<LETTER, STATE>> preds = m_Operand.internalPredecessors(q);
				Iterable<OutgoingInternalTransition<LETTER, STATE>> succs = m_Operand.internalSuccessors(q);
				
				for (IncomingInternalTransition<LETTER, STATE> p : preds) {
					++pCount;
					
					/*if (pCount > 1) {
						break;
					}*/
				}
				
				for (OutgoingInternalTransition<LETTER, STATE> s : succs) {
					++sCount;
					
					/*if (sCount > 1) {
						break;
					}*/
				}
				
				// Add all those states with the maximum number of edges to allstates.
				if (pCount != 1 || sCount != 1) {
				  if (pCount + sCount == maxEdges) {
					  allstates.add(q);
				  }
				  
				  if (pCount + sCount > maxEdges) {
					  maxEdges = pCount + sCount;
					  allstates.clear();
					  allstates.add(q);
				  }
				}
			}
			
			// If every state has one predecessor and one successor, the ball is a cycle.
			if (allstates.isEmpty()) {
				return 1;
			}
			
			Collection<Integer> subGraphLoopComplexities = new ArrayList<Integer>();

			// Create a copy since 'allstates' itself should not be modified.
			Set<STATE> copyStates = new HashSet<STATE>(allstates);

			for (STATE stateOut : allstates) {
				// Check for cancel button.
				if (!m_Services.getProgressMonitorService().continueProcessing()) {
					throw new ToolchainCanceledException(this.getClass());
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
		    for (StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE> scc : balls) {
		    	if (statesToLC.containsKey(scc.getAllStates())) {
				  ballLoopComplexities.add(statesToLC.get(scc.getAllStates()));
			    } else {
			      Integer i = this.compute(scc.getAllStates());
					
			      Set<STATE> keyStates = new HashSet<STATE>(scc.getAllStates());
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
