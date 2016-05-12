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

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.AutomatonSccComputation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Operation that computes the loop complexity of an automaton.
 * We define the loop complexity of an automaton as the loop complexity of
 * the underlying graph representation. This number is also called cycle rank.
 * https://en.wikipedia.org/wiki/Cycle_rank
 * 
 * @author Thomas Lang, Matthias Heizmann
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class LoopComplexity<LETTER, STATE> implements IOperation<LETTER, STATE> {	
	
	private final AutomataLibraryServices m_Services;
	private final ILogger m_Logger;
	
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Operand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Graph;
	private final Integer m_Result;
	
	private HashMap<Set<STATE>, Integer> statesToLC = new HashMap<Set<STATE>, Integer>();
	
	
	public LoopComplexity(AutomataLibraryServices services,
			INestedWordAutomaton<LETTER, STATE> operand) throws AutomataLibraryException {
		super();
		
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		
		if (operand instanceof NestedWordAutomatonReachableStates) {
			m_Operand = (NestedWordAutomatonReachableStates<LETTER, STATE>) operand;
		} else {
			m_Operand = (new RemoveUnreachable<LETTER, STATE>(m_Services, operand)).getResult();
		}
		
		m_Graph = constructGraph(m_Operand);
		
		m_Logger.info(this.startMessage());
		
		m_Result = computeLoopComplexityOfSubgraph(m_Graph.getStates());
		m_Logger.info(this.exitMessage());
	}

	/**
	 * Construct an automaton that represents the graph structure of
	 * the operand. The Result is a copy of the operand where each edge
	 * has the same label. As label we us some letter form the alphabet.
	 */
	private NestedWordAutomatonReachableStates<LETTER, STATE> constructGraph(
			INestedWordAutomaton<LETTER, STATE> automaton) throws OperationCanceledException {
		LETTER letter = automaton.getInternalAlphabet().iterator().next();
		Set<LETTER> singletonAlphabet = Collections.singleton(letter);
		NestedWordAutomaton<LETTER, STATE> graph = new NestedWordAutomaton<LETTER, STATE>(
				m_Services, singletonAlphabet, singletonAlphabet, singletonAlphabet, 
				automaton.getStateFactory());
				
		for (STATE q : automaton.getStates()) {
			graph.addState(true, true, q);
		}
		
		for (STATE q1 : automaton.getStates()) {
			for ( OutgoingInternalTransition<LETTER, STATE> outTrans : automaton.internalSuccessors(q1)) {
				STATE q2 = outTrans.getSucc();
				if (!graph.containsInternalTransition(q1, letter, q2)) {
					graph.addInternalTransition(q1, letter, q2);
				}
			}
		}
		return (new RemoveUnreachable<LETTER, STATE>(m_Services, graph)).getResult();
	}
	

	/**
	 * Compute the loop complexity of the subgraph that is obtained by
	 * projecting m_Graph to a subgraph. 
	 * @throws AutomataLibraryException
	 */
	private Integer computeLoopComplexityOfSubgraph(Set<STATE> statesOfSubgraph) 
			throws AutomataLibraryException {

		AutomatonSccComputation<LETTER, STATE> sccComputation = 
				new AutomatonSccComputation<LETTER, STATE>(m_Graph, m_Services, statesOfSubgraph, statesOfSubgraph);
		Collection<StronglyConnectedComponent<STATE>> balls = sccComputation.getBalls();

		// Graph contains no balls.
		if (balls.isEmpty()) {
			return 0;
		} else if (balls.size() == 1) { // Graph itself is a ball.
			// Consider all subgraphs differing from original graph by one vertex.


			Set<STATE> ballStates = balls.iterator().next().getNodes();

			Collection<STATE> nonchainStates = extractNonchainStates(ballStates);

			// If every state has one predecessor and one successor, the ball is a cycle.
			if (nonchainStates.isEmpty()) {
				return 1;
			}

			Collection<Integer> subGraphLoopComplexities = new ArrayList<Integer>();

			// Create a copy since 'nonchainStates' itself should not be modified.
			Set<STATE> copyStates = new HashSet<STATE>(statesOfSubgraph);

			for (STATE stateOut : nonchainStates) {
				// Check for cancel button.
				if (!m_Services.getProgressMonitorService().continueProcessing()) {
					throw new OperationCanceledException(this.getClass());
				}

				copyStates.remove(stateOut);

				if (statesToLC.containsKey(copyStates)) {
					subGraphLoopComplexities.add(statesToLC.get(copyStates));
				} else {
					Integer i = this.computeLoopComplexityOfSubgraph(copyStates);

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
					Integer i = this.computeLoopComplexityOfSubgraph(scc.getNodes());

					Set<STATE> keyStates = new HashSet<STATE>(scc.getNodes());
					statesToLC.put(keyStates, i);

					ballLoopComplexities.add(i);
				}
			}

			return Collections.max(ballLoopComplexities);
		}
	}

	
	/**
	 * Returns a new collection that contains only the non-chain states.
	 * We call a state a non-chain state if it has not exactly one predecessor
	 * or not exactly one successor. 
	 */
	private Collection<STATE> extractNonchainStates(Set<STATE> states) {
		Collection<STATE> peakStates = new ArrayList<STATE>();
		// Determine number of predecessors and successors for each state.
		for (STATE q : states) {
			int pCount = 0;
			int sCount = 0;

			Iterable<IncomingInternalTransition<LETTER, STATE>> preds = m_Graph.internalPredecessors(q);
			Iterable<OutgoingInternalTransition<LETTER, STATE>> succs = m_Graph.internalSuccessors(q);

			for (IncomingInternalTransition<LETTER, STATE> p : preds) {
				if (!states.contains(p.getPred())) {
					continue;
				}
				++pCount;
			}

			for (OutgoingInternalTransition<LETTER, STATE> s : succs) {
				if (!states.contains(s.getSucc())) {
					continue;
				}
				++sCount;
			}

			assert pCount > 0 : "must have at least one predecessor";
			assert sCount > 0 : "must have at least one successor";
			// Add all those states with the maximum number of edges to peakStates.
			if (pCount != 1 || sCount != 1) {
				peakStates.add(q);
			}
		}
		return peakStates;
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
		return "Finished " + operationName() + ". Operand with " + 
				m_Operand.getStates().size() + " states hast loop complexity " 
				+ m_Result;
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
