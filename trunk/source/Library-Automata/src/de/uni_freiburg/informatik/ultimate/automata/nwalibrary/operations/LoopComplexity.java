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
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates.StronglyConnectedComponents.SCC;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

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
	
	private final INestedWordAutomaton<LETTER, STATE> m_Operand;
	private final Integer m_Result;
	
	

	public LoopComplexity(IUltimateServiceProvider services,
			INestedWordAutomaton<LETTER, STATE> operand) throws AutomataLibraryException {
		super();
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_Operand = operand;
		m_Logger.info(this.startMessage());
		
		m_Result = compute(operand);
		m_Logger.info(this.exitMessage());
	}

	private Integer compute(INestedWordAutomaton<LETTER, STATE> operand) throws AutomataLibraryException {
		NestedWordAutomatonReachableStates<LETTER, STATE> nwars = 
				new NestedWordAutomatonReachableStates<>(m_Services, operand);
		NestedWordAutomatonReachableStates<LETTER, STATE>.StronglyConnectedComponents sccs = 
				nwars.getOrComputeStronglyConnectedComponents();
		Collection<NestedWordAutomatonReachableStates<LETTER, STATE>.StronglyConnectedComponents.SCC> balls = sccs.getBalls();
		for (SCC scc : balls) {
			scc.getAllStatesContainers();
		}
		// Graph contains no balls.
		if (balls.isEmpty()) {
			return 0;
		} else if (balls.size() == 1) { // Graph itself is a ball.
			// Build all subgraphs differing from original graph by one vertex.
			Collection<Integer> subGraphLoopComplexities = new ArrayList<Integer>();
			Collection<STATE> allstates = operand.getStates();
			for (STATE stateOut : allstates) {
				NestedWordAutomaton<LETTER, STATE> nwa = buildSubgraph(operand,
						stateOut);
				
				subGraphLoopComplexities.add(this.compute(nwa));
			}
			return 1 + Collections.min(subGraphLoopComplexities);
		} else { // Graph itself is not a ball.
			Collection<Integer> ballLoopComplexities = new ArrayList<Integer>();
			// Build NestedWordAutomaton for each ball and compute Loop Complexity.
			for (SCC scc : balls) {
				NestedWordAutomaton<LETTER, STATE> nwa = sccToAutomaton(
						operand, scc);
				ballLoopComplexities.add(this.compute(nwa));
			}
			return Collections.max(ballLoopComplexities);
		}
	}

	private NestedWordAutomaton<LETTER, STATE> buildSubgraph(
			INestedWordAutomaton<LETTER, STATE> operand, STATE stateOut) {
		NestedWordAutomaton<LETTER, STATE> nwa = new NestedWordAutomaton<LETTER, STATE>(m_Services, operand.getInternalAlphabet(), operand.getCallAlphabet(), operand.getReturnAlphabet(), operand.getStateFactory());
		// States to be included in new graph.
		Collection<STATE> allowedStates = operand.getStates();
		allowedStates.remove(stateOut);
		
		for (STATE state : allowedStates) {
			nwa.addState(true, true, state);
		}
		
		for (STATE state : allowedStates) {
			Iterable<OutgoingInternalTransition<LETTER, STATE>> succs = operand.internalSuccessors(state);
		    for (OutgoingInternalTransition<LETTER, STATE> outtrans : succs) {
		    	if (allowedStates.contains(outtrans.getSucc())) {
		    		nwa.addInternalTransition(state, outtrans.getLetter(), outtrans.getSucc());
		    	}
		    }
		}
		return nwa;
	}

	private NestedWordAutomaton<LETTER, STATE> sccToAutomaton(
			INestedWordAutomaton<LETTER, STATE> operand, SCC scc) {
		NestedWordAutomaton<LETTER, STATE> nwa = new NestedWordAutomaton<LETTER, STATE>(m_Services, operand.getInternalAlphabet(), operand.getCallAlphabet(), operand.getReturnAlphabet(), operand.getStateFactory());
		Set<STATE> allstates = scc.getAllStates();
		for (STATE state : allstates) {					
			nwa.addState(true, true, state);
		}
		for (STATE state : allstates) {
			Iterable<OutgoingInternalTransition<LETTER, STATE>> succs = operand.internalSuccessors(state);
		    for (OutgoingInternalTransition<LETTER, STATE> outtrans : succs) {
		    	if (allstates.contains(outtrans.getSucc())) {
		    		nwa.addInternalTransition(state, outtrans.getLetter(), outtrans.getSucc());
		    	}
		    }
		}
		return nwa;
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
