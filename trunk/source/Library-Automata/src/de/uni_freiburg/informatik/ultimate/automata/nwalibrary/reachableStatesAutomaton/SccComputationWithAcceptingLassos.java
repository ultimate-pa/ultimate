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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.StateBasedTransitionFilterPredicateProvider;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.FilteredIterable;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;

/**
 * Offers a method to compute the strongly connected components (SCCs) of
 * the game graph. Implementation of Tarjan SCC algorithm. {@link http
 * ://en.wikipedia
 * .org/wiki/Tarjan%27s_strongly_connected_components_algorithm}
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class SccComputationWithAcceptingLassos<LETTER, STATE> {
	/**
	 * 
	 */
	private final NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates;
	private final StateBasedTransitionFilterPredicateProvider<LETTER, STATE> m_TransitionFilter;
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	/**
	 * Number of all states to which the SCC computation is applied.
	 */
	private final int m_NumberOfAllStates;
	/**
	 * Use also other methods for lasso construction. This is only useful if you
	 * want to analyze if the lasso construction can be optimized.
	 */
	private final static boolean m_UseAlternativeLassoConstruction = false;
	
	/**
	 * Number of vertices that have been processed so far.
	 */
	int m_Index = 0;
	/**
	 * Vertices that have not yet been assigned to any SCC.
	 */
	Stack<StateContainer<LETTER, STATE>> m_NoScc = new Stack<StateContainer<LETTER, STATE>>();

	/**
	 * Assigns to each vertex v the number of vertices that have been
	 * processed before in this algorithm. This number is called the index
	 * of v.
	 */
	Map<StateContainer<LETTER, STATE>, Integer> m_Indices = new HashMap<StateContainer<LETTER, STATE>, Integer>();

	Map<StateContainer<LETTER, STATE>, Integer> m_LowLinks = new HashMap<StateContainer<LETTER, STATE>, Integer>();

	final Collection<SCComponentForNWARS<LETTER, STATE>> m_Balls = new ArrayList<SCComponentForNWARS<LETTER, STATE>>();
	int m_NumberOfNonBallSCCs = 0;

	private final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> m_AcceptingSummaries;

	private final Set<StateContainer<LETTER, STATE>> m_AllStatesOfSccsWithoutCallAndReturn = new HashSet<StateContainer<LETTER, STATE>>();

	private List<NestedLassoRun<LETTER, STATE>> m_NestedLassoRuns;
	private NestedLassoRun<LETTER, STATE> m_NestedLassoRun;
	private int m_AcceptingBalls = 0;
	private final SCComponentForNWARSFactory<LETTER, STATE> m_ScComponentFactory;
	private final NWARSSuccessorProvider<LETTER, STATE> m_NWARSSuccessorProvider;

	public Collection<SCComponentForNWARS<LETTER, STATE>> getBalls() {
		return m_Balls;
	}

	Set<StateContainer<LETTER, STATE>> getStatesOfAllSCCs() {
		return m_AllStatesOfSccsWithoutCallAndReturn;
	}

	public boolean buchiIsEmpty() {
		return m_AcceptingBalls == 0;
	}

	/**
	 * 
	 * @param nestedWordAutomatonReachableStates
	 * @param asc
	 * @param services
	 * @param allStates states that are considered in this SCC computation
	 * @param startStates
	 */
	public SccComputationWithAcceptingLassos(NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates, 
			NestedWordAutomatonReachableStates<LETTER, STATE>.AcceptingSummariesComputation asc, IUltimateServiceProvider services,
			Set<STATE> allStates, Set<STATE> startStates) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		this.nestedWordAutomatonReachableStates = nestedWordAutomatonReachableStates;
		m_ScComponentFactory = new SCComponentForNWARSFactory<LETTER, STATE>(this.nestedWordAutomatonReachableStates);
		m_NWARSSuccessorProvider = new NWARSSuccessorProvider<>(nestedWordAutomatonReachableStates, allStates);
		m_TransitionFilter = new StateBasedTransitionFilterPredicateProvider<>(allStates);
		m_NumberOfAllStates = allStates.size();
		m_AcceptingSummaries = asc.getAcceptingSummaries();
		for (STATE state : startStates) {
			StateContainer<LETTER, STATE> cont = this.nestedWordAutomatonReachableStates.getStateContainer(state);
			if (!m_Indices.containsKey(cont)) {
				strongconnect(cont);
			}
		}

		assert (automatonPartitionedBySCCs());
		for (SCComponentForNWARS<LETTER, STATE> scc : m_Balls) {
			if (scc.isAccepting()) {
				m_AllStatesOfSccsWithoutCallAndReturn.addAll(scc.getNodes());
				m_AcceptingBalls++;
			}
		}

		m_Logger.debug("Automaton consists of " + m_Balls.size() + " InCaSumBalls and " + m_NumberOfNonBallSCCs
				+ " non ball SCCs " + m_AcceptingBalls + " balls are accepting. Number of states in SCCs "
				+ m_AllStatesOfSccsWithoutCallAndReturn.size());
	}

	private void strongconnect(StateContainer<LETTER, STATE> v) {
		assert (!m_Indices.containsKey(v));
		assert (!m_LowLinks.containsKey(v));
		m_Indices.put(v, m_Index);
		m_LowLinks.put(v, m_Index);
		m_Index++;
		this.m_NoScc.push(v);
		
		Iterator<StateContainer<LETTER, STATE>> it = m_NWARSSuccessorProvider.getSuccessors(v);
		while(it.hasNext()) {
			StateContainer<LETTER, STATE> succCont = it.next();
			processSuccessor(v, succCont);
		}

		if (m_LowLinks.get(v).equals(m_Indices.get(v))) {
			StateContainer<LETTER, STATE> w;
			SCComponentForNWARS<LETTER, STATE> scc = m_ScComponentFactory.constructNewSCComponent();
			do {
				w = m_NoScc.pop();
				scc.addState(w);
			} while (v != w);
			scc.setRootNode(w);
			if (isBall(scc)) {
				m_Balls.add(scc);
			} else {
				m_NumberOfNonBallSCCs++;
			}
		}
	}

	private void processSuccessor(StateContainer<LETTER, STATE> v, StateContainer<LETTER, STATE> w) {
		if (!m_Indices.containsKey(w)) {
			strongconnect(w);
			int minLowLink = Math.min(m_LowLinks.get(v), m_LowLinks.get(w));
			m_LowLinks.put(v, minLowLink);
		} else if (m_NoScc.contains(w)) {
			int min = Math.min(m_LowLinks.get(v), m_Indices.get(w));
			m_LowLinks.put(v, min);
		}
	}

	boolean isBall(SCComponent<StateContainer<LETTER, STATE>> scc) {
		if (scc.getNumberOfStates() == 1) {
			StateContainer<LETTER, STATE> cont = scc.getRootNode();
			Iterator<StateContainer<LETTER, STATE>> it = m_NWARSSuccessorProvider.getSuccessors(cont);
			while(it.hasNext()) {
				StateContainer<LETTER, STATE> succCont = it.next();
				if (cont.equals(succCont)) {
					return true;
				}
			}
			return false;
		} else {
			assert scc.getNumberOfStates() > 1;
			return true;
		}
	}

	/**
	 * @return true iff the SCCS form a partition of the automaton.
	 */
	private boolean automatonPartitionedBySCCs() {
		int statesInAllBalls = 0;
		int max = 0;
		for (SCComponent<StateContainer<LETTER, STATE>> scc : m_Balls) {
			statesInAllBalls += scc.getNumberOfStates();
			max = Math.max(max, scc.getNumberOfStates());
		}
		m_Logger.debug("The biggest SCC has " + max + " vertices.");
		boolean sameNumberOfVertices = (statesInAllBalls + m_NumberOfNonBallSCCs == m_NumberOfAllStates);
		return sameNumberOfVertices;
	}
	
	public interface SCComponentFactory<NODE, C extends SCComponent<NODE>> {
		public C constructNewSCComponent();
	}
	
	public interface ISuccessorProvider<NODE> {
		public Iterator<NODE> getSuccessors(NODE node);
	}
}