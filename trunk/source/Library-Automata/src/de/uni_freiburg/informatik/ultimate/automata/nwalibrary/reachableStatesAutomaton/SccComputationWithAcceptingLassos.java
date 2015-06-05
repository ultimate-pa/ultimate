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

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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


public class SccComputationWithAcceptingLassos<LETTER, STATE> {
	/**
	 * 
	 */
	private final NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates;
	private final StateBasedTransitionFilterPredicateProvider<LETTER, STATE> m_TransitionFilter;
	/**
	 * Use also other methods for lasso construction. This is only useful if you
	 * want to analyze if the lasso construction can be optimized.
	 */
	private final static boolean m_UseAlternativeLassoConstruction = false;
	
	private final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> m_AcceptingSummaries;

	private final Set<StateContainer<LETTER, STATE>> m_AllStatesOfSccsWithoutCallAndReturn = new HashSet<StateContainer<LETTER, STATE>>();

	private List<NestedLassoRun<LETTER, STATE>> m_NestedLassoRuns;
	private NestedLassoRun<LETTER, STATE> m_NestedLassoRun;
	private SccComputation<StateContainer<LETTER, STATE>, SCComponentForNWARS<LETTER, STATE>> m_sccComputation;
	
	private int m_AcceptingBalls = 0;
	private IUltimateServiceProvider m_Services;
	private Logger m_Logger;
	private SCComponentForNWARSFactory<LETTER, STATE> m_ScComponentFactory;
	private NWARSSuccessorProvider<LETTER, STATE> m_NWARSSuccessorProvider;
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
		Set<StateContainer<LETTER, STATE>> startNodes = new HashSet<StateContainer<LETTER, STATE>>();
		for (STATE state : startStates) {
			StateContainer<LETTER, STATE> sc = nestedWordAutomatonReachableStates.getStateContainer(state);
			startNodes.add(sc);
		}
		m_sccComputation = new SccComputation(m_Services, m_Logger, m_NWARSSuccessorProvider, m_ScComponentFactory, allStates.size(), startNodes);
		m_TransitionFilter = new StateBasedTransitionFilterPredicateProvider<>(allStates);
		m_AcceptingSummaries = asc.getAcceptingSummaries();


		
		for (SCComponentForNWARS<LETTER, STATE> scc : m_sccComputation.getBalls()) {
			if (scc.isAccepting()) {
				m_AllStatesOfSccsWithoutCallAndReturn.addAll(scc.getNodes());
				m_AcceptingBalls++;
			}
		}

		m_Logger.info("Automaton has " + m_AcceptingBalls + " accepting balls. "
				+ m_AllStatesOfSccsWithoutCallAndReturn.size());
	}

	public SccComputation<StateContainer<LETTER, STATE>, SCComponentForNWARS<LETTER, STATE>> getSccComputation() {
		return m_sccComputation;
	}
	
}