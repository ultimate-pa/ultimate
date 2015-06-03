package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
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
				m_AllStatesOfSccsWithoutCallAndReturn.addAll(scc.getAllStatesContainers());
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

		for (OutgoingInternalTransition<LETTER, STATE> trans : new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(
				v.internalSuccessors(), m_TransitionFilter.getInternalSuccessorPredicate())) {
			StateContainer<LETTER, STATE> succCont = this.nestedWordAutomatonReachableStates.getStateContainer(trans.getSucc());
			processSuccessor(v, succCont);
		}
		for (SummaryReturnTransition<LETTER, STATE> trans : new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(
				this.nestedWordAutomatonReachableStates.returnSummarySuccessor(v.getState()), m_TransitionFilter.getReturnSummaryPredicate())) {
			StateContainer<LETTER, STATE> succCont = this.nestedWordAutomatonReachableStates.getStateContainer(trans.getSucc());
			processSuccessor(v, succCont);
		}
		for (OutgoingCallTransition<LETTER, STATE> trans : new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(
				v.callSuccessors(), m_TransitionFilter.getCallSuccessorPredicate())) {
			StateContainer<LETTER, STATE> succCont = this.nestedWordAutomatonReachableStates.getStateContainer(trans.getSucc());
			processSuccessor(v, succCont);
		}

		if (m_LowLinks.get(v).equals(m_Indices.get(v))) {
			StateContainer<LETTER, STATE> w;
			SCComponentForNWARS<LETTER, STATE> scc = new SCComponentForNWARS<LETTER, STATE>(this.nestedWordAutomatonReachableStates);
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

	boolean isBall(SCComponent<LETTER, STATE> scc) {
		if (scc.getNumberOfStates() == 1) {
			StateContainer<LETTER, STATE> cont = ((SCComponentForNWARS<LETTER, STATE>) scc).getRootNode();
			for (OutgoingInternalTransition<LETTER, STATE> trans : new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(
					cont.internalSuccessors(), m_TransitionFilter.getInternalSuccessorPredicate())) {
				if (trans.getSucc().equals(cont.getState())) {
					return true;
				}
			}
			for (SummaryReturnTransition<LETTER, STATE> trans : new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(
					this.nestedWordAutomatonReachableStates.returnSummarySuccessor(cont.getState()), m_TransitionFilter.getReturnSummaryPredicate())) {
				if (trans.getSucc().equals(cont.getState())) {
					return true;
				}
			}
			for (OutgoingCallTransition<LETTER, STATE> trans : new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(
					cont.callSuccessors(), m_TransitionFilter.getCallSuccessorPredicate())) {
				StateContainer<LETTER, STATE> succCont = this.nestedWordAutomatonReachableStates.getStateContainer(trans.getSucc());
				if (trans.getSucc().equals(cont.getState())) {
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
		for (SCComponent<LETTER, STATE> scc : m_Balls) {
			statesInAllBalls += scc.getNumberOfStates();
			max = Math.max(max, scc.getNumberOfStates());
		}
		m_Logger.debug("The biggest SCC has " + max + " vertices.");
		boolean sameNumberOfVertices = (statesInAllBalls + m_NumberOfNonBallSCCs == m_NumberOfAllStates);
		return sameNumberOfVertices;
	}
}