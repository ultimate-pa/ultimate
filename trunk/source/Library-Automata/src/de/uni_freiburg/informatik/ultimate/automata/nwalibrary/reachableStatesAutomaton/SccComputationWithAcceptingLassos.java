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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates.AcceptingSummariesComputation;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
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

	final Collection<SCC> m_Balls = new ArrayList<SCC>();
	int m_NumberOfNonBallSCCs = 0;

	private final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> m_AcceptingSummaries;

	private final Set<StateContainer<LETTER, STATE>> m_AllStatesOfSccsWithoutCallAndReturn = new HashSet<StateContainer<LETTER, STATE>>();

	private List<NestedLassoRun<LETTER, STATE>> m_NestedLassoRuns;
	private NestedLassoRun<LETTER, STATE> m_NestedLassoRun;
	private int m_AcceptingBalls = 0;

	public Collection<SCC> getBalls() {
		return m_Balls;
	}

	Set<StateContainer<LETTER, STATE>> getStatesOfAllSCCs() {
		return m_AllStatesOfSccsWithoutCallAndReturn;
	}

	public boolean buchiIsEmpty() {
		return m_AcceptingBalls == 0;
	}

	public SccComputationWithAcceptingLassos(NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates, AcceptingSummariesComputation asc, IUltimateServiceProvider services) {
		this.nestedWordAutomatonReachableStates = nestedWordAutomatonReachableStates;
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_NumberOfAllStates = this.nestedWordAutomatonReachableStates.size();
		m_AcceptingSummaries = asc.getAcceptingSummaries();
		for (STATE state : this.nestedWordAutomatonReachableStates.getInitialStates()) {
			StateContainer<LETTER, STATE> cont = this.nestedWordAutomatonReachableStates.getStateContainer(state);
			if (!m_Indices.containsKey(cont)) {
				strongconnect(cont);
			}
		}

		assert (automatonPartitionedBySCCs());
		for (SCC scc : m_Balls) {
			if (scc.isAccepting()) {
				m_AllStatesOfSccsWithoutCallAndReturn.addAll(scc.getAllStatesContainers());
				m_AcceptingBalls++;
			}
		}

		m_Logger.debug("Automaton consists of " + m_Balls.size() + " InCaSumBalls and " + m_NumberOfNonBallSCCs
				+ " non ball SCCs " + m_AcceptingBalls + " balls are accepting. Number of states in SCCs "
				+ m_AllStatesOfSccsWithoutCallAndReturn.size());
	}

	public void computeNestedLassoRuns(boolean onePerScc) throws OperationCanceledException {
		if (onePerScc) {
			throw new UnsupportedOperationException("not yet implemented");
		}
		assert m_NestedLassoRuns == null : "already computed";
		m_NestedLassoRuns = new ArrayList<NestedLassoRun<LETTER, STATE>>();
		for (SccComputationWithAcceptingLassos<LETTER, STATE>.SCC scc : m_Balls) {
			if (scc.isAccepting()) {
				for (StateContainer<LETTER, STATE> fin : scc.getAcceptingStatesContainers()) {
					NestedLassoRun<LETTER, STATE> nlr2 = (new LassoConstructor<LETTER, STATE>(m_Services, 
							nestedWordAutomatonReachableStates, fin, scc)).getNestedLassoRun();
					if (m_UseAlternativeLassoConstruction) {
						int nlr2Size = nlr2.getStem().getLength() + nlr2.getLoop().getLength();
						NestedLassoRun<LETTER, STATE> nlr = (new ShortestLassoExtractor<LETTER, STATE>(
								m_Services, nestedWordAutomatonReachableStates, fin)).getNestedLassoRun();
						int nlrSize = nlr.getStem().getLength() + nlr.getLoop().getLength();
						NestedLassoRun<LETTER, STATE> nlr3 = (new LassoExtractor<LETTER, STATE>(m_Services, 
								nestedWordAutomatonReachableStates, fin, scc, m_AcceptingSummaries))
								.getNestedLassoRun();
						int nlr3Size = nlr3.getStem().getLength() + nlr3.getLoop().getLength();
					}
					m_NestedLassoRuns.add(nlr2);
				}
				for (StateContainer<LETTER, STATE> sumPred : scc.getAcceptingSummariesOfSCC().getDomain()) {
					Set<Summary<LETTER, STATE>> summaries = scc.getAcceptingSummariesOfSCC().getImage(sumPred);
					for (Summary<LETTER, STATE> summary : summaries) {
						NestedLassoRun<LETTER, STATE> nlr2 = (new LassoConstructor<LETTER, STATE>(m_Services, 
								nestedWordAutomatonReachableStates, summary, scc)).getNestedLassoRun();
						if (m_UseAlternativeLassoConstruction) {
							NestedLassoRun<LETTER, STATE> nlr = (new ShortestLassoExtractor<LETTER, STATE>(
									m_Services, nestedWordAutomatonReachableStates, sumPred)).getNestedLassoRun();
							int nlrSize = nlr.getStem().getLength() + nlr.getLoop().getLength();
							int nlr2Size = nlr2.getStem().getLength() + nlr2.getLoop().getLength();
						}
						m_NestedLassoRuns.add(nlr2);
					}
				}
			}
		}
	}

	public void computeShortNestedLassoRun() throws AutomataLibraryException {
		StateContainer<LETTER, STATE> lowestSerialNumber = null;
		StateContainer<LETTER, STATE> newlowestSerialNumber = null;
		SCC sccOfLowest = null;
		for (SCC scc : m_Balls) {
			if (scc.isAccepting()) {
				StateContainer<LETTER, STATE> lowestOfScc = scc.getAcceptingWithLowestSerialNumber();
				newlowestSerialNumber = StateContainer.returnLower(lowestSerialNumber, lowestOfScc);
				if (newlowestSerialNumber != lowestSerialNumber) {
					lowestSerialNumber = newlowestSerialNumber;
					sccOfLowest = scc;
				}
			}
		}
		NestedLassoRun<LETTER, STATE> method4 = (new LassoConstructor<LETTER, STATE>(m_Services, 
				nestedWordAutomatonReachableStates, lowestSerialNumber, sccOfLowest)).getNestedLassoRun();
		m_Logger.debug("Method4: stem" + method4.getStem().getLength() + " loop" + method4.getLoop().getLength());
		if (m_UseAlternativeLassoConstruction) {
			NestedLassoRun<LETTER, STATE> method0 = (new LassoExtractor<LETTER, STATE>(m_Services, 
					nestedWordAutomatonReachableStates, sccOfLowest.getStateWithLowestSerialNumber(),
					sccOfLowest, m_AcceptingSummaries)).getNestedLassoRun();
			m_Logger.debug("Method0: stem" + method0.getStem().getLength() + " loop"
					+ method0.getLoop().getLength());
			NestedLassoRun<LETTER, STATE> method1 = (new LassoExtractor<LETTER, STATE>(m_Services, 
					nestedWordAutomatonReachableStates, lowestSerialNumber, sccOfLowest, m_AcceptingSummaries))
					.getNestedLassoRun();
			m_Logger.debug("Method1: stem" + method1.getStem().getLength() + " loop"
					+ method1.getLoop().getLength());
			NestedLassoRun<LETTER, STATE> method2 = (new ShortestLassoExtractor<LETTER, STATE>(
					m_Services, nestedWordAutomatonReachableStates, lowestSerialNumber)).getNestedLassoRun();
			m_Logger.debug("Method2: stem" + method2.getStem().getLength() + " loop"
					+ method2.getLoop().getLength());
			int method0size = method0.getStem().getLength() + method0.getLoop().getLength();
			int method1size = method1.getStem().getLength() + method1.getLoop().getLength();
			int method2size = method2.getStem().getLength() + method1.getLoop().getLength();
			m_Logger.debug("Method0size" + method0size + " Method1size" + method1size + " Method2size"
					+ method2size);
		}
		m_NestedLassoRun = method4;
	}

	public List<NestedLassoRun<LETTER, STATE>> getAllNestedLassoRuns() throws OperationCanceledException {
		if (buchiIsEmpty()) {
			return Collections.emptyList();
		} else {
			if (m_NestedLassoRuns == null) {
				computeNestedLassoRuns(false);
			}
			return m_NestedLassoRuns;
		}
	}

	public NestedLassoRun<LETTER, STATE> getNestedLassoRun() throws AutomataLibraryException {
		if (buchiIsEmpty()) {
			return null;
		} else {
			if (m_NestedLassoRun == null) {
				computeShortNestedLassoRun();
			}
			return m_NestedLassoRun;
		}
	}

	private void strongconnect(StateContainer<LETTER, STATE> v) {
		assert (!m_Indices.containsKey(v));
		assert (!m_LowLinks.containsKey(v));
		m_Indices.put(v, m_Index);
		m_LowLinks.put(v, m_Index);
		m_Index++;
		this.m_NoScc.push(v);

		for (OutgoingInternalTransition<LETTER, STATE> trans : v.internalSuccessors()) {
			StateContainer<LETTER, STATE> succCont = this.nestedWordAutomatonReachableStates.getStateContainer(trans.getSucc());
			processSuccessor(v, succCont);
		}
		for (SummaryReturnTransition<LETTER, STATE> trans : this.nestedWordAutomatonReachableStates.returnSummarySuccessor(v.getState())) {
			StateContainer<LETTER, STATE> succCont = this.nestedWordAutomatonReachableStates.getStateContainer(trans.getSucc());
			processSuccessor(v, succCont);
		}
		for (OutgoingCallTransition<LETTER, STATE> trans : v.callSuccessors()) {
			StateContainer<LETTER, STATE> succCont = this.nestedWordAutomatonReachableStates.getStateContainer(trans.getSucc());
			processSuccessor(v, succCont);
		}

		if (m_LowLinks.get(v).equals(m_Indices.get(v))) {
			StateContainer<LETTER, STATE> w;
			SCC scc = new SCC();
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

	boolean isBall(SCC scc) {
		if (scc.getNumberOfStates() == 1) {
			StateContainer<LETTER, STATE> cont = scc.getRootNode();
			for (OutgoingInternalTransition<LETTER, STATE> trans : cont.internalSuccessors()) {
				if (trans.getSucc().equals(cont.getState())) {
					return true;
				}
			}
			for (SummaryReturnTransition<LETTER, STATE> trans : this.nestedWordAutomatonReachableStates.returnSummarySuccessor(cont.getState())) {
				if (trans.getSucc().equals(cont.getState())) {
					return true;
				}
			}
			for (OutgoingCallTransition<LETTER, STATE> trans : cont.callSuccessors()) {
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
		for (SCC scc : m_Balls) {
			statesInAllBalls += scc.getNumberOfStates();
			max = Math.max(max, scc.getNumberOfStates());
		}
		m_Logger.debug("The biggest SCC has " + max + " vertices.");
		boolean sameNumberOfVertices = (statesInAllBalls + m_NumberOfNonBallSCCs == m_NumberOfAllStates);
		return sameNumberOfVertices;
	}

	public class SCC {
		StateContainer<LETTER, STATE> m_RootNode;
		final Set<StateContainer<LETTER, STATE>> m_AcceptingStates = new HashSet<StateContainer<LETTER, STATE>>();
		/**
		 * States that have an outgoing summary. The summary successor may
		 * could be outside of this SCC. We determine the needed set only if
		 * construction of this SCC is finished.
		 */
		Set<StateContainer<LETTER, STATE>> m_HasOutgoingAcceptingSum = new HashSet<StateContainer<LETTER, STATE>>();
		final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> m_AcceptingSummariesOfSCC = new HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>>();
		final Set<StateContainer<LETTER, STATE>> m_AllStates = new HashSet<StateContainer<LETTER, STATE>>();
		/**
		 * State of SCC with lowest serial number.
		 */
		private StateContainer<LETTER, STATE> m_StateWithLowestSerialNumber;
		/**
		 * State of SCC with lowest serial number that is accepting or
		 * successor
		 */
		private StateContainer<LETTER, STATE> m_AcceptingWithLowestSerialNumber;

		public void addState(StateContainer<LETTER, STATE> cont) {
			if (m_RootNode != null) {
				throw new UnsupportedOperationException("If root node is set SCC may not be modified");
			}
			m_AllStates.add(cont);
			m_StateWithLowestSerialNumber = StateContainer.returnLower(m_StateWithLowestSerialNumber, cont);

			if (SccComputationWithAcceptingLassos.this.nestedWordAutomatonReachableStates.isFinal(cont.getState())) {
				m_AcceptingStates.add(cont);
				m_AcceptingWithLowestSerialNumber = StateContainer.returnLower(m_AcceptingWithLowestSerialNumber,
						cont);
			}
			if (m_AcceptingSummaries.getDomain().contains(cont)) {
				m_HasOutgoingAcceptingSum.add(cont);
				// if we have to update lowest is determined later
			}
		}

		public void setRootNode(StateContainer<LETTER, STATE> rootNode) {
			if (m_RootNode != null) {
				throw new UnsupportedOperationException("If root node is set SCC may not be modified");
			}
			this.m_RootNode = rootNode;
			// TODO: Optimization: compute this only if there is no
			// accepting state in SCC
			for (StateContainer<LETTER, STATE> pred : m_HasOutgoingAcceptingSum) {
				for (Summary<LETTER, STATE> summary : m_AcceptingSummaries.getImage(pred)) {
					if (m_AllStates.contains(summary.getSucc())) {
						m_AcceptingWithLowestSerialNumber = StateContainer.returnLower(
								m_AcceptingWithLowestSerialNumber, pred);
						m_AcceptingSummariesOfSCC.addPair(pred, summary);
					}
				}
			}
			m_HasOutgoingAcceptingSum = null;
		}

		public int getNumberOfStates() {
			return m_AllStates.size();
		}

		public StateContainer<LETTER, STATE> getRootNode() {
			return m_RootNode;
		}

		/**
		 * @return The {@link StateContainer}s of all states that are 
		 * contained in this SCC.
		 */
		public Set<StateContainer<LETTER, STATE>> getAllStatesContainers() {
			return m_AllStates;
		}

		public Set<StateContainer<LETTER, STATE>> getAcceptingStatesContainers() {
			return m_AcceptingStates;
		}
		
		/**
		 * @return all states (not state containers) of this SCC.
		 * This methods is not efficient because a new Set is constructed.
		 * At the moment this is a workaround for Thomas' loop complexity
		 * project.
		 */
		public Set<STATE> getAllStates() {
			Set<STATE> result = new HashSet<>();
			for (StateContainer<LETTER, STATE> sc : m_AllStates) {
				result.add(sc.getState());
			}
			return result;
		}

		public HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> getAcceptingSummariesOfSCC() {
			return m_AcceptingSummariesOfSCC;
		}

		public StateContainer<LETTER, STATE> getStateWithLowestSerialNumber() {
			return m_StateWithLowestSerialNumber;
		}

		public boolean isAccepting() {
			return m_AcceptingWithLowestSerialNumber != null;
		}

		/**
		 * Returns the state with the lowest serial number that is accepting
		 * or call predecessor of an accepting summary. Returns null if no
		 * such state exists.
		 * 
		 * @return
		 */
		public StateContainer<LETTER, STATE> getAcceptingWithLowestSerialNumber() {
			return m_AcceptingWithLowestSerialNumber;
		}
	}
}