/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.StateBasedTransitionFilterPredicateProvider;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.FilteredIterable;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.IteratorConcatenation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.IStronglyConnectedComponentFactory;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputationNonRecursive;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;


public class AcceptingComponentsAnalysis<LETTER, STATE> {
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
	private SccComputation<StateContainer<LETTER, STATE>, StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE>> m_SccComputation;
	
	private int m_AcceptingBalls = 0;
	private final AutomataLibraryServices m_Services;
	private final Logger m_Logger;
	private StronglyConnectedComponentWithAcceptanceInformation_Factory m_ScComponentFactory;
	private InSumCaSuccessorProvider m_NWARSSuccessorProvider;
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
	public AcceptingComponentsAnalysis(NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates, 
			NestedWordAutomatonReachableStates<LETTER, STATE>.AcceptingSummariesComputation asc, AutomataLibraryServices services,
			Set<STATE> allStates, Set<STATE> startStates) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		this.nestedWordAutomatonReachableStates = nestedWordAutomatonReachableStates;
		m_ScComponentFactory = new StronglyConnectedComponentWithAcceptanceInformation_Factory(this.nestedWordAutomatonReachableStates);
		m_NWARSSuccessorProvider = new InSumCaSuccessorProvider(nestedWordAutomatonReachableStates, allStates);
		Set<StateContainer<LETTER, STATE>> startNodes = new HashSet<StateContainer<LETTER, STATE>>();
		for (STATE state : startStates) {
			StateContainer<LETTER, STATE> sc = nestedWordAutomatonReachableStates.getStateContainer(state);
			startNodes.add(sc);
		}
		m_SccComputation = new SccComputationNonRecursive<>(m_Logger, m_NWARSSuccessorProvider, m_ScComponentFactory, allStates.size(), startNodes);
		m_TransitionFilter = new StateBasedTransitionFilterPredicateProvider<>(allStates);
		m_AcceptingSummaries = asc.getAcceptingSummaries();


		
		for (StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE> scc : m_SccComputation.getBalls()) {
			if (scc.isAccepting()) {
				m_AllStatesOfSccsWithoutCallAndReturn.addAll(scc.getNodes());
				m_AcceptingBalls++;
			}
		}

		m_Logger.info("Automaton has " + m_AcceptingBalls + " accepting balls. "
				+ m_AllStatesOfSccsWithoutCallAndReturn.size());
	}

	public SccComputation<StateContainer<LETTER, STATE>, StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE>> getSccComputation() {
		return m_SccComputation;
	}
	
	public List<NestedLassoRun<LETTER, STATE>> computeNestedLassoRuns(boolean onePerScc) throws OperationCanceledException {
		if (onePerScc) {
			throw new UnsupportedOperationException("not yet implemented");
		}
		List<NestedLassoRun<LETTER, STATE>> nestedLassoRuns = new ArrayList<NestedLassoRun<LETTER, STATE>>();
		for (StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE> scc : getSccComputation().getBalls()) {
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
					nestedLassoRuns.add(nlr2);
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
						nestedLassoRuns.add(nlr2);
					}
				}
			}
		}
		return nestedLassoRuns;
	}

	public void computeShortNestedLassoRun() throws AutomataLibraryException {
		StateContainer<LETTER, STATE> lowestSerialNumber = null;
		StateContainer<LETTER, STATE> newlowestSerialNumber = null;
		StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE> sccOfLowest = null;
		for (StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE> scc : getSccComputation().getBalls()) {
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
				m_NestedLassoRuns = computeNestedLassoRuns(false);
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
	
	
	
	
	
	
	
	
	
	
	/**
	 * Extension of {@link StronglyConnectedcomponent} that stores an maintains
	 * information which is needed by {@link NestedWordAutomatonReachableStates}
	 * to efficiently computed accepting runs.
	 * @author Matthias Heizmann
	 *
	 * @param <LETTER>
	 * @param <STATE>
	 */
	public static class StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE> extends StronglyConnectedComponent<StateContainer<LETTER, STATE>> {
		final Set<StateContainer<LETTER, STATE>> m_AcceptingStates = new HashSet<StateContainer<LETTER, STATE>>();
		final NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates;
		/**
		 * States that have an outgoing summary. The summary successor may
		 * could be outside of this SCC. We determine the needed set only if
		 * construction of this SCC is finished.
		 */
		Set<StateContainer<LETTER, STATE>> m_HasOutgoingAcceptingSum = new HashSet<StateContainer<LETTER, STATE>>();
		final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> m_AcceptingSummariesOfSCC = new HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>>();
		/**
		 * State of SCC with lowest serial number.
		 */
		private StateContainer<LETTER, STATE> m_StateWithLowestSerialNumber;
		/**
		 * State of SCC with lowest serial number that is accepting or
		 * successor
		 */
		private StateContainer<LETTER, STATE> m_AcceptingWithLowestSerialNumber;
		
		public StronglyConnectedComponentWithAcceptanceInformation(NestedWordAutomatonReachableStates<LETTER, STATE> nwars) {
			nestedWordAutomatonReachableStates = nwars;
		}

		@Override
		public void addNode(StateContainer<LETTER, STATE> cont) {
			super.addNode(cont);
			m_StateWithLowestSerialNumber = StateContainer.returnLower(m_StateWithLowestSerialNumber, cont);

			if (nestedWordAutomatonReachableStates.isFinal(cont.getState())) {
				m_AcceptingStates.add(cont);
				m_AcceptingWithLowestSerialNumber = StateContainer.returnLower(m_AcceptingWithLowestSerialNumber,
						cont);
			}
			if (nestedWordAutomatonReachableStates.getAcceptingSummariesComputation().getAcceptingSummaries().getDomain().contains(cont)) {
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
				for (Summary<LETTER, STATE> summary : nestedWordAutomatonReachableStates.getAcceptingSummariesComputation().getAcceptingSummaries().getImage(pred)) {
					if (m_Nodes.contains(summary.getSucc())) {
						m_AcceptingWithLowestSerialNumber = StateContainer.returnLower(
								m_AcceptingWithLowestSerialNumber, pred);
						m_AcceptingSummariesOfSCC.addPair(pred, summary);
					}
				}
			}
			m_HasOutgoingAcceptingSum = null;
		}

		public Set<StateContainer<LETTER, STATE>> getAcceptingStatesContainers() {
			return m_AcceptingStates;
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

		/**
		 * @return all states (not state containers) of this SCC.
		 * This methods is not efficient because a new Set is constructed.
		 * At the moment this is a workaround for Thomas' loop complexity
		 * project.
		 */
		public Set<STATE> getAllStates() {
			Set<STATE> result = new HashSet<>();
			for (StateContainer<LETTER, STATE> sc : m_Nodes) {
				result.add(sc.getState());
			}
			return result;
		}
	
	
	}
	
		
		
	/**
	 * Factory that constructs new {@link StronglyConnectedComponentWithAcceptanceInformation}.
	 * @author Matthias Heizmann
	 */
	private class StronglyConnectedComponentWithAcceptanceInformation_Factory implements IStronglyConnectedComponentFactory<StateContainer<LETTER, STATE>, StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE>> {

		private final NestedWordAutomatonReachableStates<LETTER, STATE> m_NestedWordAutomatonReachableStates;

		public StronglyConnectedComponentWithAcceptanceInformation_Factory(
				NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates) {
			super();
			m_NestedWordAutomatonReachableStates = nestedWordAutomatonReachableStates;
		}

		@Override
		public StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE> constructNewSCComponent() {
			return new StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE>(m_NestedWordAutomatonReachableStates);
		}

	}
		
		
		
		
	/**
	 * Provides for a given StateContiner all StateContainers that are
	 * successors of internal transitions, summaries and call transitions.
	 * @author Matthias Heizmann
	 *
	 */
	private class InSumCaSuccessorProvider implements ISuccessorProvider<StateContainer<LETTER, STATE>> {

		private final NestedWordAutomatonReachableStates<LETTER, STATE> m_NestedWordAutomatonReachableStates;
		private final StateBasedTransitionFilterPredicateProvider<LETTER, STATE> m_TransitionFilter;



		public InSumCaSuccessorProvider(
				NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates,
				Set<STATE> allStates) {
			super();
			m_NestedWordAutomatonReachableStates = nestedWordAutomatonReachableStates;
			m_TransitionFilter = new StateBasedTransitionFilterPredicateProvider<>(allStates);
		}


		private <E extends OutgoingTransitionlet<LETTER, STATE>> Iterator<StateContainer<LETTER, STATE>> getStateContainerIterator(final Iterator<E> it) {
			return new Iterator<StateContainer<LETTER,STATE>>() {

				@Override
				public boolean hasNext() {
					return it.hasNext();
				}

				@Override
				public StateContainer<LETTER, STATE> next() {
					return m_NestedWordAutomatonReachableStates.getStateContainer(it.next().getSucc());
				}

				@Override
				public void remove() {
					throw new UnsupportedOperationException("not modifiable");
				}

			};

		}

		@Override
		public Iterator<StateContainer<LETTER, STATE>> getSuccessors(final StateContainer<LETTER, STATE> sc) {

			Iterator<StateContainer<LETTER,STATE>> internalTransitionsIterator = 
					getStateContainerIterator(new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(
							sc.internalSuccessors(), m_TransitionFilter.getInternalSuccessorPredicate()).iterator());

			Iterator<StateContainer<LETTER,STATE>> returnSummaryTransitionsIterator = 
					getStateContainerIterator(new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(
							m_NestedWordAutomatonReachableStates.returnSummarySuccessor(sc.getState()), m_TransitionFilter.getReturnSummaryPredicate()).iterator());


			Iterator<StateContainer<LETTER,STATE>> callTransitionsIterator = 
					getStateContainerIterator(new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(
							sc.callSuccessors(), m_TransitionFilter.getCallSuccessorPredicate()).iterator());


			Iterator<StateContainer<LETTER,STATE>>[] iterators = (Iterator<StateContainer<LETTER, STATE>>[]) 
					new Iterator<?>[] { internalTransitionsIterator, returnSummaryTransitionsIterator, callTransitionsIterator };
			return new IteratorConcatenation<StateContainer<LETTER,STATE>>(Arrays.asList(iterators));
		}

	}
	
	
}
