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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.StateBasedTransitionFilterPredicateProvider;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.FilteredIterable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.IteratorConcatenation;
import de.uni_freiburg.informatik.ultimate.util.relation.HashRelation;
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
	private final StateBasedTransitionFilterPredicateProvider<LETTER, STATE> mTransitionFilter;
	/**
	 * Use also other methods for lasso construction. This is only useful if you
	 * want to analyze if the lasso construction can be optimized.
	 */
	private final static boolean mUseAlternativeLassoConstruction = false;
	
	private final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> mAcceptingSummaries;

	private final Set<StateContainer<LETTER, STATE>> mAllStatesOfSccsWithoutCallAndReturn = new HashSet<StateContainer<LETTER, STATE>>();

	private List<NestedLassoRun<LETTER, STATE>> mNestedLassoRuns;
	private NestedLassoRun<LETTER, STATE> mNestedLassoRun;
	private SccComputation<StateContainer<LETTER, STATE>, StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE>> mSccComputation;
	
	private int mAcceptingBalls = 0;
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	private StronglyConnectedComponentWithAcceptanceInformation_Factory mScComponentFactory;
	private InSumCaSuccessorProvider mNWARSSuccessorProvider;
	Set<StateContainer<LETTER, STATE>> getStatesOfAllSCCs() {
		return mAllStatesOfSccsWithoutCallAndReturn;
	}

	public boolean buchiIsEmpty() {
		return mAcceptingBalls == 0;
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
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		this.nestedWordAutomatonReachableStates = nestedWordAutomatonReachableStates;
		mScComponentFactory = new StronglyConnectedComponentWithAcceptanceInformation_Factory(this.nestedWordAutomatonReachableStates);
		mNWARSSuccessorProvider = new InSumCaSuccessorProvider(nestedWordAutomatonReachableStates, allStates);
		Set<StateContainer<LETTER, STATE>> startNodes = new HashSet<StateContainer<LETTER, STATE>>();
		for (STATE state : startStates) {
			StateContainer<LETTER, STATE> sc = nestedWordAutomatonReachableStates.getStateContainer(state);
			startNodes.add(sc);
		}
		mSccComputation = new SccComputationNonRecursive<>(mLogger, mNWARSSuccessorProvider, mScComponentFactory, allStates.size(), startNodes);
		mTransitionFilter = new StateBasedTransitionFilterPredicateProvider<>(allStates);
		mAcceptingSummaries = asc.getAcceptingSummaries();


		
		for (StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE> scc : mSccComputation.getBalls()) {
			if (scc.isAccepting()) {
				mAllStatesOfSccsWithoutCallAndReturn.addAll(scc.getNodes());
				mAcceptingBalls++;
			}
		}

		mLogger.info("Automaton has " + mAcceptingBalls + " accepting balls. "
				+ mAllStatesOfSccsWithoutCallAndReturn.size());
	}

	public SccComputation<StateContainer<LETTER, STATE>, StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE>> getSccComputation() {
		return mSccComputation;
	}
	
	public List<NestedLassoRun<LETTER, STATE>> computeNestedLassoRuns(boolean onePerScc) throws AutomataOperationCanceledException {
		if (onePerScc) {
			throw new UnsupportedOperationException("not yet implemented");
		}
		List<NestedLassoRun<LETTER, STATE>> nestedLassoRuns = new ArrayList<NestedLassoRun<LETTER, STATE>>();
		for (StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE> scc : getSccComputation().getBalls()) {
			if (scc.isAccepting()) {
				for (StateContainer<LETTER, STATE> fin : scc.getAcceptingStatesContainers()) {
					NestedLassoRun<LETTER, STATE> nlr2 = (new LassoConstructor<LETTER, STATE>(mServices, 
							nestedWordAutomatonReachableStates, fin, scc)).getNestedLassoRun();
					if (mUseAlternativeLassoConstruction) {
						int nlr2Size = nlr2.getStem().getLength() + nlr2.getLoop().getLength();
						NestedLassoRun<LETTER, STATE> nlr = (new ShortestLassoExtractor<LETTER, STATE>(
								mServices, nestedWordAutomatonReachableStates, fin)).getNestedLassoRun();
						int nlrSize = nlr.getStem().getLength() + nlr.getLoop().getLength();
						NestedLassoRun<LETTER, STATE> nlr3 = (new LassoExtractor<LETTER, STATE>(mServices, 
								nestedWordAutomatonReachableStates, fin, scc, mAcceptingSummaries))
								.getNestedLassoRun();
						int nlr3Size = nlr3.getStem().getLength() + nlr3.getLoop().getLength();
					}
					nestedLassoRuns.add(nlr2);
				}
				for (StateContainer<LETTER, STATE> sumPred : scc.getAcceptingSummariesOfSCC().getDomain()) {
					Set<Summary<LETTER, STATE>> summaries = scc.getAcceptingSummariesOfSCC().getImage(sumPred);
					for (Summary<LETTER, STATE> summary : summaries) {
						NestedLassoRun<LETTER, STATE> nlr2 = (new LassoConstructor<LETTER, STATE>(mServices, 
								nestedWordAutomatonReachableStates, summary, scc)).getNestedLassoRun();
						if (mUseAlternativeLassoConstruction) {
							NestedLassoRun<LETTER, STATE> nlr = (new ShortestLassoExtractor<LETTER, STATE>(
									mServices, nestedWordAutomatonReachableStates, sumPred)).getNestedLassoRun();
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
		NestedLassoRun<LETTER, STATE> method4 = (new LassoConstructor<LETTER, STATE>(mServices, 
				nestedWordAutomatonReachableStates, lowestSerialNumber, sccOfLowest)).getNestedLassoRun();
		mLogger.debug("Method4: stem" + method4.getStem().getLength() + " loop" + method4.getLoop().getLength());
		if (mUseAlternativeLassoConstruction) {
			NestedLassoRun<LETTER, STATE> method0 = (new LassoExtractor<LETTER, STATE>(mServices, 
					nestedWordAutomatonReachableStates, sccOfLowest.getStateWithLowestSerialNumber(),
					sccOfLowest, mAcceptingSummaries)).getNestedLassoRun();
			mLogger.debug("Method0: stem" + method0.getStem().getLength() + " loop"
					+ method0.getLoop().getLength());
			NestedLassoRun<LETTER, STATE> method1 = (new LassoExtractor<LETTER, STATE>(mServices, 
					nestedWordAutomatonReachableStates, lowestSerialNumber, sccOfLowest, mAcceptingSummaries))
					.getNestedLassoRun();
			mLogger.debug("Method1: stem" + method1.getStem().getLength() + " loop"
					+ method1.getLoop().getLength());
			NestedLassoRun<LETTER, STATE> method2 = (new ShortestLassoExtractor<LETTER, STATE>(
					mServices, nestedWordAutomatonReachableStates, lowestSerialNumber)).getNestedLassoRun();
			mLogger.debug("Method2: stem" + method2.getStem().getLength() + " loop"
					+ method2.getLoop().getLength());
			int method0size = method0.getStem().getLength() + method0.getLoop().getLength();
			int method1size = method1.getStem().getLength() + method1.getLoop().getLength();
			int method2size = method2.getStem().getLength() + method1.getLoop().getLength();
			mLogger.debug("Method0size" + method0size + " Method1size" + method1size + " Method2size"
					+ method2size);
		}
		mNestedLassoRun = method4;
	}

	public List<NestedLassoRun<LETTER, STATE>> getAllNestedLassoRuns() throws AutomataOperationCanceledException {
		if (buchiIsEmpty()) {
			return Collections.emptyList();
		} else {
			if (mNestedLassoRuns == null) {
				mNestedLassoRuns = computeNestedLassoRuns(false);
			}
			return mNestedLassoRuns;
		}
	}

	public NestedLassoRun<LETTER, STATE> getNestedLassoRun() throws AutomataLibraryException {
		if (buchiIsEmpty()) {
			return null;
		} else {
			if (mNestedLassoRun == null) {
				computeShortNestedLassoRun();
			}
			return mNestedLassoRun;
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
		final Set<StateContainer<LETTER, STATE>> mAcceptingStates = new HashSet<StateContainer<LETTER, STATE>>();
		final NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates;
		/**
		 * States that have an outgoing summary. The summary successor may
		 * could be outside of this SCC. We determine the needed set only if
		 * construction of this SCC is finished.
		 */
		Set<StateContainer<LETTER, STATE>> mHasOutgoingAcceptingSum = new HashSet<StateContainer<LETTER, STATE>>();
		final HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> mAcceptingSummariesOfSCC = new HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>>();
		/**
		 * State of SCC with lowest serial number.
		 */
		private StateContainer<LETTER, STATE> mStateWithLowestSerialNumber;
		/**
		 * State of SCC with lowest serial number that is accepting or
		 * successor
		 */
		private StateContainer<LETTER, STATE> mAcceptingWithLowestSerialNumber;
		
		public StronglyConnectedComponentWithAcceptanceInformation(NestedWordAutomatonReachableStates<LETTER, STATE> nwars) {
			nestedWordAutomatonReachableStates = nwars;
		}

		@Override
		public void addNode(StateContainer<LETTER, STATE> cont) {
			super.addNode(cont);
			mStateWithLowestSerialNumber = StateContainer.returnLower(mStateWithLowestSerialNumber, cont);

			if (nestedWordAutomatonReachableStates.isFinal(cont.getState())) {
				mAcceptingStates.add(cont);
				mAcceptingWithLowestSerialNumber = StateContainer.returnLower(mAcceptingWithLowestSerialNumber,
						cont);
			}
			if (nestedWordAutomatonReachableStates.getAcceptingSummariesComputation().getAcceptingSummaries().getDomain().contains(cont)) {
				mHasOutgoingAcceptingSum.add(cont);
				// if we have to update lowest is determined later
			}
		}

		public void setRootNode(StateContainer<LETTER, STATE> rootNode) {
			if (mRootNode != null) {
				throw new UnsupportedOperationException("If root node is set SCC may not be modified");
			}
			this.mRootNode = rootNode;
			// TODO: Optimization: compute this only if there is no
			// accepting state in SCC
			for (StateContainer<LETTER, STATE> pred : mHasOutgoingAcceptingSum) {
				for (Summary<LETTER, STATE> summary : nestedWordAutomatonReachableStates.getAcceptingSummariesComputation().getAcceptingSummaries().getImage(pred)) {
					if (mNodes.contains(summary.getSucc())) {
						mAcceptingWithLowestSerialNumber = StateContainer.returnLower(
								mAcceptingWithLowestSerialNumber, pred);
						mAcceptingSummariesOfSCC.addPair(pred, summary);
					}
				}
			}
			mHasOutgoingAcceptingSum = null;
		}

		public Set<StateContainer<LETTER, STATE>> getAcceptingStatesContainers() {
			return mAcceptingStates;
		}
		
		public HashRelation<StateContainer<LETTER, STATE>, Summary<LETTER, STATE>> getAcceptingSummariesOfSCC() {
			return mAcceptingSummariesOfSCC;
		}

		public StateContainer<LETTER, STATE> getStateWithLowestSerialNumber() {
			return mStateWithLowestSerialNumber;
		}

		public boolean isAccepting() {
			return mAcceptingWithLowestSerialNumber != null;
		}

		/**
		 * Returns the state with the lowest serial number that is accepting
		 * or call predecessor of an accepting summary. Returns null if no
		 * such state exists.
		 * 
		 * @return
		 */
		public StateContainer<LETTER, STATE> getAcceptingWithLowestSerialNumber() {
			return mAcceptingWithLowestSerialNumber;
		}

		/**
		 * @return all states (not state containers) of this SCC.
		 * This methods is not efficient because a new Set is constructed.
		 * At the moment this is a workaround for Thomas' loop complexity
		 * project.
		 */
		public Set<STATE> getAllStates() {
			Set<STATE> result = new HashSet<>();
			for (StateContainer<LETTER, STATE> sc : mNodes) {
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

		private final NestedWordAutomatonReachableStates<LETTER, STATE> mNestedWordAutomatonReachableStates;

		public StronglyConnectedComponentWithAcceptanceInformation_Factory(
				NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates) {
			super();
			mNestedWordAutomatonReachableStates = nestedWordAutomatonReachableStates;
		}

		@Override
		public StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE> constructNewSCComponent() {
			return new StronglyConnectedComponentWithAcceptanceInformation<LETTER, STATE>(mNestedWordAutomatonReachableStates);
		}

	}
		
		
		
		
	/**
	 * Provides for a given StateContiner all StateContainers that are
	 * successors of internal transitions, summaries and call transitions.
	 * @author Matthias Heizmann
	 *
	 */
	private class InSumCaSuccessorProvider implements ISuccessorProvider<StateContainer<LETTER, STATE>> {

		private final NestedWordAutomatonReachableStates<LETTER, STATE> mNestedWordAutomatonReachableStates;
		private final StateBasedTransitionFilterPredicateProvider<LETTER, STATE> mTransitionFilter;



		public InSumCaSuccessorProvider(
				NestedWordAutomatonReachableStates<LETTER, STATE> nestedWordAutomatonReachableStates,
				Set<STATE> allStates) {
			super();
			mNestedWordAutomatonReachableStates = nestedWordAutomatonReachableStates;
			mTransitionFilter = new StateBasedTransitionFilterPredicateProvider<>(allStates);
		}


		private <E extends OutgoingTransitionlet<LETTER, STATE>> Iterator<StateContainer<LETTER, STATE>> getStateContainerIterator(final Iterator<E> it) {
			return new Iterator<StateContainer<LETTER,STATE>>() {

				@Override
				public boolean hasNext() {
					return it.hasNext();
				}

				@Override
				public StateContainer<LETTER, STATE> next() {
					return mNestedWordAutomatonReachableStates.getStateContainer(it.next().getSucc());
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
							sc.internalSuccessors(), mTransitionFilter.getInternalSuccessorPredicate()).iterator());

			Iterator<StateContainer<LETTER,STATE>> returnSummaryTransitionsIterator = 
					getStateContainerIterator(new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(
							mNestedWordAutomatonReachableStates.returnSummarySuccessor(sc.getState()), mTransitionFilter.getReturnSummaryPredicate()).iterator());


			Iterator<StateContainer<LETTER,STATE>> callTransitionsIterator = 
					getStateContainerIterator(new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(
							sc.callSuccessors(), mTransitionFilter.getCallSuccessorPredicate()).iterator());


			Iterator<StateContainer<LETTER,STATE>>[] iterators = (Iterator<StateContainer<LETTER, STATE>>[]) 
					new Iterator<?>[] { internalTransitionsIterator, returnSummaryTransitionsIterator, callTransitionsIterator };
			return new IteratorConcatenation<StateContainer<LETTER,STATE>>(Arrays.asList(iterators));
		}

	}
	
	
}
