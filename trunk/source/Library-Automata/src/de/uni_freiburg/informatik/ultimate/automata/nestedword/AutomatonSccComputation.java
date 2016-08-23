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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.StateBasedTransitionFilterPredicateProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.FilteredIterable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.IteratorConcatenation;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultSccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Compute SCCs of an automaton. Allows to restrict computation to a subgraph
 * (subset of states with corresponding edges) of the automaton.
 * This computation should work for each {@link INestedWordAutomaton}, however, it is
 * only sound if each return transition is reachable (i.e., each summary
 * transition can actually be taken). To enforce soundness we restricted the
 * input to {@link NestedWordAutomatonReachableStates}. We might relax this in the
 * future.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class AutomatonSccComputation<LETTER, STATE> {
	
	// result
	private final DefaultSccComputation<STATE> mSccComputation;
	
	/**
	 * Computes SCCs of an automaton for a given subset of states.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param stateSubset
	 *            subset of the automaton's states
	 * @param startStates
	 *            states at which the computation of SSCs starts
	 */
	@SuppressWarnings("fb-contrib:OCP_OVERLY_CONCRETE_PARAMETER")
	public AutomatonSccComputation(
			final AutomataLibraryServices services,
			final NestedWordAutomatonReachableStates<LETTER, STATE> operand,
			final Set<STATE> stateSubset, final Set<STATE> startStates) {
		mSccComputation =
				new DefaultSccComputation<STATE>(services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID),
						new InSumCaSuccessorProvider(operand, stateSubset),
						stateSubset.size(), startStates);
	}
	
	/**
	 * Returns all balls of the computed SCC.
	 * 
	 * @return balls
	 */
	public Collection<StronglyConnectedComponent<STATE>> getBalls() {
		return mSccComputation.getBalls();
	}
	
	/**
	 * Provides - for a given state - all states that are
	 * <ul>
	 * <li>successors of internal transitions, summaries and call transitions,
	 * and
	 * <li>contained in a given set of states.
	 * </ul>
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class InSumCaSuccessorProvider implements ISuccessorProvider<STATE> {
		
		private final INestedWordAutomaton<LETTER, STATE> mOperand;
		private final StateBasedTransitionFilterPredicateProvider<LETTER, STATE> mTransitionFilter;
		
		public InSumCaSuccessorProvider(
				final INestedWordAutomaton<LETTER, STATE> nestedWordAutomatonReachableStates,
				final Set<STATE> stateSubset) {
			mOperand = nestedWordAutomatonReachableStates;
			mTransitionFilter = new StateBasedTransitionFilterPredicateProvider<>(stateSubset);
		}
		
		private <E extends IOutgoingTransitionlet<LETTER, STATE>> Iterator<STATE>
				getStateContainerIterator(final Iterator<E> iterator) {
			return new Iterator<STATE>() {
				
				@Override
				public boolean hasNext() {
					return iterator.hasNext();
				}
				
				@Override
				public STATE next() {
					return iterator.next().getSucc();
				}
			};
		}
		
		@Override
		public IteratorConcatenation<STATE> getSuccessors(final STATE state) {
			
			final Iterator<STATE> internalTransitionsIterator =
					getStateContainerIterator(
							new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(
									mOperand.internalSuccessors(state),
									mTransitionFilter.getInternalSuccessorPredicate()).iterator());
									
			final Iterator<STATE> returnSummaryTransitionsIterator =
					getStateContainerIterator(
							new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(
									mOperand.summarySuccessors(state),
									mTransitionFilter.getReturnSummaryPredicate()).iterator());
									
			final Iterator<STATE> callTransitionsIterator =
					getStateContainerIterator(
							new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(
									mOperand.callSuccessors(state),
									mTransitionFilter.getCallSuccessorPredicate()).iterator());
									
			final List<Iterator<STATE>> iteratorList = new ArrayList<>();
			iteratorList.add(internalTransitionsIterator);
			iteratorList.add(returnSummaryTransitionsIterator);
			iteratorList.add(callTransitionsIterator);
			
			return new IteratorConcatenation<STATE>(iteratorList);
		}
	}
}
