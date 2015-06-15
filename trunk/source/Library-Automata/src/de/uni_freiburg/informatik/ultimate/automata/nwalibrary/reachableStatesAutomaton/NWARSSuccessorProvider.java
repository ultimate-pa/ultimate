package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.StateBasedTransitionFilterPredicateProvider;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.FilteredIterable;
import de.uni_freiburg.informatik.ultimate.util.IteratorConcatenation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;

public class NWARSSuccessorProvider<LETTER, STATE> implements ISuccessorProvider<StateContainer<LETTER, STATE>> {
	
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_NestedWordAutomatonReachableStates;
	private final StateBasedTransitionFilterPredicateProvider<LETTER, STATE> m_TransitionFilter;
	
	

	public NWARSSuccessorProvider(
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
