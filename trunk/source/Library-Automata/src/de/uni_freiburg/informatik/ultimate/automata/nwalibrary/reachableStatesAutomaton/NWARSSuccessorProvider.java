package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.SccComputationWithAcceptingLassos.ISuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.StateBasedTransitionFilterPredicateProvider;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.FilteredIterable;
import de.uni_freiburg.informatik.ultimate.util.IteratorConcatenation;

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



	@Override
	public Iterator<StateContainer<LETTER, STATE>> getSuccessors(final StateContainer<LETTER, STATE> sc) {
		
		Iterator<StateContainer<LETTER,STATE>> internalTransitionsIterator = new Iterator<StateContainer<LETTER,STATE>>() {
			private final Iterator<OutgoingInternalTransition<LETTER, STATE>> m_OitIterator;
			{
				m_OitIterator = new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(
						sc.internalSuccessors(), m_TransitionFilter.getInternalSuccessorPredicate()).iterator();
			}

			@Override
			public boolean hasNext() {
				return m_OitIterator.hasNext();
			}

			@Override
			public StateContainer<LETTER, STATE> next() {
				return m_NestedWordAutomatonReachableStates.getStateContainer(m_OitIterator.next().getSucc());
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException("not modifiable");
			}
			
		};
		
		Iterator<StateContainer<LETTER,STATE>> returnSummaryTransitionsIterator = new Iterator<StateContainer<LETTER,STATE>>() {
			private final Iterator<SummaryReturnTransition<LETTER, STATE>> m_SrtIterator;
			{
				m_SrtIterator = new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(
						m_NestedWordAutomatonReachableStates.returnSummarySuccessor(sc.getState()), m_TransitionFilter.getReturnSummaryPredicate()).iterator();
			}

			@Override
			public boolean hasNext() {
				return m_SrtIterator.hasNext();
			}

			@Override
			public StateContainer<LETTER, STATE> next() {
				return m_NestedWordAutomatonReachableStates.getStateContainer(m_SrtIterator.next().getSucc());
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException("not modifiable");
			}
			
		};
		
		
		Iterator<StateContainer<LETTER,STATE>> callTransitionsIterator = new Iterator<StateContainer<LETTER,STATE>>() {
			private final Iterator<OutgoingCallTransition<LETTER, STATE>> m_OctIterator;

			{
				m_OctIterator = new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(
						sc.callSuccessors(), m_TransitionFilter.getCallSuccessorPredicate()).iterator();
			}

			@Override
			public boolean hasNext() {
				return m_OctIterator.hasNext();
			}

			@Override
			public StateContainer<LETTER, STATE> next() {
				return m_NestedWordAutomatonReachableStates.getStateContainer(m_OctIterator.next().getSucc());
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException("not modifiable");
			}
			
		};
		
		Iterator<StateContainer<LETTER,STATE>>[] iterators = (Iterator<StateContainer<LETTER, STATE>>[]) 
				new Iterator<?>[] { internalTransitionsIterator, returnSummaryTransitionsIterator, callTransitionsIterator };
		return new IteratorConcatenation<StateContainer<LETTER,STATE>>(Arrays.asList(iterators));
		
		
		
//		for (OutgoingInternalTransition<LETTER, STATE> trans : new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(
//				sc.internalSuccessors(), m_TransitionFilter.getInternalSuccessorPredicate())) {
//			StateContainer<LETTER, STATE> succCont = this.m_NestedWordAutomatonReachableStates.getStateContainer(trans.getSucc());
//			processSuccessor(v, succCont);
//		}
//		for (SummaryReturnTransition<LETTER, STATE> trans : new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(
//				this.m_NestedWordAutomatonReachableStates.returnSummarySuccessor(sc.getState()), m_TransitionFilter.getReturnSummaryPredicate())) {
//			StateContainer<LETTER, STATE> succCont = this.m_NestedWordAutomatonReachableStates.getStateContainer(trans.getSucc());
//			processSuccessor(v, succCont);
//		}
//		for (OutgoingCallTransition<LETTER, STATE> trans : new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(
//				sc.callSuccessors(), m_TransitionFilter.getCallSuccessorPredicate())) {
//			StateContainer<LETTER, STATE> succCont = this.m_NestedWordAutomatonReachableStates.getStateContainer(trans.getSucc());
//			processSuccessor(sc, succCont);
//		}
	}

}
