package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;

public class DeletedStatesAutomaton<LETTER, STATE> implements
		INestedWordAutomaton<LETTER, STATE> {
	INestedWordAutomaton<LETTER, STATE> m_Automaton;
	Set<STATE> m_States;
	
	DeletedStatesAutomaton(INestedWordAutomaton<LETTER, STATE> automaton, Set<STATE> states) {
		m_Automaton = automaton;
		m_States = states;
	}

	@Override
	public IRun<LETTER, STATE> acceptingRun() throws OperationCanceledException {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean accepts(Word<LETTER> word) {
		throw new UnsupportedOperationException();
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public Collection<LETTER> getAlphabet() {
		return m_Automaton.getAlphabet();
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> getInternalAlphabet() {
		return m_Automaton.getInternalAlphabet();
	}

	@Override
	public Collection<LETTER> getCallAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> getReturnAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> getStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> getInitialStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<STATE> getFinalStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isInitial(STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFinal(STATE state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void addState(boolean isInitial, boolean isFinal, STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void removeState(STATE state) {
		throw new UnsupportedOperationException();
	}

	@Override
	public STATE getEmptyStackState() {
		return m_Automaton.getEmptyStackState();
	}

	@Override
	public Collection<LETTER> lettersInternal(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersCall(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersReturn(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersInternalIncoming(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersCallIncoming(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersReturnIncoming(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> lettersReturnSummary(STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<STATE> succInternal(final STATE state, final LETTER letter) {
		return new FilteredIterable<STATE>(m_Automaton.succInternal(state, letter), m_States);
	}

	@Override
	public Iterable<STATE> succCall(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Automaton.succCall(state, letter), m_States);
	}

	@Override
	public Iterable<STATE> hierPred(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Automaton.succCall(state, letter), m_States);
	}

	@Override
	public Iterable<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		return new FilteredIterable<STATE>(m_Automaton.succCall(state, letter), m_States);
	}

	@Override
	public Iterable<STATE> predInternal(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Automaton.succCall(state, letter), m_States);
	}

	@Override
	public Iterable<STATE> predCall(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Automaton.succCall(state, letter), m_States);
	}

	@Override
	public Iterable<STATE> predReturnLin(STATE state, LETTER letter, STATE hier) {
		return new FilteredIterable<STATE>(m_Automaton.succCall(state, letter), m_States);
	}

	@Override
	public Iterable<STATE> predReturnHier(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Automaton.succCall(state, letter), m_States);
	}

	@Override
	public void addInternalTransition(STATE pred, LETTER letter, STATE succ) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void addCallTransition(STATE pred, LETTER letter, STATE succ) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void addReturnTransition(STATE pred, STATE hier, LETTER letter,
			STATE succ) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean finalIsTrap() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isDeterministic() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isTotal() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> getSummaryReturnTransitions(
			LETTER letter, STATE hier) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> getIncomingReturnTransitions(
			LETTER letter, STATE succ) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			LETTER letter, STATE succ) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			STATE succ) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			LETTER letter, STATE succ) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			STATE succ) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		Set<OutgoingInternalTransition<LETTER, STATE>> filter = new Set<OutgoingInternalTransition<LETTER,STATE>>() {

			@Override
			public boolean add(OutgoingInternalTransition<LETTER, STATE> e) {
				// TODO Auto-generated method stub
				return false;
			}

			@Override
			public boolean addAll(
					Collection<? extends OutgoingInternalTransition<LETTER, STATE>> c) {
				// TODO Auto-generated method stub
				return false;
			}

			@Override
			public void clear() {
				// TODO Auto-generated method stub
				
			}

			@Override
			public boolean contains(Object o) {
				// TODO Auto-generated method stub
				return false;
			}

			@Override
			public boolean containsAll(Collection<?> c) {
				// TODO Auto-generated method stub
				return false;
			}

			@Override
			public boolean isEmpty() {
				// TODO Auto-generated method stub
				return false;
			}

			@Override
			public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
				// TODO Auto-generated method stub
				return null;
			}

			@Override
			public boolean remove(Object o) {
				// TODO Auto-generated method stub
				return false;
			}

			@Override
			public boolean removeAll(Collection<?> c) {
				// TODO Auto-generated method stub
				return false;
			}

			@Override
			public boolean retainAll(Collection<?> c) {
				// TODO Auto-generated method stub
				return false;
			}

			@Override
			public int size() {
				// TODO Auto-generated method stub
				return 0;
			}

			@Override
			public Object[] toArray() {
				// TODO Auto-generated method stub
				return null;
			}

			@Override
			public <T> T[] toArray(T[] a) {
				// TODO Auto-generated method stub
				return null;
			}
			
		};
		return new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(m_Automaton.internalSuccessors(state), filter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			STATE hier, LETTER letter, STATE succ) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			LETTER letter, STATE succ) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			STATE succ) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE state, LETTER letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		// TODO Auto-generated method stub
		return null;
	}

}
