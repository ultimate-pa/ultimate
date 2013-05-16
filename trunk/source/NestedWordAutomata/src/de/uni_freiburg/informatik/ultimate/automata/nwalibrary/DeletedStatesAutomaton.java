package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;

public class DeletedStatesAutomaton<LETTER, STATE> implements
		INestedWordAutomaton<LETTER, STATE> {
	INestedWordAutomaton<LETTER, STATE> m_Nwa;
	Predicate<STATE> m_RemainingStates;
	Predicate<STATE> m_RemainingInitials;
	
	DeletedStatesAutomaton(INestedWordAutomaton<LETTER, STATE> automaton, 
			Predicate<STATE> remainingStates, Predicate<STATE> remainingInitials) {
		m_Nwa = automaton;
		m_RemainingStates = remainingStates;
		m_RemainingInitials = remainingInitials;
	}
	
	DeletedStatesAutomaton(ReachableStatesAutomaton<LETTER, STATE> automaton) {
		m_Nwa = automaton;
		m_RemainingStates = new NoDeadEnd(automaton);
		m_RemainingInitials = new InitialAfterDeadEndRemoval(automaton);
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
		return m_Nwa.getAlphabet();
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Collection<LETTER> getInternalAlphabet() {
		return m_Nwa.getInternalAlphabet();
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
	public STATE getEmptyStackState() {
		return m_Nwa.getEmptyStackState();
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
		return new FilteredIterable<STATE>(m_Nwa.succInternal(state, letter), m_RemainingStates);
	}

	@Override
	public Iterable<STATE> succCall(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Nwa.succCall(state, letter), m_RemainingStates);
	}

	@Override
	public Iterable<STATE> hierPred(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Nwa.succCall(state, letter), m_RemainingStates);
	}

	@Override
	public Iterable<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		return new FilteredIterable<STATE>(m_Nwa.succCall(state, letter), m_RemainingStates);
	}

	@Override
	public Iterable<STATE> predInternal(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Nwa.succCall(state, letter), m_RemainingStates);
	}

	@Override
	public Iterable<STATE> predCall(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Nwa.succCall(state, letter), m_RemainingStates);
	}

	@Override
	public Iterable<STATE> predReturnLin(STATE state, LETTER letter, STATE hier) {
		return new FilteredIterable<STATE>(m_Nwa.succCall(state, letter), m_RemainingStates);
	}

	@Override
	public Iterable<STATE> predReturnHier(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Nwa.succCall(state, letter), m_RemainingStates);
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
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(LETTER letter, STATE succ) {
		Predicate<IncomingCallTransition<LETTER, STATE>> predicate = new Predicate<IncomingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(IncomingCallTransition<LETTER, STATE> trans) {
				return m_RemainingStates.evaluate(trans.getPred());
			}
		};
		return new FilteredIterable<IncomingCallTransition<LETTER, STATE>>(m_Nwa.callPredecessors(letter,succ), predicate);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(STATE succ) {
		Predicate<IncomingCallTransition<LETTER, STATE>> predicate = new Predicate<IncomingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(IncomingCallTransition<LETTER, STATE> trans) {
				return m_RemainingStates.evaluate(trans.getPred());
			}
		};
		return new FilteredIterable<IncomingCallTransition<LETTER, STATE>>(m_Nwa.callPredecessors(succ), predicate);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		Predicate<OutgoingInternalTransition<LETTER, STATE>> predicate = new Predicate<OutgoingInternalTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(OutgoingInternalTransition<LETTER, STATE> trans) {
				return m_RemainingStates.evaluate(trans.getSucc());
			}
		};
		return new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(m_Nwa.internalSuccessors(state,letter), predicate);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(STATE state) {
		Predicate<OutgoingInternalTransition<LETTER, STATE>> predicate = new Predicate<OutgoingInternalTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(OutgoingInternalTransition<LETTER, STATE> trans) {
				return m_RemainingStates.evaluate(trans.getSucc());
			}
		};
		return new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(m_Nwa.internalSuccessors(state), predicate);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(STATE state, LETTER letter) {
		Predicate<OutgoingCallTransition<LETTER, STATE>> predicate = new Predicate<OutgoingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(OutgoingCallTransition<LETTER, STATE> trans) {
				return m_RemainingStates.evaluate(trans.getSucc());
			}
		};
		return new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(m_Nwa.callSuccessors(state,letter), predicate);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(STATE state) {
		Predicate<OutgoingCallTransition<LETTER, STATE>> predicate = new Predicate<OutgoingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(OutgoingCallTransition<LETTER, STATE> trans) {
				return m_RemainingStates.evaluate(trans.getSucc());
			}
		};
		return new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(m_Nwa.callSuccessors(state), predicate);
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
	
	
	
	
	
	public interface Predicate<T> {
		public boolean evaluate(T elem);
	}
	
	public class TruePredicate implements Predicate<STATE> {
		@Override
		public boolean evaluate(STATE state) {
			return true;
		}
	}
	
	public class NoDeadEnd implements Predicate<STATE> {
		final ReachableStatesAutomaton<LETTER, STATE> m_Nwa;
		NoDeadEnd(ReachableStatesAutomaton<LETTER, STATE> nwa) {
			m_Nwa = nwa;
		}
		@Override
		public boolean evaluate(STATE state) {
			return !m_Nwa.isDeadEnd(state);
		}
	}
	
	public class InitialAfterDeadEndRemoval implements Predicate<STATE> {
		final ReachableStatesAutomaton<LETTER, STATE> m_Nwa;
		InitialAfterDeadEndRemoval(ReachableStatesAutomaton<LETTER, STATE> nwa) {
			m_Nwa = nwa;
		}
		@Override
		public boolean evaluate(STATE state) {
			return m_Nwa.isInitialAfterDeadEndRemoval(state);
		}
	}


	
	
	
	public class FilteredIterable<T> implements Iterable<T> {
		final Iterable<T> m_Iterable;
		final Predicate<T> m_Predicate;
		
		public FilteredIterable(Iterable<T> iterable, Predicate<T> predicate) {
			m_Iterable = iterable;
			m_Predicate = predicate;
		}
		
		@Override
		public Iterator<T> iterator() {
			return new Iterator<T>() {
				final Iterator<T> m_Iterator;
				T m_next;
				{
					m_Iterator = m_Iterable.iterator();
					computeNext();
				}
				private void computeNext() {
					while (m_next != null && m_Iterator.hasNext() && 
												!m_Predicate.evaluate(m_next)) {
						m_next = m_Iterator.next();
					}
						
				}

				@Override
				public boolean hasNext() {
					return m_next != null;
				}

				@Override
				public T next() {
					T result = m_next;
					computeNext();
					return result;
				}

				@Override
				public void remove() {
					throw new UnsupportedOperationException();
				}

			};
		}

	}

}
