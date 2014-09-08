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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;

public class NestedWordAutomatonFilteredStates<LETTER, STATE> implements
		INestedWordAutomatonOldApi<LETTER, STATE>, INestedWordAutomaton<LETTER, STATE>, IDoubleDeckerAutomaton<LETTER, STATE> {
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Nwa;
	private final Set<STATE> m_RemainingStates;
	private final Set<STATE> m_newInitials;
	private final Set<STATE> m_newFinals;
	private final NestedWordAutomatonReachableStates<LETTER, STATE>.AncestorComputation m_AncestorComputation;
	
	NestedWordAutomatonFilteredStates(INestedWordAutomatonOldApi<LETTER, STATE> automaton, 
			Set<STATE> remainingStates, Set<STATE> newInitials, Set<STATE> newFinals) {
		m_Nwa = automaton;
		m_RemainingStates = remainingStates;
		m_newInitials = newInitials;
		m_newFinals = newFinals;
		m_AncestorComputation = null;
	}
	
	public NestedWordAutomatonFilteredStates(
			NestedWordAutomatonReachableStates<LETTER, STATE> automaton, 
			NestedWordAutomatonReachableStates<LETTER, STATE>.AncestorComputation ancestorComputation) {
		m_Nwa = automaton;
		m_RemainingStates = ancestorComputation.getStates();
		m_newInitials = ancestorComputation.getInitials();
		m_newFinals = ancestorComputation.getFinals();
		m_AncestorComputation = ancestorComputation;
	}
	
	public Set<STATE> getDownStates(STATE up) {
		if (m_AncestorComputation != null) {
			return m_AncestorComputation.getDownStates(up);
		}
		throw new UnsupportedOperationException();
	}

	@Override
	public int size() {
		return getStates().size();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return m_Nwa.getAlphabet();
	}

	@Override
	public String sizeInformation() {
		return m_RemainingStates.size() + " states.";
	}

	@Override
	public Set<LETTER> getInternalAlphabet() {
		return m_Nwa.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return m_Nwa.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return m_Nwa.getReturnAlphabet();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_Nwa.getStateFactory();
	}

	@Override
	public Collection<STATE> getStates() {
		return m_RemainingStates;
	}

	@Override
	public Collection<STATE> getInitialStates() {
		return m_newInitials;
	}

	@Override
	public Collection<STATE> getFinalStates() {
		return m_newFinals;
	}

	@Override
	public boolean isInitial(STATE state) {
		return m_newInitials.contains(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return m_newFinals.contains(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return m_Nwa.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (OutgoingInternalTransition<LETTER, STATE> outTrans : internalSuccessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (OutgoingCallTransition<LETTER, STATE> outTrans : callSuccessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Set<LETTER> lettersInternalIncoming(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (IncomingInternalTransition<LETTER, STATE> outTrans : internalPredecessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Set<LETTER> lettersCallIncoming(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (IncomingCallTransition<LETTER, STATE> outTrans : callPredecessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Set<LETTER> lettersReturnIncoming(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (IncomingReturnTransition<LETTER, STATE> outTrans : returnPredecessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Set<LETTER> lettersReturnSummary(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (SummaryReturnTransition<LETTER, STATE> outTrans : returnSummarySuccessor(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Iterable<STATE> succInternal(final STATE state, final LETTER letter) {
		return new FilteredIterable<STATE>(m_Nwa.succInternal(state, letter), m_RemainingStates);
	}

	@Override
	public Iterable<STATE> succCall(STATE state, LETTER letter) {
		Set<STATE> result = new HashSet<STATE>();
		for ( OutgoingCallTransition<LETTER, STATE> outTrans  : callSuccessors(state, letter)) {
			result.add(outTrans.getSucc());
		}
		return result;
	}

	@Override
	public Iterable<STATE> hierPred(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Nwa.hierPred(state, letter), m_RemainingStates);
	}

	@Override
	public Iterable<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		return new FilteredIterable<STATE>(m_Nwa.succReturn(state, hier, letter), m_RemainingStates);
	}

	@Override
	public Iterable<STATE> predInternal(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Nwa.predInternal(state, letter), m_RemainingStates);
	}

	@Override
	public Iterable<STATE> predCall(STATE state, LETTER letter) {
		Set<STATE> result = new HashSet<STATE>();
		for (IncomingCallTransition<LETTER, STATE> inTrans  : callPredecessors(letter, state)) {
			result.add(inTrans.getPred());
		}
		return result;
	}

	@Override
	public boolean finalIsTrap() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isDeterministic() {
		return false;
	}

	@Override
	public boolean isTotal() {
		throw new UnsupportedOperationException();
	}



	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(LETTER letter, STATE succ) {
		SetSupportingOnlyContains<IncomingInternalTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<IncomingInternalTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				IncomingInternalTransition<LETTER, STATE> trans = (IncomingInternalTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getPred());
			}
		};
		return new FilteredIterable<IncomingInternalTransition<LETTER, STATE>>(m_Nwa.internalPredecessors(letter,succ), predicate);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(STATE succ) {
		SetSupportingOnlyContains<IncomingInternalTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<IncomingInternalTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				IncomingInternalTransition<LETTER, STATE> trans = (IncomingInternalTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getPred());
			}
		};
		return new FilteredIterable<IncomingInternalTransition<LETTER, STATE>>(m_Nwa.internalPredecessors(succ), predicate);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(LETTER letter, final STATE succ) {
		SetSupportingOnlyContains<IncomingCallTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<IncomingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				IncomingCallTransition<LETTER, STATE> trans = (IncomingCallTransition<LETTER, STATE>) o;
				// filter out also transitions that are not contained any more 
				// because (succ, trans.getPred()) is not a DoubleDecker of the
				// resulting automaton
				return m_RemainingStates.contains(trans.getPred()) && isDoubleDecker(succ, trans.getPred());
			}
		};
		return new FilteredIterable<IncomingCallTransition<LETTER, STATE>>(m_Nwa.callPredecessors(letter,succ), predicate);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ) {
		SetSupportingOnlyContains<IncomingCallTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<IncomingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				IncomingCallTransition<LETTER, STATE> trans = (IncomingCallTransition<LETTER, STATE>) o;
				// filter out also transitions that are not contained any more 
				// because (succ, trans.getPred()) is not a DoubleDecker of the
				// resulting automaton
				return m_RemainingStates.contains(trans.getPred()) && isDoubleDecker(succ, trans.getPred());
			}
		};
		return new FilteredIterable<IncomingCallTransition<LETTER, STATE>>(m_Nwa.callPredecessors(succ), predicate);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(STATE state, LETTER letter) {
		SetSupportingOnlyContains<OutgoingInternalTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<OutgoingInternalTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				OutgoingInternalTransition<LETTER, STATE> trans = (OutgoingInternalTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getSucc());
			}
		};
		return new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(m_Nwa.internalSuccessors(state,letter), predicate);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(STATE state) {
		SetSupportingOnlyContains<OutgoingInternalTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<OutgoingInternalTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				OutgoingInternalTransition<LETTER, STATE> trans = (OutgoingInternalTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getSucc());
			}
		};
		return new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(m_Nwa.internalSuccessors(state), predicate);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, LETTER letter) {
		SetSupportingOnlyContains<OutgoingCallTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<OutgoingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				OutgoingCallTransition<LETTER, STATE> trans = (OutgoingCallTransition<LETTER, STATE>) o;
				// filter out also transitions that are not contained any more 
				// because (trans.getSucc(), state) is not a DoubleDecker of the
				// resulting automaton
				return m_RemainingStates.contains(trans.getSucc()) && isDoubleDecker(trans.getSucc(), state);
			}
		};
		return new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(m_Nwa.callSuccessors(state,letter), predicate);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		SetSupportingOnlyContains<OutgoingCallTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<OutgoingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				OutgoingCallTransition<LETTER, STATE> trans = (OutgoingCallTransition<LETTER, STATE>) o;
				// filter out also transitions that are not contained any more 
				// because (trans.getSucc(), state) is not a DoubleDecker of the
				// resulting automaton
				return m_RemainingStates.contains(trans.getSucc()) && isDoubleDecker(trans.getSucc(), state);
			}
		};
		return new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(m_Nwa.callSuccessors(state), predicate);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(STATE hier, LETTER letter, STATE succ) {
		SetSupportingOnlyContains<IncomingReturnTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<IncomingReturnTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				IncomingReturnTransition<LETTER, STATE> trans = (IncomingReturnTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getLinPred());
			}
		};
		return new FilteredIterable<IncomingReturnTransition<LETTER, STATE>>(m_Nwa.returnPredecessors(hier, letter, succ), predicate);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(LETTER letter, STATE succ) {
		SetSupportingOnlyContains<IncomingReturnTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<IncomingReturnTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				IncomingReturnTransition<LETTER, STATE> trans = (IncomingReturnTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getLinPred()) && m_RemainingStates.contains(trans.getHierPred());
			}
		};
		return new FilteredIterable<IncomingReturnTransition<LETTER, STATE>>(m_Nwa.returnPredecessors(letter, succ), predicate);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(STATE succ) {
		SetSupportingOnlyContains<IncomingReturnTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<IncomingReturnTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				IncomingReturnTransition<LETTER, STATE> trans = (IncomingReturnTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getLinPred()) && m_RemainingStates.contains(trans.getHierPred());
			}
		};
		return new FilteredIterable<IncomingReturnTransition<LETTER, STATE>>(m_Nwa.returnPredecessors(succ), predicate);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(STATE state, STATE hier, LETTER letter) {
		SetSupportingOnlyContains<OutgoingReturnTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<OutgoingReturnTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				OutgoingReturnTransition<LETTER, STATE> trans = (OutgoingReturnTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getSucc());
			}
		};
		return new FilteredIterable<OutgoingReturnTransition<LETTER, STATE>>(m_Nwa.returnSucccessors(state,hier,letter), predicate);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(STATE state, LETTER letter) {
		SetSupportingOnlyContains<OutgoingReturnTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<OutgoingReturnTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				OutgoingReturnTransition<LETTER, STATE> trans = (OutgoingReturnTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getHierPred()) && m_RemainingStates.contains(trans.getSucc());
			}
		};
		return new FilteredIterable<OutgoingReturnTransition<LETTER, STATE>>(m_Nwa.returnSuccessors(state, letter), predicate);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(STATE state) {
		SetSupportingOnlyContains<OutgoingReturnTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<OutgoingReturnTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				OutgoingReturnTransition<LETTER, STATE> trans = (OutgoingReturnTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getHierPred()) && m_RemainingStates.contains(trans.getSucc());
			}
		};
		return new FilteredIterable<OutgoingReturnTransition<LETTER, STATE>>(m_Nwa.returnSuccessors(state), predicate);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(STATE state, STATE hier) {
		SetSupportingOnlyContains<OutgoingReturnTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<OutgoingReturnTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				OutgoingReturnTransition<LETTER, STATE> trans = (OutgoingReturnTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getSucc());
			}
		};
		return new FilteredIterable<OutgoingReturnTransition<LETTER, STATE>>(m_Nwa.returnSuccessorsGivenHier(state,hier), predicate);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(LETTER letter, STATE hier) {
		SetSupportingOnlyContains<SummaryReturnTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<SummaryReturnTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				SummaryReturnTransition<LETTER, STATE> trans = (SummaryReturnTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getSucc()) && m_RemainingStates.contains(trans.getLinPred());
			}
		};
		return new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(m_Nwa.returnSummarySuccessor(letter, hier), predicate);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(STATE hier) {
		SetSupportingOnlyContains<SummaryReturnTransition<LETTER, STATE>> predicate = new SetSupportingOnlyContains<SummaryReturnTransition<LETTER,STATE>>() {
			@Override
			public boolean contains(Object o) {
				SummaryReturnTransition<LETTER, STATE> trans = (SummaryReturnTransition<LETTER, STATE>) o;
				return m_RemainingStates.contains(trans.getSucc()) && m_RemainingStates.contains(trans.getLinPred());
			}
		};
		return new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(m_Nwa.returnSummarySuccessor(hier), predicate);
	}
	
	@Override
	public String toString() {
		return (new AtsDefinitionPrinter<String,String>("nwa", this)).getDefinitionAsString();
	}
	
	
	
	public abstract class SetSupportingOnlyContains<T> implements Set<T> {

		@Override
		public boolean add(T e) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean addAll(Collection<? extends T> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void clear() {
			throw new UnsupportedOperationException();
		}

		@Override
		public abstract boolean contains(Object o);

		@Override
		public boolean containsAll(Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isEmpty() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Iterator<T> iterator() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean remove(Object o) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean removeAll(Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean retainAll(Collection<?> c) {
			throw new UnsupportedOperationException();
		}

		@Override
		public int size() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Object[] toArray() {
			throw new UnsupportedOperationException();
		}

		@Override
		public <T> T[] toArray(T[] a) {
			throw new UnsupportedOperationException();
		}
		

	}
	


	
	
	
	public class FilteredIterable<T> implements Iterable<T> {
		final Iterable<T> m_Iterable;
		final Set<T> m_RemainingElements;
		
		public FilteredIterable(Iterable<T> iterable, Set<T> remainingElements) {
			m_Iterable = iterable;
			m_RemainingElements = remainingElements;
		}
		
		@Override
		public Iterator<T> iterator() {
			return new Iterator<T>() {
				final Iterator<T> m_Iterator;
				T m_next = null;
				{
					m_Iterator = m_Iterable.iterator();
					if (m_Iterator.hasNext()) {
						getNextThatSatisfiesPredicate();
					}
				}
				private void getNextThatSatisfiesPredicate() {
					if (m_Iterator.hasNext()) {
						m_next = m_Iterator.next();
						while (m_next != null && !m_RemainingElements.contains(m_next)) {
							if (m_Iterator.hasNext()) {
								m_next = m_Iterator.next();
							} else {
								m_next = null;
							}
						}
					} else {
						m_next = null;
					}
				}

				@Override
				public boolean hasNext() {
					return m_next != null;
				}

				@Override
				public T next() {
					T result = m_next;
					getNextThatSatisfiesPredicate();
					return result;
				}

				@Override
				public void remove() {
					throw new UnsupportedOperationException();
				}

			};
		}

	}





	@Override
	public boolean isDoubleDecker(STATE up, STATE down) {
		return m_AncestorComputation.isDownState(up, down);
	}


}
