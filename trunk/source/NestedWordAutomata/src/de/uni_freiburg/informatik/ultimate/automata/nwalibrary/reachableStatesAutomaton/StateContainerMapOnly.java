package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates.ReachProp;

/**
 * Contains STATES and information of transitions.
 *
 * @param <LETTER>
 * @param <STATE>
 */
class StateContainerMapOnly<LETTER,STATE> extends StateContainer<LETTER, STATE> {

	/**
	 * Set of internal transitions PREs x LETTERs x SUCCs stored as map
	 * PREs -> LETTERs -> SUCCs
	 * The keySet of this map is used to store the set of states of this
	 * automaton.
	 */
	Map<LETTER,Set<STATE>> m_InternalOut;

	/**
	 * Set of internal transitions PREs x LETTERs x SUCCs stored as map
	 * SUCCs -> LETTERs -> PREs
	 */
	private Map<LETTER,Set<STATE>> m_InternalIn =
			new HashMap<LETTER,Set<STATE>>();

	/**
	 * Set of call transitions PREs x LETTERs x SUCCs stored as map
	 * PREs -> LETTERs -> SUCCs
	 */
	Map<LETTER,Set<STATE>> m_CallOut =
			new HashMap<LETTER,Set<STATE>>();

	/**
	 * Set of call transitions PREs x LETTERs x SUCCs stored as map
	 * SUCCs -> LETTERs -> PREs
	 */
	private Map<LETTER,Set<STATE>> m_CallIn =
			new HashMap<LETTER,Set<STATE>>();

	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
	 * map LinPREs -> LETTERs -> HierPREs -> SUCCs
	 * 
	 */
	Map<LETTER,Map<STATE,Set<STATE>>> m_ReturnOut =
			new HashMap<LETTER,Map<STATE,Set<STATE>>>();

	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
	 * map HierPREs -> LETTERs -> LinPREs -> SUCCs
	 * 
	 */
	private Map<LETTER,Map<STATE,Set<STATE>>> m_ReturnSummary =
			new HashMap<LETTER,Map<STATE,Set<STATE>>>();

	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
	 * map SUCCs -> LETTERs -> HierPREs -> LinPREs
	 * 
	 */
	private Map<LETTER,Map<STATE,Set<STATE>>> m_ReturnIn =
			new HashMap<LETTER,Map<STATE,Set<STATE>>>();

	private Set<LETTER> m_EmptySetOfLetters = new HashSet<LETTER>(0);

	private Collection<STATE> m_EmptySetOfStates = new HashSet<STATE>(0);

	StateContainerMapOnly(STATE state, int serialNumber, 
			HashMap<STATE,Integer> downStates, boolean canHaveOutgoingReturn) {
		super(state, serialNumber, downStates, canHaveOutgoingReturn);
	}


	@Override
	void addInternalOutgoing(OutgoingInternalTransition<LETTER, STATE> internalOutgoing) {
		LETTER letter = internalOutgoing.getLetter();
		STATE succ = internalOutgoing.getSucc();
		if (m_InternalOut == null) {
			m_InternalOut = new HashMap<LETTER, Set<STATE>>();
		}
		Set<STATE> succs = m_InternalOut.get(letter);
		if (succs == null) {
			succs = new HashSet<STATE>();
			m_InternalOut.put(letter, succs);
		}
		succs.add(succ);
	}

	@Override
	void addInternalIncoming(IncomingInternalTransition<LETTER, STATE> internalIncoming) {
		LETTER letter = internalIncoming.getLetter();
		STATE pred = internalIncoming.getPred();
		if (m_InternalIn == null) {
			m_InternalIn = new HashMap<LETTER, Set<STATE>>();
		}
		Set<STATE> preds = m_InternalIn.get(letter);
		if (preds == null) {
			preds = new HashSet<STATE>();
			m_InternalIn.put(letter,preds);
		}
		preds.add(pred);
	}

	@Override
	void addCallOutgoing(OutgoingCallTransition<LETTER, STATE> callOutgoing) {
		LETTER letter = callOutgoing.getLetter();
		STATE succ = callOutgoing.getSucc();
		if (m_CallOut == null) {
			m_CallOut = new HashMap<LETTER, Set<STATE>>();
		}
		Set<STATE> succs = m_CallOut.get(letter);
		if (succs == null) {
			succs = new HashSet<STATE>();
			m_CallOut.put(letter,succs);
		}
		succs.add(succ);
	}
	@Override
	void addCallIncoming(IncomingCallTransition<LETTER, STATE> callIncoming) {
		LETTER letter = callIncoming.getLetter();
		STATE pred = callIncoming.getPred();
		if (m_CallIn == null) {
			m_CallIn = new HashMap<LETTER, Set<STATE>>();
		}
		Set<STATE> preds = m_CallIn.get(letter);
		if (preds == null) {
			preds = new HashSet<STATE>();
			m_CallIn.put(letter,preds);
		}
		preds.add(pred);
	}
	@Override
	void addReturnOutgoing(OutgoingReturnTransition<LETTER, STATE> returnOutgoing) {
		LETTER letter = returnOutgoing.getLetter();
		STATE hier = returnOutgoing.getHierPred();
		STATE succ = returnOutgoing.getSucc();
		if (m_ReturnOut == null) {
			m_ReturnOut = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
		}
		Map<STATE, Set<STATE>> hier2succs = m_ReturnOut.get(letter);
		if (hier2succs == null) {
			hier2succs = new HashMap<STATE, Set<STATE>>();
			m_ReturnOut.put(letter, hier2succs);
		}
		Set<STATE> succs = hier2succs.get(hier);
		if (succs == null) {
			succs = new HashSet<STATE>();
			hier2succs.put(hier, succs);
		}
		succs.add(succ);
	}
	@Override
	void addReturnIncoming(IncomingReturnTransition<LETTER, STATE> returnIncoming) {
		LETTER letter = returnIncoming.getLetter();
		STATE hier = returnIncoming.getHierPred();
		STATE pred = returnIncoming.getLinPred();
		if (m_ReturnIn == null) {
			m_ReturnIn = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
		}
		Map<STATE, Set<STATE>> hier2preds = m_ReturnIn.get(letter);
		if (hier2preds == null) {
			hier2preds = new HashMap<STATE, Set<STATE>>();
			m_ReturnIn.put(letter, hier2preds);
		}
		Set<STATE> preds = hier2preds.get(hier);
		if (preds == null) {
			preds = new HashSet<STATE>();
			hier2preds.put(hier, preds);
		}
		preds.add(pred);
	}



	@Override
	public Set<LETTER> lettersInternal() {
		Map<LETTER, Set<STATE>> map = m_InternalOut;
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}


	@Override
	public Set<LETTER> lettersInternalIncoming() {
		Map<LETTER, Set<STATE>> map = m_InternalIn;
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}

	@Override
	public Set<LETTER> lettersCall() {
		Map<LETTER, Set<STATE>> map = m_CallOut;
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}

	@Override
	public Set<LETTER> lettersCallIncoming() {
		Map<LETTER, Set<STATE>> map = m_CallIn;
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}

	@Override
	public Set<LETTER> lettersReturn() {
		Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut;
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}

	@Override
	public Set<LETTER> lettersReturnIncoming() {
		Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnIn;
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}


	@Override
	public Collection<STATE> succInternal(LETTER letter) {
		Map<LETTER, Set<STATE>> map = m_InternalOut;
		if (map == null) {
			return m_EmptySetOfStates;
		}
		Set<STATE> result = map.get(letter);
		return result == null ? m_EmptySetOfStates : result;
	}

	@Override
	public Collection<STATE> predInternal(LETTER letter) {
		Map<LETTER, Set<STATE>> map = m_InternalIn;
		if (map == null) {
			return m_EmptySetOfStates;
		}
		Set<STATE> result = map.get(letter);
		return result == null ? m_EmptySetOfStates : result;
	}

	@Override
	public Collection<STATE> succCall(LETTER letter) {
		Map<LETTER, Set<STATE>> map = m_CallOut;
		if (map == null) {
			return m_EmptySetOfStates;
		}
		Set<STATE> result = map.get(letter);
		return result == null ? m_EmptySetOfStates : result;
	}

	@Override
	public Collection<STATE> predCall(LETTER letter) {
		Map<LETTER, Set<STATE>> map = m_CallIn;
		if (map == null) {
			return m_EmptySetOfStates;
		}
		Set<STATE> result = map.get(letter);
		return result == null ? m_EmptySetOfStates : result;
	}

	@Override
	public Collection<STATE> hierPred(LETTER letter) {
		Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut;
		if (map == null) {
			return m_EmptySetOfStates;
		}
		Map<STATE, Set<STATE>> hier2succs = map.get(letter);
		return hier2succs == null ? m_EmptySetOfStates : hier2succs.keySet();
	}

	@Override
	public Collection<STATE> succReturn(STATE hier, LETTER letter) {
		Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut;
		if (map == null) {
			return m_EmptySetOfStates;
		}
		Map<STATE, Set<STATE>> hier2succs = map.get(letter);
		if (hier2succs == null) {
			return m_EmptySetOfStates;
		}
		Set<STATE> result = hier2succs.get(hier);
		return result == null ? m_EmptySetOfStates : result;
	}

	@Override
	public Collection<STATE> predReturnLin(LETTER letter, STATE hier) {
		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds  = m_ReturnIn;
		if (letter2hier2preds == null) {
			return m_EmptySetOfStates;
		}
		Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		if (hier2preds == null) {
			return m_EmptySetOfStates;
		}
		Set<STATE> result = hier2preds.get(hier);
		return result == null ? m_EmptySetOfStates : result;
	}

	@Override
	public Collection<STATE> predReturnHier(LETTER letter) {
		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds  = m_ReturnIn;
		if (letter2hier2preds == null) {
			return m_EmptySetOfStates ;
		}
		Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		if (hier2preds == null) {
			return m_EmptySetOfStates;
		}
		return hier2preds.keySet();
	}





	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final LETTER letter) {
		return new Iterable<IncomingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingInternalTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Set<STATE>> letter2pred = m_InternalIn;
						if (letter2pred != null) {
							if (letter2pred.get(letter) != null) {
								m_Iterator = letter2pred.get(letter).iterator();
							} else {
								m_Iterator = null;
							}
						} else {
							m_Iterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_Iterator != null && m_Iterator.hasNext();
					}

					@Override
					public IncomingInternalTransition<LETTER, STATE> next() {
						if (m_Iterator == null) {
							throw new NoSuchElementException();
						} else {
							STATE pred = m_Iterator.next(); 
							return new IncomingInternalTransition<LETTER, STATE>(pred, letter);
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}



	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors() {
		return new Iterable<IncomingInternalTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all IncomingInternalTransition of succ.
			 * Iterates over all incoming internal letters and uses the 
			 * iterators returned by internalPredecessors(letter, succ)
			 */
			@Override
			public Iterator<IncomingInternalTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
					Iterator<LETTER> m_LetterIterator;
					LETTER m_CurrentLetter;
					Iterator<IncomingInternalTransition<LETTER, STATE>> m_CurrentIterator;
					{
						m_LetterIterator = lettersInternalIncoming().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = internalPredecessors(
										m_CurrentLetter).iterator();
							} while (!m_CurrentIterator.hasNext()
									&& m_LetterIterator.hasNext());
							if (!m_CurrentIterator.hasNext()) {
								m_CurrentLetter = null;
								m_CurrentIterator = null;
							}
						} else {
							m_CurrentLetter = null;
							m_CurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_CurrentLetter != null;
					}

					@Override
					public IncomingInternalTransition<LETTER, STATE> next() {
						if (m_CurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							IncomingInternalTransition<LETTER, STATE> result = 
									m_CurrentIterator.next();
							if (!m_CurrentIterator.hasNext()) {
								nextLetter();
							}
							return result;
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}





	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final LETTER letter) {
		return new Iterable<IncomingCallTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingCallTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingCallTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingCallTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Set<STATE>> letter2pred = m_CallIn;
						if (letter2pred != null) {
							if (letter2pred.get(letter) != null) {
								m_Iterator = letter2pred.get(letter).iterator();
							} else {
								m_Iterator = null;
							}
						} else {
							m_Iterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_Iterator != null && m_Iterator.hasNext();
					}

					@Override
					public IncomingCallTransition<LETTER, STATE> next() {
						if (m_Iterator == null) {
							throw new NoSuchElementException();
						} else {
							STATE pred = m_Iterator.next(); 
							return new IncomingCallTransition<LETTER, STATE>(pred, letter);
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}



	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors() {
		return new Iterable<IncomingCallTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all IncomingCallTransition of succ.
			 * Iterates over all incoming call letters and uses the 
			 * iterators returned by callPredecessors(letter, succ)
			 */
			@Override
			public Iterator<IncomingCallTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingCallTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingCallTransition<LETTER, STATE>>() {
					Iterator<LETTER> m_LetterIterator;
					LETTER m_CurrentLetter;
					Iterator<IncomingCallTransition<LETTER, STATE>> m_CurrentIterator;
					{
						m_LetterIterator = lettersCallIncoming().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = callPredecessors(
										m_CurrentLetter).iterator();
							} while (!m_CurrentIterator.hasNext()
									&& m_LetterIterator.hasNext());
							if (!m_CurrentIterator.hasNext()) {
								m_CurrentLetter = null;
								m_CurrentIterator = null;
							}
						} else {
							m_CurrentLetter = null;
							m_CurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_CurrentLetter != null;
					}

					@Override
					public IncomingCallTransition<LETTER, STATE> next() {
						if (m_CurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							IncomingCallTransition<LETTER, STATE> result = 
									m_CurrentIterator.next();
							if (!m_CurrentIterator.hasNext()) {
								nextLetter();
							}
							return result;
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}



	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE hier, final LETTER letter) {
		return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingReturnTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = m_ReturnIn;
						if (letter2hier2pred != null) {
							Map<STATE, Set<STATE>> hier2pred = letter2hier2pred.get(letter);
							if (hier2pred != null) {
								if (hier2pred.get(hier) != null) {
									m_Iterator = hier2pred.get(hier).iterator();
								} else {
									m_Iterator = null;
								}
							} else {
								m_Iterator = null;
							}
						} else {
							m_Iterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_Iterator != null && m_Iterator.hasNext();
					}

					@Override
					public IncomingReturnTransition<LETTER, STATE> next() {
						if (m_Iterator == null) {
							throw new NoSuchElementException();
						} else {
							STATE pred = m_Iterator.next(); 
							return new IncomingReturnTransition<LETTER, STATE>(pred, hier, letter);
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}


	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final LETTER letter) {
		return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all IncomingReturnTransition of succ.
			 * Iterates over all incoming return letters and uses the 
			 * iterators returned by returnPredecessors(hier, letter, succ)
			 */
			@Override
			public Iterator<IncomingReturnTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
					Iterator<STATE> m_HierIterator;
					STATE m_CurrentHier;
					Iterator<IncomingReturnTransition<LETTER, STATE>> m_CurrentIterator;
					{
						m_HierIterator = predReturnHier(letter).iterator();
						nextHier();
					}

					private void nextHier() {
						if (m_HierIterator.hasNext()) {
							do {
								m_CurrentHier = m_HierIterator.next();
								m_CurrentIterator = returnPredecessors(
										m_CurrentHier, letter).iterator();
							} while (!m_CurrentIterator.hasNext()
									&& m_HierIterator.hasNext());
							if (!m_CurrentIterator.hasNext()) {
								m_CurrentHier = null;
								m_CurrentIterator = null;
							}
						} else {
							m_CurrentHier = null;
							m_CurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_CurrentHier != null;
					}

					@Override
					public IncomingReturnTransition<LETTER, STATE> next() {
						if (m_CurrentHier == null) {
							throw new NoSuchElementException();
						} else {
							IncomingReturnTransition<LETTER, STATE> result = 
									m_CurrentIterator.next();
							if (!m_CurrentIterator.hasNext()) {
								nextHier();
							}
							return result;
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}


	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors() {
		return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all IncomingReturnTransition of succ.
			 * Iterates over all incoming return letters and uses the 
			 * iterators returned by returnPredecessors(letter, succ)
			 */
			@Override
			public Iterator<IncomingReturnTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
					Iterator<LETTER> m_LetterIterator;
					LETTER m_CurrentLetter;
					Iterator<IncomingReturnTransition<LETTER, STATE>> m_CurrentIterator;
					{
						m_LetterIterator = lettersReturnIncoming().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = returnPredecessors(
										m_CurrentLetter).iterator();
							} while (!m_CurrentIterator.hasNext()
									&& m_LetterIterator.hasNext());
							if (!m_CurrentIterator.hasNext()) {
								m_CurrentLetter = null;
								m_CurrentIterator = null;
							}
						} else {
							m_CurrentLetter = null;
							m_CurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_CurrentLetter != null;
					}

					@Override
					public IncomingReturnTransition<LETTER, STATE> next() {
						if (m_CurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							IncomingReturnTransition<LETTER, STATE> result = 
									m_CurrentIterator.next();
							if (!m_CurrentIterator.hasNext()) {
								nextLetter();
							}
							return result;
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}



	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final LETTER letter) {
		return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Set<STATE>> letter2succ = m_InternalOut;
						if (letter2succ != null) {
							if (letter2succ.get(letter) != null) {
								m_Iterator = letter2succ.get(letter).iterator();
							} else {
								m_Iterator = null;
							}
						} else {
							m_Iterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_Iterator != null && m_Iterator.hasNext();
					}

					@Override
					public OutgoingInternalTransition<LETTER, STATE> next() {
						if (m_Iterator == null) {
							throw new NoSuchElementException();
						} else {
							STATE succ = m_Iterator.next(); 
							return new OutgoingInternalTransition<LETTER, STATE>(letter, succ);
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors() {
		return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingInternalTransition of state.
			 * Iterates over all outgoing internal letters and uses the 
			 * iterators returned by internalSuccessors(state, letter)
			 */
			@Override
			public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
					Iterator<LETTER> m_LetterIterator;
					LETTER m_CurrentLetter;
					Iterator<OutgoingInternalTransition<LETTER, STATE>> m_CurrentIterator;
					{
						m_LetterIterator = lettersInternal().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = internalSuccessors(
										m_CurrentLetter).iterator();
							} while (!m_CurrentIterator.hasNext()
									&& m_LetterIterator.hasNext());
							if (!m_CurrentIterator.hasNext()) {
								m_CurrentLetter = null;
								m_CurrentIterator = null;
							}
						} else {
							m_CurrentLetter = null;
							m_CurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_CurrentLetter != null;
					}

					@Override
					public OutgoingInternalTransition<LETTER, STATE> next() {
						if (m_CurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							OutgoingInternalTransition<LETTER, STATE> result = 
									m_CurrentIterator.next();
							if (!m_CurrentIterator.hasNext()) {
								nextLetter();
							}
							return result;
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}





	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final LETTER letter) {
		return new Iterable<OutgoingCallTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingCallTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingCallTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Set<STATE>> letter2succ = m_CallOut;
						if (letter2succ != null) {
							if (letter2succ.get(letter) != null) {
								m_Iterator = letter2succ.get(letter).iterator();
							} else {
								m_Iterator = null;
							}
						} else {
							m_Iterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_Iterator != null && m_Iterator.hasNext();
					}

					@Override
					public OutgoingCallTransition<LETTER, STATE> next() {
						if (m_Iterator == null) {
							throw new NoSuchElementException();
						} else {
							STATE succ = m_Iterator.next(); 
							return new OutgoingCallTransition<LETTER, STATE>(letter, succ);
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors() {
		return new Iterable<OutgoingCallTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingCallTransition of state.
			 * Iterates over all outgoing call letters and uses the 
			 * iterators returned by callSuccessors(state, letter)
			 */
			@Override
			public Iterator<OutgoingCallTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingCallTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
					Iterator<LETTER> m_LetterIterator;
					LETTER m_CurrentLetter;
					Iterator<OutgoingCallTransition<LETTER, STATE>> m_CurrentIterator;
					{
						m_LetterIterator = lettersCall().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = callSuccessors(m_CurrentLetter).iterator();
							} while (!m_CurrentIterator.hasNext()
									&& m_LetterIterator.hasNext());
							if (!m_CurrentIterator.hasNext()) {
								m_CurrentLetter = null;
								m_CurrentIterator = null;
							}
						} else {
							m_CurrentLetter = null;
							m_CurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_CurrentLetter != null;
					}

					@Override
					public OutgoingCallTransition<LETTER, STATE> next() {
						if (m_CurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							OutgoingCallTransition<LETTER, STATE> result = 
									m_CurrentIterator.next();
							if (!m_CurrentIterator.hasNext()) {
								nextLetter();
							}
							return result;
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}








	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE hier, final LETTER letter) {
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succ = m_ReturnOut;
						if (letter2hier2succ != null) {
							Map<STATE, Set<STATE>> hier2succ = letter2hier2succ.get(letter);
							if (hier2succ != null) {
								if (hier2succ.get(hier) != null) {
									m_Iterator = hier2succ.get(hier).iterator();
								} else {
									m_Iterator = null;
								}
							} else {
								m_Iterator = null;
							}
						} else {
							m_Iterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_Iterator != null && m_Iterator.hasNext();
					}

					@Override
					public OutgoingReturnTransition<LETTER, STATE> next() {
						if (m_Iterator == null) {
							throw new NoSuchElementException();
						} else {
							STATE succ = m_Iterator.next(); 
							return new OutgoingReturnTransition<LETTER, STATE>(hier, letter, succ);
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}


	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final LETTER letter) {
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingReturnTransition of state.
			 * Iterates over all outgoing return letters and uses the 
			 * iterators returned by returnSuccecessors(state, letter)
			 */
			@Override
			public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					Iterator<STATE> m_HierIterator;
					STATE m_CurrentHier;
					Iterator<OutgoingReturnTransition<LETTER, STATE>> m_CurrentIterator;
					{
						m_HierIterator = hierPred(letter).iterator();
						nextHier();
					}

					private void nextHier() {
						if (m_HierIterator.hasNext()) {
							do {
								m_CurrentHier = m_HierIterator.next();
								m_CurrentIterator = returnSuccessors(
										m_CurrentHier, letter).iterator();
							} while (!m_CurrentIterator.hasNext()
									&& m_HierIterator.hasNext());
							if (!m_CurrentIterator.hasNext()) {
								m_CurrentHier = null;
								m_CurrentIterator = null;
							}
						} else {
							m_CurrentHier = null;
							m_CurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_CurrentHier != null;
					}

					@Override
					public OutgoingReturnTransition<LETTER, STATE> next() {
						if (m_CurrentHier == null) {
							throw new NoSuchElementException();
						} else {
							OutgoingReturnTransition<LETTER, STATE> result = 
									m_CurrentIterator.next();
							if (!m_CurrentIterator.hasNext()) {
								nextHier();
							}
							return result;
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			final STATE hier) {
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingReturnTransition of state with 
			 * hierarchical successor hier. 
			 * Iterates over all outgoing return letters and uses the 
			 * iterators returned by returnSuccecessors(state, hier, letter)
			 */
			@Override
			public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					Iterator<LETTER> m_LetterIterator;
					LETTER m_CurrentLetter;
					Iterator<OutgoingReturnTransition<LETTER, STATE>> m_CurrentIterator;
					{
						m_LetterIterator = lettersReturn().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = returnSuccessors(
										hier, m_CurrentLetter).iterator();
							} while (!m_CurrentIterator.hasNext()
									&& m_LetterIterator.hasNext());
							if (!m_CurrentIterator.hasNext()) {
								m_CurrentLetter = null;
								m_CurrentIterator = null;
							}
						} else {
							m_CurrentLetter = null;
							m_CurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_CurrentLetter != null;
					}

					@Override
					public OutgoingReturnTransition<LETTER, STATE> next() {
						if (m_CurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							OutgoingReturnTransition<LETTER, STATE> result = 
									m_CurrentIterator.next();
							if (!m_CurrentIterator.hasNext()) {
								nextLetter();
							}
							return result;
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}


	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			) {
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingReturnTransition of state.
			 * Iterates over all outgoing return letters and uses the 
			 * iterators returned by returnSuccessors(state, letter)
			 */
			@Override
			public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					Iterator<LETTER> m_LetterIterator;
					LETTER m_CurrentLetter;
					Iterator<OutgoingReturnTransition<LETTER, STATE>> m_CurrentIterator;
					{
						m_LetterIterator = lettersReturn().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = returnSuccessors(m_CurrentLetter).iterator();
							} while (!m_CurrentIterator.hasNext()
									&& m_LetterIterator.hasNext());
							if (!m_CurrentIterator.hasNext()) {
								m_CurrentLetter = null;
								m_CurrentIterator = null;
							}
						} else {
							m_CurrentLetter = null;
							m_CurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return m_CurrentLetter != null;
					}

					@Override
					public OutgoingReturnTransition<LETTER, STATE> next() {
						if (m_CurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							OutgoingReturnTransition<LETTER, STATE> result = 
									m_CurrentIterator.next();
							if (!m_CurrentIterator.hasNext()) {
								nextLetter();
							}
							return result;
						}
					}

					@Override
					public void remove() {
						throw new UnsupportedOperationException();
					}
				};
				return iterator;
			}
		};
	}
}

