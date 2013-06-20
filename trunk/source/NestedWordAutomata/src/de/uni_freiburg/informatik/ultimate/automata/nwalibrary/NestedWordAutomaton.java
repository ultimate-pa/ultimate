package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.ConcurrentProduct;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;



/**
 * 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class NestedWordAutomaton<LETTER,STATE> implements INestedWordAutomatonOldApi<LETTER,STATE>, INestedWordAutomaton<LETTER, STATE> {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	
	private Set<LETTER> m_InternalAlphabet;
	private Set<LETTER> m_CallAlphabet;
	private Set<LETTER> m_ReturnAlphabet;
	
	protected final StateFactory<STATE> m_StateFactory;
	
	/**
	 * Set of internal transitions PREs x LETTERs x SUCCs stored as map
	 * PREs -> LETTERs -> SUCCs
	 * The keySet of this map is used to store the set of states of this
	 * automaton.
	 */
	private Map<STATE,Map<LETTER,Set<STATE>>> m_InternalOut =
			new HashMap<STATE,Map<LETTER,Set<STATE>>>();
	
	/**
	 * Set of internal transitions PREs x LETTERs x SUCCs stored as map
	 * SUCCs -> LETTERs -> PREs
	 */
	private Map<STATE,Map<LETTER,Set<STATE>>> m_InternalIn =
			new HashMap<STATE,Map<LETTER,Set<STATE>>>();
	
	/**
	 * Set of call transitions PREs x LETTERs x SUCCs stored as map
	 * PREs -> LETTERs -> SUCCs
	 */
	private Map<STATE,Map<LETTER,Set<STATE>>> m_CallOut =
			new HashMap<STATE,Map<LETTER,Set<STATE>>>();
	
	/**
	 * Set of call transitions PREs x LETTERs x SUCCs stored as map
	 * SUCCs -> LETTERs -> PREs
	 */
	private Map<STATE,Map<LETTER,Set<STATE>>> m_CallIn =
			new HashMap<STATE,Map<LETTER,Set<STATE>>>();
	
	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
	 * map LinPREs -> LETTERs -> HierPREs -> SUCCs
	 * 
	 */
	private Map<STATE,Map<LETTER,Map<STATE,Set<STATE>>>> m_ReturnOut =
			new HashMap<STATE,Map<LETTER,Map<STATE,Set<STATE>>>>();
	
	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
	 * map HierPREs -> LETTERs -> LinPREs -> SUCCs
	 * 
	 */
	private Map<STATE,Map<LETTER,Map<STATE,Set<STATE>>>> m_ReturnSummary =
			new HashMap<STATE,Map<LETTER,Map<STATE,Set<STATE>>>>();
	
	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
	 * map SUCCs -> LETTERs -> HierPREs -> LinPREs
	 * 
	 */
	private Map<STATE,Map<LETTER,Map<STATE,Set<STATE>>>> m_ReturnIn =
			new HashMap<STATE,Map<LETTER,Map<STATE,Set<STATE>>>>();

	
	private Set<STATE> m_InitialStates = new HashSet<STATE>();
	private Set<STATE> m_FinalStates = new HashSet<STATE>();
	
	
	protected final STATE emptyStackState;
	

	
	
	
	
	
	
	
	@Override
	public Set<LETTER> getInternalAlphabet() {
		return m_InternalAlphabet;
	}	
	
	@Override
	public Set<LETTER> getCallAlphabet() {
		return m_CallAlphabet == null ? new HashSet<LETTER>(0) : m_CallAlphabet;
	}
	
	@Override
	public Set<LETTER> getReturnAlphabet() {
		return m_ReturnAlphabet == null ? new HashSet<LETTER>(0) : m_ReturnAlphabet;
	}
	
	@Override
	public Collection<STATE> getStates() {
		return this.m_InternalOut.keySet();
	}
	
	@Override
	public STATE getEmptyStackState() {
		return this.emptyStackState;
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return this.m_StateFactory;
	}
	
	boolean contains(STATE state) {
		return m_InternalOut.containsKey(state);
	}
	
	
	@Override
	public int size() {
		return m_InternalOut.size();
	}


	@Override
	public Set<LETTER> getAlphabet() {
		return getInternalAlphabet();
	}

	@Override
	public Collection<STATE> getInitialStates() {
		return m_InitialStates;
	}


	@Override
	public boolean isInitial(STATE state) {
		assert contains(state);
		return m_InitialStates.contains(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		assert contains(state);
		return m_FinalStates.contains(state);
	}

	@Override
	public Collection<STATE> getFinalStates() {
		return m_FinalStates;
	}
	

	public void addState(boolean isInitial, boolean isFinal, STATE state) {
		assert (state != null);
		if (m_InternalOut.containsKey(state)) {
			throw new IllegalArgumentException("State already exists");
		}
		assert (!m_InternalIn.containsKey(state));
		//FIXME others
		m_InternalOut.put(state, null);
		
		if (isInitial) {
			m_InitialStates.add(state);
		}
		if (isFinal) {
			m_FinalStates.add(state);
		}
		//FIXME remove this
//		return state;
//		assert checkTransitionsReturnedConsistent();
	}
	
	Set<LETTER> m_EmptySetOfLetters = 
			Collections.unmodifiableSet(new HashSet<LETTER>(0));
	Set<STATE> m_EmptySetOfStates = 
			Collections.unmodifiableSet(new HashSet<STATE>(0));


	
	
	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		Map<LETTER, Set<STATE>> map = m_InternalOut.get(state);
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersInternalIncoming(STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		Map<LETTER, Set<STATE>> map = m_InternalIn.get(state);
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersCall(STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		Map<LETTER, Set<STATE>> map = m_CallOut.get(state);
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersCallIncoming(STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		Map<LETTER, Set<STATE>> map = m_CallIn.get(state);
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		 Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut.get(state);
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersReturnIncoming(STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		 Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnIn.get(state);
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}
	
	
	@Override
	public Set<LETTER> lettersReturnSummary(STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		 Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnSummary.get(state);
		return map == null ? m_EmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Collection<STATE> succInternal(STATE state, LETTER letter) {
		assert contains(state);
		Map<LETTER, Set<STATE>> map = m_InternalOut.get(state);
		if (map == null) {
			return m_EmptySetOfStates;
		}
		Set<STATE> result = map.get(letter);
		return result == null ? m_EmptySetOfStates : result;
	}
	
	@Override
	public Collection<STATE> predInternal(STATE state, LETTER letter) {
		assert contains(state);
		Map<LETTER, Set<STATE>> map = m_InternalIn.get(state);
		if (map == null) {
			return m_EmptySetOfStates;
		}
		Set<STATE> result = map.get(letter);
		return result == null ? m_EmptySetOfStates : result;
	}
	
	@Override
	public Collection<STATE> succCall(STATE state, LETTER letter) {
		assert contains(state);
		Map<LETTER, Set<STATE>> map = m_CallOut.get(state);
		if (map == null) {
			return m_EmptySetOfStates;
		}
		Set<STATE> result = map.get(letter);
		return result == null ? m_EmptySetOfStates : result;
	}
	
	@Override
	public Collection<STATE> predCall(STATE state, LETTER letter) {
		assert contains(state);
		Map<LETTER, Set<STATE>> map = m_CallIn.get(state);
		if (map == null) {
			return m_EmptySetOfStates;
		}
		Set<STATE> result = map.get(letter);
		return result == null ? m_EmptySetOfStates : result;
	}
	
	@Override
	public Collection<STATE> hierPred(STATE state, LETTER letter) {
		assert contains(state);
		Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut.get(state);
		if (map == null) {
			return m_EmptySetOfStates;
		}
		 Map<STATE, Set<STATE>> hier2succs = map.get(letter);
		return hier2succs == null ? m_EmptySetOfStates : hier2succs.keySet();
	}
	
	@Override
	public Collection<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		assert contains(state);
		assert contains(hier);
		Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut.get(state);
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
	public Collection<STATE> predReturnLin(STATE state, LETTER letter, STATE hier) {
		assert contains(state);
		assert contains(hier);
		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds  = m_ReturnIn.get(state);
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
	public Collection<STATE> predReturnHier(STATE state, LETTER letter) {
		assert contains(state);
		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds  = m_ReturnIn.get(state);
		if (letter2hier2preds == null) {
			return m_EmptySetOfStates;
		}
		Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		if (hier2preds == null) {
			return m_EmptySetOfStates;
		}
		return hier2preds.keySet();
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> 
						returnSummarySuccessor(LETTER letter, STATE hier) {
		Set<SummaryReturnTransition<LETTER, STATE>> result = 
				new HashSet<SummaryReturnTransition<LETTER, STATE>>();
		Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succ = 
				m_ReturnSummary.get(hier);
		if (letter2pred2succ == null) {
			return result;
		}
		Map<STATE, Set<STATE>> pred2succ = letter2pred2succ.get(letter);
		if (pred2succ == null) {
			return result;
		}
		for (STATE pred : pred2succ.keySet()) {
			if (pred2succ.get(pred) != null) {
				for (STATE succ : pred2succ.get(pred)) {
				SummaryReturnTransition<LETTER, STATE> srt = 
					new SummaryReturnTransition<LETTER, STATE>(pred, letter, succ);
				result.add(srt);
				}
			}
		}
		return result;
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(final STATE hier) {
		return new Iterable<SummaryReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all SummaryReturnTransition of hier.
			 */
			@Override
			public Iterator<SummaryReturnTransition<LETTER, STATE>> iterator() {
				Iterator<SummaryReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<SummaryReturnTransition<LETTER, STATE>>() {
					Iterator<LETTER> m_LetterIterator;
					LETTER m_CurrentLetter;
					Iterator<SummaryReturnTransition<LETTER, STATE>> m_CurrentIterator;
					{
						m_LetterIterator = lettersReturnSummary(hier).iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = returnSummarySuccessor(
										m_CurrentLetter, hier).iterator();
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
					public SummaryReturnTransition<LETTER, STATE> next() {
						if (m_CurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							SummaryReturnTransition<LETTER, STATE> result = 
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
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final LETTER letter, final STATE succ) {
		return new Iterable<IncomingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingInternalTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Set<STATE>> letter2pred = m_InternalIn.get(succ);
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
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final STATE succ) {
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
						m_LetterIterator = lettersInternalIncoming(succ).iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = internalPredecessors(
										m_CurrentLetter, succ).iterator();
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
			final LETTER letter, final STATE succ) {
		return new Iterable<IncomingCallTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingCallTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingCallTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingCallTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Set<STATE>> letter2pred = m_CallIn.get(succ);
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
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final STATE succ) {
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
						m_LetterIterator = lettersCallIncoming(succ).iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = callPredecessors(
										m_CurrentLetter, succ).iterator();
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
			final STATE hier, final LETTER letter, final STATE succ) {
		return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingReturnTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = m_ReturnIn.get(succ);
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
			final LETTER letter, final STATE succ) {
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
						m_HierIterator = predReturnHier(succ, letter).iterator();
						nextHier();
					}

					private void nextHier() {
						if (m_HierIterator.hasNext()) {
							do {
								m_CurrentHier = m_HierIterator.next();
								m_CurrentIterator = returnPredecessors(
										m_CurrentHier, letter, succ).iterator();
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
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ) {
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
						m_LetterIterator = lettersReturnIncoming(succ).iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = returnPredecessors(
										m_CurrentLetter, succ).iterator();
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
			final STATE state, final LETTER letter) {
		return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Set<STATE>> letter2succ = m_InternalOut.get(state);
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
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state) {
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
						m_LetterIterator = lettersInternal(state).iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = internalSuccessors(state,
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
			final STATE state, final LETTER letter) {
		return new Iterable<OutgoingCallTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingCallTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingCallTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Set<STATE>> letter2succ = m_CallOut.get(state);
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
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state) {
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
						m_LetterIterator = lettersCall(state).iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = callSuccessors(state,
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
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			final STATE state, final STATE hier, final LETTER letter) {
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succ = m_ReturnOut.get(state);
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
			final STATE state, final LETTER letter) {
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
						m_HierIterator = hierPred(state, letter).iterator();
						nextHier();
					}

					private void nextHier() {
						if (m_HierIterator.hasNext()) {
							do {
								m_CurrentHier = m_HierIterator.next();
								m_CurrentIterator = returnSucccessors(
										state, m_CurrentHier, letter).iterator();
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
			final STATE state, final STATE hier) {
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
						m_LetterIterator = lettersReturn(state).iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = returnSucccessors(
										state, hier, m_CurrentLetter).iterator();
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
			final STATE state) {
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
						m_LetterIterator = lettersReturn(state).iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = returnSuccessors(state,
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
	
	
	
	
	
	
	private boolean checkTransitionsReturnedConsistent() {
		boolean result = true;
		for (STATE state : getStates()) {
			for (IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(state)) {
				result &= containsInternalTransition(inTrans.getPred(), inTrans.getLetter(), state);
				assert result;
			}
			for (OutgoingInternalTransition<LETTER, STATE> outTrans : internalSuccessors(state)) {
				result &= containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert result;
			}
			for (IncomingCallTransition<LETTER, STATE> inTrans : callPredecessors(state)) {
				result &= containsCallTransition(inTrans.getPred(), inTrans.getLetter(), state);
				assert result;
			}
			for (OutgoingCallTransition<LETTER, STATE> outTrans : callSuccessors(state)) {
				result &= containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert result;
			}
			for (IncomingReturnTransition<LETTER, STATE> inTrans : returnPredecessors(state)) {
				result &= containsReturnTransition(inTrans.getLinPred(), inTrans.getHierPred(), inTrans.getLetter(), state);
				assert result;
			}
			for (OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state)) {
				result &= containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
				assert result;
			}
		}

		return result;
	}
	
	
	
	
	public boolean containsInternalTransition(STATE state, LETTER letter, STATE succ) {
		assert contains(state);
		Map<LETTER, Set<STATE>> map = m_InternalOut.get(state);
		if (map == null) {
			return false;
		}
		Set<STATE> result = map.get(letter);
		return result == null ? false : result.contains(succ);
	}
	
	public boolean containsCallTransition(STATE state, LETTER letter, STATE succ) {
		assert contains(state);
		Map<LETTER, Set<STATE>> map = m_CallOut.get(state);
		if (map == null) {
			return false;
		}
		Set<STATE> result = map.get(letter);
		return result == null ? false : result.contains(succ);
	}
	
	public boolean containsReturnTransition(STATE state, STATE hier, LETTER letter, STATE succ) {
		assert contains(state);
		assert contains(hier);
		Map<LETTER, Map<STATE, Set<STATE>>> map = m_ReturnOut.get(state);
		if (map == null) {
			return false;
		}
		Map<STATE, Set<STATE>> hier2succs = map.get(letter);
		if (hier2succs == null) {
			return false;
		}
		Set<STATE> result = hier2succs.get(hier);
		return result == null ? false : result.contains(succ);
	}
	
	


	
	public void makeStateNonIntial(STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		if (!m_InitialStates.contains(state)) {
			throw new AssertionError("Can only make initial state non-Initial");
		}
		m_InitialStates.remove(state);	
	}
	
	
	

	public void removeState(STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		m_FinalStates.remove(state);
		m_InitialStates.remove(state);
		
		for (LETTER letter : lettersCall(state)) {
			for (STATE succ : succCall(state, letter)) {
				removeCallIn(state, letter, succ);
			}
		}
		m_CallOut.remove(state);

		for (LETTER letter : lettersCallIncoming(state)) {
			for (STATE pred : predCall(state, letter)) {
				removeCallOut(pred, letter, state);
			}
		}
		m_CallIn.remove(state);
		
		for (LETTER letter : lettersReturn(state)) {
			for (STATE hier: hierPred(state,letter)) {
				for (STATE succ : succReturn(state, hier, letter)) {
					removeReturnIn(state, hier, letter, succ);
					removeReturnSummary(state, hier, letter, succ);
				}
			}
		}
		m_ReturnOut.remove(state);
		
		Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = m_ReturnSummary.get(state);
		if (letter2pred2succs != null)
		for (LETTER letter : m_ReturnSummary.get(state).keySet()) {
			Map<STATE, Set<STATE>> pred2succs = m_ReturnSummary.get(state).get(letter);
			if (pred2succs != null)
			for (STATE pred: pred2succs.keySet()) {
				Set<STATE> succs = pred2succs.get(pred);
				if (succs != null)
				for (STATE succ : succs) {
					removeReturnIn(pred, state, letter, succ);
					removeReturnOut(pred, state, letter, succ);
				}
			}
		}
		m_ReturnSummary.remove(state);
		
		for (LETTER letter : lettersReturnIncoming(state)) {
			Map<STATE, Set<STATE>> hier2pred = m_ReturnIn.get(state).get(letter);
			if (hier2pred != null) {
				for (STATE hier: hier2pred.keySet()) {
					for (STATE pred : predReturnLin(state, letter, hier)) {
						removeReturnOut(pred, hier, letter, state);
						removeReturnSummary(pred, hier, letter, state);
					}
				}
			}
		}
		m_ReturnIn.remove(state);
		
		for (LETTER letter : lettersInternalIncoming(state)) {
			for (STATE pred : predInternal(state, letter)) {
				removeInternalOut(pred, letter, state);
			}
		}
		m_InternalIn.remove(state);
		
		for (LETTER letter : lettersInternal(state)) {
			for (STATE succ : succInternal(state, letter)) {
				removeInternalIn(state, letter, succ);
			}
		}
		m_InternalOut.remove(state);

		// assert checkTransitionsStoredConsistent();
		assert checkTransitionsReturnedConsistent();
		assert sizeInformation() != "";
	}
	
	
	private void removeInternalIn(STATE pred, LETTER letter, STATE succ) {
		Map<LETTER, Set<STATE>> letter2preds = m_InternalIn.get(succ);
		Set<STATE> preds = letter2preds.get(letter);
		assert (preds.contains(pred));
		preds.remove(pred);
		if (preds.isEmpty()) {
			letter2preds.remove(letter);
			if (letter2preds.isEmpty()) {
				m_InternalIn.remove(succ);
			}
		}
	}
	
	private void removeInternalOut(STATE pred, LETTER letter, STATE succ) {
		Map<LETTER, Set<STATE>> letter2succs = m_InternalOut.get(pred);
		Set<STATE> succs = letter2succs.get(letter);
		assert (succs.contains(succ));
		succs.remove(succ);
		if (succs.isEmpty()) {
			letter2succs.remove(letter);
			if (letter2succs.isEmpty()) {
				//The keySet of m_InternalOut is used to store set of states of
				//this automaton. We don't remove succ, only set image to null.
				m_InternalOut.put(pred, null);
			}
		}
	}
	
	private void removeCallIn(STATE pred, LETTER letter, STATE succ) {
		Map<LETTER, Set<STATE>> letter2preds = m_CallIn.get(succ);
		Set<STATE> preds = letter2preds.get(letter);
		assert (preds.contains(pred));
		preds.remove(pred);
		if (preds.isEmpty()) {
			letter2preds.remove(letter);
			if (letter2preds.isEmpty()) {
				m_CallIn.remove(succ);
			}
		}
	}
	
	private void removeCallOut(STATE pred, LETTER letter, STATE succ) {
		Map<LETTER, Set<STATE>> letter2succs = m_CallOut.get(pred);
		Set<STATE> succs = letter2succs.get(letter);
		assert (succs.contains(succ));
		succs.remove(succ);
		if (succs.isEmpty()) {
			letter2succs.remove(letter);
			if (letter2succs.isEmpty()) {
				m_CallOut.remove(pred);
			}
		}
	}
	
	private void removeReturnIn(STATE pred, STATE hier, LETTER letter, STATE succ) {
		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds = m_ReturnIn.get(succ);
		Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		Set<STATE> preds = hier2preds.get(hier);
		assert (preds.contains(pred));
		preds.remove(pred);
		if (preds.isEmpty()) {
			hier2preds.remove(hier);
			if (hier2preds.isEmpty()) {
				letter2hier2preds.remove(letter);
				if (letter2hier2preds.isEmpty()) {
					m_ReturnIn.remove(succ);
				}
			}
		}
	}
	
	private void removeReturnOut(STATE pred, STATE hier, LETTER letter, STATE succ) {
		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succs = m_ReturnOut.get(pred);
		Map<STATE, Set<STATE>> hier2succs = letter2hier2succs.get(letter);
		Set<STATE> succs = hier2succs.get(hier);
		assert (succs.contains(succ));
		succs.remove(succ);
		if (succs.isEmpty()) {
			hier2succs.remove(hier);
			if (hier2succs.isEmpty()) {
				letter2hier2succs.remove(letter);
				if (letter2hier2succs.isEmpty()) {
					m_ReturnOut.remove(pred);
				}
			}
		}
	}
	
	private void removeReturnSummary(STATE pred, STATE hier, LETTER letter, STATE succ) {
		Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = m_ReturnSummary.get(hier);
		Map<STATE, Set<STATE>> pred2succs = letter2pred2succs.get(letter);
		Set<STATE> succs = pred2succs.get(pred);
		assert (succs.contains(succ));
		succs.remove(succ);
		if (succs.isEmpty()) {
			pred2succs.remove(pred);
			if (pred2succs.isEmpty()) {
				letter2pred2succs.remove(letter);
				if (letter2pred2succs.isEmpty()) {
					m_ReturnSummary.remove(hier);
				}
			}
		}
	}
	
	
	
	
	private boolean checkTransitionsStoredConsistent() {
		boolean result = true;
		for (STATE pred : m_InternalOut.keySet()) {
			Map<LETTER, Set<STATE>> letter2succs = m_InternalOut.get(pred);
			if (letter2succs == null) {
				// may be null because the keySet is used to store the set of
				// all states, but some state my not have an outgoing internal
				// transition
				continue;
			}
			assert !letter2succs.isEmpty();
			for (LETTER letter : letter2succs.keySet()) {
				Set<STATE> succs = letter2succs.get(letter);
				assert !succs.isEmpty();
				for (STATE succ : succs) {
					assert (m_InternalIn.get(succ).get(letter).contains(pred));
					if (!m_InternalIn.get(succ).get(letter).contains(pred)) {
						result = false;
					}
				}
			}
		}
		for (STATE succ : m_InternalIn.keySet()) {
			Map<LETTER, Set<STATE>> letter2preds = m_InternalIn.get(succ);
			assert !letter2preds.isEmpty();
			for (LETTER letter : letter2preds.keySet()) {
				Set<STATE> preds = letter2preds.get(letter);
				assert !preds.isEmpty();
				for (STATE pred : preds) {
					assert (m_InternalOut.get(pred).get(letter).contains(succ));
					if (!m_InternalOut.get(pred).get(letter).contains(succ)) {
						result = false;
					}
				}
			}
		}
		for (STATE pred : m_CallOut.keySet()) {
			Map<LETTER, Set<STATE>> letter2succs = m_CallOut.get(pred);
			assert !letter2succs.isEmpty();
			for (LETTER letter : letter2succs.keySet()) {
				Set<STATE> succs = letter2succs.get(letter);
				assert !succs.isEmpty();
				for (STATE succ : succs) {
					assert (m_CallIn.get(succ).get(letter).contains(pred));
					if (!m_CallIn.get(succ).get(letter).contains(pred)) {
						result = false;
					}
				}
			}
		}
		for (STATE succ : m_CallIn.keySet()) {
			Map<LETTER, Set<STATE>> letter2preds = m_CallIn.get(succ);
			assert !letter2preds.isEmpty();
			for (LETTER letter : letter2preds.keySet()) {
				Set<STATE> preds = letter2preds.get(letter);
				assert !preds.isEmpty();
				for (STATE pred : preds) {
					assert (m_CallOut.get(pred).get(letter).contains(succ));
					if (!m_CallOut.get(pred).get(letter).contains(succ)) {
						result = false;
					}
				}
			}
		}	
		for (STATE pred : m_ReturnOut.keySet()) {
			Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succs = m_ReturnOut.get(pred);
			assert !letter2hier2succs.isEmpty();
			for (LETTER letter : letter2hier2succs.keySet()) {
				Map<STATE, Set<STATE>> hier2succs = letter2hier2succs.get(letter);
				assert !hier2succs.isEmpty();
				for (STATE hier : hier2succs.keySet()) {
					Set<STATE> succs = hier2succs.get(hier);
					assert !succs.isEmpty();
					for (STATE succ : succs) {
						assert m_ReturnIn.get(succ).get(letter).get(hier).contains(pred);
						assert m_ReturnSummary.get(hier).get(letter).get(pred).contains(succ);
						if (!m_ReturnIn.get(succ).get(letter).get(hier).contains(pred)) {
							result = false;
						}
						if (!m_ReturnSummary.get(hier).get(letter).get(pred).contains(succ)) {
							result = false;
						}
					}
				}
			}
		}
		for (STATE succ : m_ReturnIn.keySet()) {
			Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = m_ReturnIn.get(succ);
			assert !letter2hier2pred.isEmpty();
			for (LETTER letter : letter2hier2pred.keySet()) {
				Map<STATE, Set<STATE>> hier2preds = letter2hier2pred.get(letter);
				assert !hier2preds.isEmpty();
				for (STATE hier : hier2preds.keySet()) {
					Set<STATE> preds = hier2preds.get(hier);
					assert !preds.isEmpty();
					for (STATE pred : preds) {
						assert m_ReturnOut.get(pred).get(letter).get(hier).contains(succ);
						assert m_ReturnSummary.get(hier).get(letter).get(pred).contains(succ);
						if (!m_ReturnOut.get(pred).get(letter).get(hier).contains(succ)) {
							result = false;
						}
						if (!m_ReturnSummary.get(hier).get(letter).get(pred).contains(succ)) {
							result = false;
						}
					}
				}
			}
		}
		for (STATE hier : m_ReturnSummary.keySet()) {
			Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = m_ReturnSummary.get(hier);
			assert !letter2pred2succs.isEmpty();
			for (LETTER letter : letter2pred2succs.keySet()) {
				Map<STATE, Set<STATE>> pred2succs = letter2pred2succs.get(letter);
				assert !pred2succs.isEmpty();
				for (STATE pred : pred2succs.keySet()) {
					Set<STATE> succs = pred2succs.get(pred);
					assert !succs.isEmpty();
					for (STATE succ : succs) {
						assert m_ReturnOut.get(pred).get(letter).get(hier).contains(succ);
						assert m_ReturnIn.get(succ).get(letter).get(hier).contains(pred);
						if (!m_ReturnOut.get(pred).get(letter).get(hier).contains(succ)) {
							result = false;
						}
						if (!m_ReturnIn.get(succ).get(letter).get(hier).contains(pred)) {
							result = false;
						}
					}
				}
			}
		}
		return result;
	}
	
	private int numberIncomingInternalTransitions(STATE state) {
		int result = 0;
		for (IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(state)) {
			result++;
		}
		return result;
	}
	
	private int numberIncomingCallTransitions(STATE state) {
		int result = 0;
		for (IncomingCallTransition<LETTER, STATE> inTrans : callPredecessors(state)) {
			result++;
		}
		return result;
	}
	
	private int numberIncomingReturnTransitions(STATE state) {
		int result = 0;
		for (IncomingReturnTransition<LETTER, STATE> inTrans : returnPredecessors(state)) {
			result++;
		}
		return result;
	}
	
	
	@Override
	public String sizeInformation() {
		boolean verbose = false;
		if (!verbose) {
			int states = m_InternalOut.size();
			return states + " states.";
		}
		int statesWithInternalSuccessors = 0;
		int internalSuccessors = 0;
		for (STATE pred : m_InternalOut.keySet()) {
			Map<LETTER, Set<STATE>> letter2succs = m_InternalOut.get(pred);
			if (letter2succs == null) {
				// may be null because the keySet is used to store the set of
				// all states, but some state my not have an outgoing internal
				// transition
				continue;
			}
			statesWithInternalSuccessors++;
			for (LETTER letter : letter2succs.keySet()) {
				Set<STATE> succs = letter2succs.get(letter);
				internalSuccessors += succs.size();
			}
		}
		int statesWithInternalPredecessors = 0;
		int internalPredecessors = 0;
		for (STATE succ : m_InternalIn.keySet()) {
			int internalPredOfSucc = 0;
			statesWithInternalPredecessors++;
			Map<LETTER, Set<STATE>> letter2preds = m_InternalIn.get(succ);
			for (LETTER letter : letter2preds.keySet()) {
				Set<STATE> preds = letter2preds.get(letter);
				internalPredOfSucc += preds.size();
			}
			assert (internalPredOfSucc == numberIncomingInternalTransitions(succ));
			internalPredecessors += internalPredOfSucc;
		}
		int statesWithCallSuccessors = 0;
		int callSuccessors = 0;		
		for (STATE pred : m_CallOut.keySet()) {
			statesWithCallSuccessors++;
			Map<LETTER, Set<STATE>> letter2succs = m_CallOut.get(pred);
			for (LETTER letter : letter2succs.keySet()) {
				Set<STATE> succs = letter2succs.get(letter);
				callSuccessors += succs.size();
			}
		}
		int statesWithCallPredecessors = 0;
		int callPredecessors = 0;		
		for (STATE succ : m_CallIn.keySet()) {
			statesWithCallPredecessors++;
			int callPredOfSucc = 0;
			Map<LETTER, Set<STATE>> letter2preds = m_CallIn.get(succ);
			for (LETTER letter : letter2preds.keySet()) {
				Set<STATE> preds = letter2preds.get(letter);
				callPredOfSucc += preds.size();
			}
			assert (callPredOfSucc == numberIncomingCallTransitions(succ));
			callPredecessors += callPredOfSucc;

		}
		int statesWithReturnSuccessor = 0;
		int returnSuccessors = 0;
		for (STATE pred : m_ReturnOut.keySet()) {
			statesWithReturnSuccessor++;
			Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succs = m_ReturnOut.get(pred);
			for (LETTER letter : letter2hier2succs.keySet()) {
				Map<STATE, Set<STATE>> hier2succs = letter2hier2succs.get(letter);
				for (STATE hier : hier2succs.keySet()) {
					Set<STATE> succs = hier2succs.get(hier);
					returnSuccessors += succs.size();
				}
			}
		}
		int statesWithReturnLinearPredecessors = 0;
		int returnLinearPredecessors = 0;
		for (STATE succ : m_ReturnIn.keySet()) {
			Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = m_ReturnIn.get(succ);
			statesWithReturnLinearPredecessors++;
			int returnLinPredOfSucc = 0;
			for (LETTER letter : letter2hier2pred.keySet()) {
				Map<STATE, Set<STATE>> hier2preds = letter2hier2pred.get(letter);
				for (STATE hier : hier2preds.keySet()) {
					Set<STATE> preds = hier2preds.get(hier);
					returnLinPredOfSucc += preds.size();
				}
			}
			assert (returnLinPredOfSucc == numberIncomingReturnTransitions(succ));
			returnLinearPredecessors += returnLinPredOfSucc;
		}
		int statesWithReturnHierarchicalSuccessor = 0;
		int returnHierarchicalSuccessors = 0;
		for (STATE hier : m_ReturnSummary.keySet()) {
			Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = m_ReturnSummary.get(hier);
			statesWithReturnHierarchicalSuccessor++;
			for (LETTER letter : letter2pred2succs.keySet()) {
				Map<STATE, Set<STATE>> pred2succs = letter2pred2succs.get(letter);
				for (STATE pred : pred2succs.keySet()) {
					Set<STATE> succs = pred2succs.get(pred);
					returnHierarchicalSuccessors += succs.size();
				}
			}
		}
		StringBuilder sb = new StringBuilder();
		sb.append(" has ").append(m_InternalOut.size()).append(" states, " +
				statesWithInternalSuccessors).append( " states have internal successors, (").append(internalSuccessors).append("), ").append(
				statesWithInternalPredecessors).append(" states have internal predecessors, (").append(internalPredecessors).append("), ").append(
				
				statesWithCallSuccessors).append(" states have call successors, (").append(callSuccessors).append("), ").append(
				statesWithCallPredecessors).append(" states have call predecessors, (").append(callPredecessors).append("), ").append(
				
				statesWithReturnSuccessor).append(" states have return successors, (").append(returnSuccessors).append("), ").append(
				statesWithReturnLinearPredecessors).append(" states have call predecessors, (").append(returnLinearPredecessors).append("), " +
				statesWithReturnHierarchicalSuccessor).append(" states have call successors, (").append(returnHierarchicalSuccessors).append(")");
		return sb.toString();
		
//		return " has " + m_InternalOut.size() + " states, " +
//		statesWithInternalSuccessors + " states have internal successors, (" + internalSuccessors + "), " +
//		statesWithInternalPredecessors + " states have internal predecessors, (" + internalPredecessors + "), " +
//		
//		statesWithCallSuccessors + " states have call successors, (" + callSuccessors + "), " +
//		statesWithCallPredecessors + " states have call predecessors, (" + callPredecessors + "), " +
//		
//		statesWithReturnSuccessor + " states have return successors, (" + returnSuccessors + "), " +
//		statesWithReturnLinearPredecessors + " states have call predecessors, (" + returnLinearPredecessors + "), " +
//		statesWithReturnHierarchicalSuccessor + " states have call successors, (" + returnHierarchicalSuccessors + ")";
	}

	
	public void addInternalTransition(STATE pred, LETTER letter, STATE succ) {
		if (!contains(pred)) {
			throw new IllegalArgumentException();
		}
		assert contains(pred);
		assert contains(succ);
		Map<LETTER, Set<STATE>> letter2succs = m_InternalOut.get(pred);
		if (letter2succs == null) {
			letter2succs = new HashMap<LETTER, Set<STATE>>();
			m_InternalOut.put(pred, letter2succs);
		}
		Set<STATE> succs = letter2succs.get(letter);
		if (succs == null) {
			succs = new HashSet<STATE>();
			letter2succs.put(letter,succs);
		}
		succs.add(succ);
		
		Map<LETTER, Set<STATE>> letter2preds = m_InternalIn.get(succ);
		if (letter2preds == null) {
			letter2preds = new HashMap<LETTER, Set<STATE>>();
			m_InternalIn.put(succ, letter2preds);
		}
		Set<STATE> preds = letter2preds.get(letter);
		if (preds == null) {
			preds = new HashSet<STATE>();
			letter2preds.put(letter,preds);
		}
		preds.add(pred);
		// assert checkTransitionsStoredConsistent();
	}
	

	public void addCallTransition(STATE pred, LETTER letter, STATE succ) {
		assert contains(pred);
		assert contains(succ);
		Map<LETTER, Set<STATE>> letter2succs = m_CallOut.get(pred);
		if (letter2succs == null) {
			letter2succs = new HashMap<LETTER, Set<STATE>>();
			m_CallOut.put(pred, letter2succs);
		}
		Set<STATE> succs = letter2succs.get(letter);
		if (succs == null) {
			succs = new HashSet<STATE>();
			letter2succs.put(letter,succs);
		}
		succs.add(succ);
		
		Map<LETTER, Set<STATE>> letter2preds = m_CallIn.get(succ);
		if (letter2preds == null) {
			letter2preds = new HashMap<LETTER, Set<STATE>>();
			m_CallIn.put(succ, letter2preds);
		}
		Set<STATE> preds = letter2preds.get(letter);
		if (preds == null) {
			preds = new HashSet<STATE>();
			letter2preds.put(letter,preds);
		}
		preds.add(pred);
		// assert checkTransitionsStoredConsistent();
	}
	

	public void addReturnTransition(STATE pred, STATE hier, LETTER letter, STATE succ) {
		assert contains(pred);
		assert contains(hier);
		assert contains(succ);
		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succs = m_ReturnOut.get(pred);
		if (letter2hier2succs == null) {
			letter2hier2succs = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
			m_ReturnOut.put(pred, letter2hier2succs);
		}
		Map<STATE, Set<STATE>> hier2succs = letter2hier2succs.get(letter);
		if (hier2succs == null) {
			hier2succs = new HashMap<STATE, Set<STATE>>();
			letter2hier2succs.put(letter, hier2succs);
		}
		Set<STATE> succs = hier2succs.get(hier);
		if (succs == null) {
			succs = new HashSet<STATE>();
			hier2succs.put(hier, succs);
		}
		succs.add(succ);
		
		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds = m_ReturnIn.get(succ);
		if (letter2hier2preds == null) {
			letter2hier2preds = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
			m_ReturnIn.put(succ, letter2hier2preds);
		}
		Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		if (hier2preds == null) {
			hier2preds = new HashMap<STATE, Set<STATE>>();
			letter2hier2preds.put(letter, hier2preds);
		}
		Set<STATE> preds = hier2preds.get(hier);
		if (preds == null) {
			preds = new HashSet<STATE>();
			hier2preds.put(hier, preds);
		}
		preds.add(pred);
		
		Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = m_ReturnSummary.get(hier);
		if (letter2pred2succs == null) {
			letter2pred2succs = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
			m_ReturnSummary.put(hier, letter2pred2succs);
		}
		Map<STATE, Set<STATE>> pred2succs = letter2pred2succs.get(letter);
		if (pred2succs == null) {
			pred2succs = new HashMap<STATE, Set<STATE>>();
			letter2pred2succs.put(letter, pred2succs);
		}
		Set<STATE> succS = pred2succs.get(pred);
		if (succS == null) {
			succS = new HashSet<STATE>();
			pred2succs.put(pred, succS);
		}
		succS.add(succ);
		// assert checkTransitionsStoredConsistent();
	}
	
	
	
	
	
	
	
	

	

	
	public NestedWordAutomaton(Set<LETTER> internalAlphabet,
				Set<LETTER> callAlphabet,
				Set<LETTER> returnAlphabet,
			   StateFactory<STATE> stateFactory) {
		if (internalAlphabet == null) {
			throw new IllegalArgumentException("nwa must have internal alphabet");
		}
		if (stateFactory == null) {
			throw new IllegalArgumentException("nwa must have stateFactory");
		}
		this.m_InternalAlphabet = internalAlphabet;
		this.m_CallAlphabet = callAlphabet;
		this.m_ReturnAlphabet = returnAlphabet;
		this.m_StateFactory = stateFactory;
		this.emptyStackState = m_StateFactory.createEmptyStackState();
	}
	
	
//	@Deprecated
//	public NestedWordAutomaton(INestedWordAutomaton<LETTER,STATE> nwa,
//								boolean totalize,
//								boolean complement) {
//		if (totalize && nwa.isTotal()) {
//			throw new IllegalArgumentException(
//				"Automaton is already total");
//		}
//		if (totalize && !nwa.isDeterministic()) {
//			throw new IllegalArgumentException(
//					"I only totalize deterministic NWAs");
//		}
//		if (complement && !(totalize || nwa.isTotal()) ) {
//			throw new IllegalArgumentException(
//							"I only complement total NWAs");
//		}
//		this.m_InternalAlphabet = new HashSet<LETTER>();
//		this.m_InternalAlphabet.addAll(nwa.getInternalAlphabet());
//		this.m_CallAlphabet = new HashSet<LETTER>();
//		this.m_CallAlphabet.addAll(nwa.getCallAlphabet());
//		this.m_ReturnAlphabet = new HashSet<LETTER>();
//		this.m_ReturnAlphabet.addAll(nwa.getReturnAlphabet());
//		this.m_contentFactory = nwa.getStateFactory();
//		
//		this.states = new HashSet<IAuxiliaryStateContainer<LETTER,STATE>>();
//		this.initialStates = new HashSet<IAuxiliaryStateContainer<LETTER,STATE>>();
//		this.finalStates = new HashSet<IAuxiliaryStateContainer<LETTER,STATE>>();
//		
//		this.emptyStackContent = m_contentFactory.createEmptyStackContent();
//		this.emptyStackState = new AuxiliaryStateContainer<LETTER,STATE>(false,
//				this.emptyStackContent, m_ConstructedStates++);
//		assert(isFinalStoredConsistent((NestedWordAutomaton<LETTER, STATE>) nwa));
//		
//	
//		
//		for (STATE state : nwa.states()) {
//			boolean isInitial = nwa.getInitial().contains(state);
//			boolean isFinal;
//			if (complement) {
//				isFinal = !nwa.isFinal(state);
//			}
//			else {
//				isFinal = nwa.isFinal(state);
//			}
//			this.addContent(isInitial, isFinal, state);
//		}
//		STATE sink = m_contentFactory.createSinkStateContent();
//		//don't add sink state if automaton is already total
//		if (totalize) {
//			// sinkState is initial if automaton does not have initial states
//			boolean isInitial = this.initialStates.isEmpty();
//			this.addContent(isInitial, complement, sink);
//		}
//		
//		for (STATE state : this.states()) {
//			
//			for (LETTER symbol : this.getInternalAlphabet()) {
//				if (state == sink) {
//					this.addInternalTransition(state, symbol, sink);
//				}
//				else {
//					Collection<STATE> succs = nwa.succInternal(state, symbol);
//					assert (!totalize || succs.size() <= 1);
//					for (STATE succ : succs) {
//						this.addInternalTransition(state, symbol, succ);
//					}
//					if (totalize && succs.isEmpty()) {
//						this.addInternalTransition(state, symbol, sink);
//					}
//				}
//			}
//			
//			for (LETTER symbol : this.getCallAlphabet()) {
//				if (state == sink) {
//					this.addCallTransition(state, symbol, sink);
//				}
//				else {
//					Collection<STATE> succs = nwa.succCall(state, symbol);
//					assert (!totalize || succs.size() <= 1);
//					for (STATE succ : succs) {
//						this.addCallTransition(state, symbol, succ);
//					}
//					if (totalize && succs.isEmpty()) {
//						this.addCallTransition(state, symbol, sink);
//					}
//				}
//			}
//			
//			for (LETTER symbol : this.getReturnAlphabet()) {
//				for (STATE hier : this.states()) {
//					if (state == sink) {
//						this.addReturnTransition(state, hier, symbol, sink);
//					}
//					else if (hier == sink) {
//						this.addReturnTransition(state, hier, symbol, sink);
//					}
//					else {
//						Collection<STATE> succs = nwa.succReturn(state, hier, symbol);
//						assert (!totalize || succs.size() <= 1);
//						for (STATE succ : succs) {
//							this.addReturnTransition(state, hier, symbol, succ);
//						}
//						if (totalize && succs.isEmpty()) {
//							this.addReturnTransition(state, hier, symbol, sink);
//						}
//					}
//				}
//			}
//			
//		}
//	}
	
	


	

	




	/**
	 * Return true iff this automaton is deterministic.
	 */
	@Override
	public boolean isDeterministic() {
		if(getInitialStates().size() > 1) {
			return false;
		}
		for (STATE state : this.getStates()) {
			for (LETTER symbol : lettersInternal(state)) {
				if (succInternal(state, symbol).size() > 1) {
					return false;
				}
			}
			for (LETTER symbol : lettersCall(state)) {
				if (succCall(state, symbol).size() > 1) {
					return false;
				}
			}
			for (LETTER symbol : lettersReturn(state)) {
				for (STATE hier : hierPred(state, symbol)) {
					if (succReturn(state, hier, symbol).size() > 1) {
						return false;
					}
				}
			}
		}
		return true;
	}

	/**
	 * Return true iff this automaton is total.
	 */
	@Override
	public boolean isTotal() {
		if(getInitialStates().size() < 1) {
			return false;
		}
		for (STATE state : this.getStates()) {
			for (LETTER symbol : getInternalAlphabet()) {
				if (succInternal(state, symbol).size() < 1) {
					return false;
				}
			}
			for (LETTER symbol : getCallAlphabet()) {
				if (succCall(state, symbol).size() < 1) {
					return false;
				}
			}
			for (LETTER symbol : getReturnAlphabet()) {
				for (STATE hier : getStates()) {
					if (succReturn(state, hier, symbol).size() < 1) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	
	
	
	@Override
	public boolean accepts(Word<LETTER> word) {
		
		NestedWord<LETTER> nw = NestedWord.nestedWord(word);
		try {
			return (new Accepts<LETTER, STATE>(this, nw, false, false)).getResult();
		} catch (OperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			throw new AssertionError();
		}

	}
	
	


	
	
	

	
	
	@Deprecated
	public NestedRun<LETTER,STATE> getAcceptingNestedRun() throws OperationCanceledException {
		NestedRun<LETTER,STATE> result = (new IsEmpty<LETTER,STATE>(this).getNestedRun());
		return result;
	}
	
	
	/**
	 * maximize set of accepting states
	 */
	public void buchiClosure() {
		s_Logger.info("Accepting states before buchiClosure: " + getFinalStates().size());
		Set<STATE> worklist = new HashSet<STATE>();
		worklist.addAll(getFinalStates());
		while (!worklist.isEmpty()) {
			STATE state = worklist.iterator().next();
			worklist.remove(state);
			if (!getFinalStates().contains(state)) {
				if (allSuccessorsAccepting(state)) {
					makeStateAccepting(state);
				}
				else {
					continue;
				}
			}
			for (LETTER symbol : lettersInternalIncoming(state)) {
				for (STATE succ : predInternal(state, symbol)) {
					if (!getFinalStates().contains(succ)) {
						worklist.add(succ);
					}
				}
			}
			for (LETTER symbol : lettersCall(state)) {
				for (STATE succ : succCall(state, symbol)) {
					if (!getFinalStates().contains(succ)) {
						worklist.add(succ);
					}
				}
			}
			for (LETTER symbol : lettersReturn(state)) {
				for (STATE hier : hierPred(state, symbol)) {
					for (STATE succ : succReturn(state, hier, symbol)) {
						if (!getFinalStates().contains(succ)) {
							worklist.add(succ);
						}
					}
				}
			}
		}
		s_Logger.info("Accepting states after buchiClosure: " + getFinalStates().size());
	}
	
	/**
	 * Return true iff all successors of state state are accepting states.
	 */
	private boolean allSuccessorsAccepting(STATE state) {
		for (LETTER symbol : lettersInternal(state)) {
			for (STATE succ : succInternal(state, symbol)) {
				if (!getFinalStates().contains(succ)) {
					return false;
				}
			}
		}
		for (LETTER symbol : lettersCall(state)) {
			for (STATE succ : succCall(state, symbol)) {
				if (!getFinalStates().contains(succ)) {
					return false;
				}
			}
		}
		for (LETTER symbol : lettersReturn(state)) {
			for (STATE hier : hierPred(state, symbol)) {
				for (STATE succ : succReturn(state, hier, symbol)) {
					if (!getFinalStates().contains(succ)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	
	/**
	 * Change status of state from non-accepting to accepting
	 */
	private void makeStateAccepting(STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		if (isFinal(state)) {
			throw new IllegalArgumentException("state " + state + " already final");
		}
		m_FinalStates.add(state);
	}
	
	

	
	
	

	
	public INestedWordAutomatonOldApi<LETTER,STATE> concurrentProduct(
											INestedWordAutomatonOldApi<LETTER,STATE> nwa) {
		return (new ConcurrentProduct<LETTER,STATE>(this, nwa, false)).getResult();
	}

	
	public INestedWordAutomatonOldApi<LETTER,STATE> concurrentPrefixProduct(
			INestedWordAutomatonOldApi<LETTER,STATE> nwa) {
		return (new ConcurrentProduct<LETTER,STATE>(this, nwa, true)).getResult();
	}
	
	
	
	
	
	

	
	
	
	
	/**
	 * @return true iff the language of this automaton is closed under
	 * concatenation with sigma star.
	 */
	@Deprecated
	public boolean finalIsTrap() {
		if (!this.getCallAlphabet().isEmpty()) {
			throw new UnsupportedOperationException(
											"only finite automata supported");
		}
		if (!this.getReturnAlphabet().isEmpty()) {
			throw new UnsupportedOperationException(
											"only finite automata supported");
		}

		for (STATE finalState : m_FinalStates) {
			for (LETTER symbol : this.getInternalAlphabet()) {
				Collection<STATE> succs = succInternal(finalState, symbol) ;
				if (succs.isEmpty()) {
					return false;
				}
				for (STATE succ : succs) {
					if (!isFinal(succ)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	
	
	public int numberOfOutgoingInternalTransitions(STATE state) {
		int result = 0;
		for (LETTER letter : lettersInternal(state)) {
			for (STATE succ : succInternal(state, letter)) {
				result++;
			}
		}
		return result;
	}
	
	
	public int numberOfIncomingInternalTransitions(STATE state) {
		int result = 0;
		for (LETTER letter : lettersInternalIncoming(state)) {
			for (STATE pred : predInternal(state, letter)) {
				result++;
			}
		}
		return result;
	}
	
	public static <LETTER, STATE> boolean sameAlphabet(
			INestedWordAutomatonSimple<LETTER, STATE> nwa1, 
			INestedWordAutomatonSimple<LETTER, STATE> nwa2) {
		boolean result = true;
		Collection<LETTER> in1 = nwa1.getInternalAlphabet();
		Collection<LETTER> in2 = nwa2.getInternalAlphabet();
		result &= in1.equals(in2);
		result &= nwa1.getInternalAlphabet().equals(nwa2.getInternalAlphabet());
		result &= nwa1.getCallAlphabet().equals(nwa2.getCallAlphabet());
		result &= nwa1.getReturnAlphabet().equals(nwa2.getReturnAlphabet());
		return result;
	}
	
	
//	public InternalTransitions getInternalTransitions(IAuxiliaryStateContainer<LETTER,STATE> state, LETTER symbol) {
//		return new InternalTransitions(state, symbol);
//	}
//	
//	public InternalTransitions getInternalTransitions(IAuxiliaryStateContainer<LETTER,STATE> state) {
//		return new InternalTransitions(state);
//	}
//	
//	public InternalTransitions getInternalTransitions() {
//		return new InternalTransitions();
//	}
//
//
//	public class InternalTransition {
//		private final IAuxiliaryStateContainer<LETTER,STATE> predecessor;
//		private final LETTER symbol;
//		private final IAuxiliaryStateContainer<LETTER,STATE> successor;
//
//		public InternalTransition(IAuxiliaryStateContainer<LETTER,STATE> predecessor, 
//								  LETTER symbol,
//								  IAuxiliaryStateContainer<LETTER,STATE> successor) {
//			this.predecessor = predecessor;
//			this.symbol = symbol;
//			this.successor = successor;
//		}
//		
//		public IAuxiliaryStateContainer<LETTER,STATE> getPredecessor() {
//			return predecessor;
//		}
//		
//		public LETTER getSymbol() {
//			return symbol;
//		}
//		
//		public IAuxiliaryStateContainer<LETTER,STATE> getSuccessor() {
//			return successor;
//		}
//		
//		public String toString() {
//			return "( " + predecessor + " , " + symbol + " , " + 
//															successor + " )";
//		}
//	}
	
//	public class InternalTransitions implements Iterable<InternalTransition> {
//		private final boolean fixedPredecessor;
//		private IAuxiliaryStateContainer<LETTER,STATE> predecessor;
//		private final boolean fixedSymbol;
//		private LETTER symbol;
//		
//		public InternalTransitions(IAuxiliaryStateContainer<LETTER,STATE> state, LETTER symbol) {
//			fixedPredecessor = true;
//			this.predecessor = state;
//			fixedSymbol = true;
//			this.symbol = symbol;
//		}
//		
//		public InternalTransitions(IAuxiliaryStateContainer<LETTER,STATE> state) {
//			fixedPredecessor = true;
//			this.predecessor = state;
//			fixedSymbol = false;
//		}
//		
//		public InternalTransitions() {
//			fixedPredecessor = false;
//			fixedSymbol = false;
//		}
//		
//
//		@Override
//		public Iterator<InternalTransition> iterator() {
//			return new InternalTransitionIterator();
//		}
//		
//		public class InternalTransitionIterator implements Iterator<InternalTransition> {
//			
//			public Iterator<IAuxiliaryStateContainer<LETTER, STATE>> predIterator;
//			private Iterator<LETTER> symbolIterator;
//			private Iterator<IAuxiliaryStateContainer<LETTER,STATE>> succIterator;
//			
//			private boolean finished = false;
//			
//
//
//			public InternalTransitionIterator() {
//				if (fixedSymbol) {
//					assert (fixedPredecessor);
//					predIterator = null;
//					symbolIterator = null;
//					succIterator = predecessor.getInternalSucc(symbol).iterator();
//					assert (succIterator != null);
//				}
//				else {
//					if (fixedPredecessor) {
//						predIterator = null;
//						symbolIterator = predecessor.getSymbolsInternal().iterator();
//						assert (symbolIterator != null);
//						updateSuccIterator();
//						while (!finished && !succIterator.hasNext()) {
//							updateSymbolIterator();
//						}
//					}
//					else {
//						predIterator = getAllStates().iterator();
//						updateSymbolIterator();
//						updateSuccIterator();
//						while (!finished && !succIterator.hasNext()) {
//							updateSymbolIterator();
//						}
//					}
//				}
//			}
//			
//			
//			
//			private void updateSuccIterator(){
//				if (fixedSymbol) {
//					this.finished = true;
//					return;
//				}
//				else {
//					while (!finished && !symbolIterator.hasNext() ) {
//						updateSymbolIterator();
//					}	
//					if (this.finished) {
//						return;
//					}
//					else {
//						assert (symbolIterator.hasNext());
//						symbol = symbolIterator.next();
//						succIterator = predecessor.getInternalSucc(symbol).iterator();
//					}
//				}
//			}
//				
//			private void updateSymbolIterator() {
//				if (fixedPredecessor) {
//					this.finished = true;
//					return;
//				}
//				else {
//					if (predIterator.hasNext()) {
//						predecessor = predIterator.next();
//						symbolIterator = predecessor.getSymbolsInternal().iterator();
//					}
//					else {
//						this.finished = true;
//					}
//				}
//			}
//
//			@Override
//			public boolean hasNext() {
//				if (finished) {
//					return false;
//				}
//				else {
//					return succIterator.hasNext();
//				}
//				
//			}
//
//			@Override
//			public InternalTransition next() {
//				IAuxiliaryStateContainer<LETTER,STATE> succ = succIterator.next();
//				InternalTransition result = 
//					new InternalTransition(predecessor, symbol, succ);
//				while (!finished && !succIterator.hasNext()) {
//					updateSuccIterator();
//				}
//				return result; 
//			}
//
//			@Override
//			public void remove() {
//				throw new UnsupportedOperationException();
//			}
//			
//		}
//		
//	}

	
	@Override
	public String toString() {
		return (new AtsDefinitionPrinter<String,String>("nwa", this)).getDefinitionAsString();
	}




	
}
