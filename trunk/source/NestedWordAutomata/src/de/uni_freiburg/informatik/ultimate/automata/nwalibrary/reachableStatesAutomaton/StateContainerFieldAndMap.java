package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;

/**
 * Contains STATES and information of transitions.
 *
 * @param <LETTER>
 * @param <STATE>
 */
class StateContainerFieldAndMap<LETTER,STATE> extends StateContainer<LETTER, STATE> {

	private Set<LETTER> m_EmptySetOfLetters = new HashSet<LETTER>(0);
	private Collection<STATE> m_EmptySetOfStates = new HashSet<STATE>(0);
	
	private Object mOut1;
	private Object mOut2;
	private Object mOut3;
	private Object mIn1;
	private Object mIn2;
	private Object mIn3;

	StateContainerFieldAndMap(STATE state, CommonEntriesComponent<LETTER,STATE> cec) {
		super(state,cec);
	}


	boolean mapModeOutgoing() {
		return (mOut1 instanceof Map) ||(mOut2 instanceof Map) || (mOut3 instanceof Map); 
	}
	
	boolean mapModeIncoming() {
		return (mIn1 instanceof Map) ||(mIn2 instanceof Map) || (mIn3 instanceof Map); 
	}
	
	
	private void switchOutgoingToMapMode() {
		assert(!mapModeOutgoing());
		List<Object> transitions = new ArrayList<Object>(3);
		if (mOut1 != null) {
			transitions.add(mOut1);
			mOut1 = null;
		}
		if (mOut2 != null) {
			transitions.add(mOut2);
			mOut2 = null;
		}
		if (mOut3 != null) {
			transitions.add(mOut3);
			mOut3 = null;
		}
		for (Object trans : transitions) {
			if (trans instanceof OutgoingInternalTransition) {
				addInternalOutgoingMap((OutgoingInternalTransition<LETTER, STATE>) trans);
			} else if (trans instanceof OutgoingCallTransition) {
				addCallOutgoingMap((OutgoingCallTransition<LETTER, STATE>) trans);
			} else if (trans instanceof OutgoingReturnTransition) {
				addReturnOutgoingMap((OutgoingReturnTransition<LETTER, STATE>) trans);
			} else {
				throw new AssertionError();
			}
		}
		assert (mapModeOutgoing());
	}
	
	private void switchIncomingToMapMode() {
		assert(!mapModeIncoming());
		List<Object> transitions = new ArrayList<Object>(3);
		if (mIn1 != null) {
			transitions.add(mIn1);
			mIn1 = null;
		}
		if (mIn2 != null) {
			transitions.add(mIn2);
			mIn2 = null;
		}
		if (mIn3 != null) {
			transitions.add(mIn3);
			mIn3 = null;
		}
		for (Object trans : transitions) {
			if (trans instanceof IncomingInternalTransition) {
				addInternalIncomingMap((IncomingInternalTransition<LETTER, STATE>) trans);
			} else if (trans instanceof IncomingCallTransition) {
				addCallIncomingMap((IncomingCallTransition<LETTER, STATE>) trans);
			} else if (trans instanceof IncomingReturnTransition) {
				addReturnIncomingMap((IncomingReturnTransition<LETTER, STATE>) trans);
			} else {
				throw new AssertionError();
			}
		}
		assert (mapModeIncoming());
	}
	
	
	
	@Override
	void addInternalOutgoing(OutgoingInternalTransition<LETTER, STATE> trans) {
		if (mapModeOutgoing()) {
			addInternalOutgoingMap(trans);
		} else {
			if (mOut1 == null) {
				mOut1 = trans;
			} else if (mOut2 == null) {
				mOut2 = trans;
			} else if (mOut3 == null && (mOut2 instanceof OutgoingInternalTransition)) {
				mOut3 = trans;
			} else {
				switchOutgoingToMapMode();
				addInternalOutgoingMap(trans);
			}
		}
	}


	@Override
	void addInternalIncoming(IncomingInternalTransition<LETTER, STATE> trans) {
		if (mapModeIncoming()) {
			addInternalIncomingMap(trans);
		} else {
			if (mIn1 == null) {
				mIn1 = trans;
			} else if (mIn2 == null) {
				mIn2 = trans;
			} else if (mIn3 == null && (mIn2 instanceof IncomingInternalTransition)) {
				mIn3 = trans;
			} else {
				switchIncomingToMapMode();
				addInternalIncomingMap(trans);
			}
		}
	}


	@Override
	void addCallOutgoing(OutgoingCallTransition<LETTER, STATE> trans) {
		if (mapModeOutgoing()) {
			addCallOutgoingMap(trans);
		} else {
			if (mOut2 == null) {
				mOut2 = trans;
			} else {
				switchOutgoingToMapMode();
				addCallOutgoingMap(trans);
			}
		}
	}


	@Override
	void addCallIncoming(IncomingCallTransition<LETTER, STATE> trans) {
		if (mapModeIncoming()) {
			addCallIncomingMap(trans);
		} else {
			if (mIn2 == null) {
				mIn2 = trans;
			} else {
				switchIncomingToMapMode();
				addCallIncomingMap(trans);
			}
		}
	}


	@Override
	void addReturnOutgoing(OutgoingReturnTransition<LETTER, STATE> trans) {
		if (mapModeOutgoing()) {
			addReturnOutgoingMap(trans);
		} else {
			if (mOut3 == null) {
				mOut3 = trans;
			} else {
				switchOutgoingToMapMode();
				addReturnOutgoingMap(trans);
			}
		}
	}


	@Override
	void addReturnIncoming(IncomingReturnTransition<LETTER, STATE> trans) {
		if (mapModeIncoming()) {
			addReturnIncomingMap(trans);
		} else {
			if (mIn3 == null) {
				mIn3 = trans;
			} else {
				switchIncomingToMapMode();
				addReturnIncomingMap(trans);
			}
		}
	}


	
	void addInternalOutgoingMap(OutgoingInternalTransition<LETTER, STATE> internalOutgoing) {
		LETTER letter = internalOutgoing.getLetter();
		STATE succ = internalOutgoing.getSucc();
		if (mOut1 == null) {
			mOut1 = new HashMap<LETTER, Set<STATE>>();
		}
		Set<STATE> succs = ((Map<LETTER, Set<STATE>>) mOut1).get(letter);
		if (succs == null) {
			succs = new HashSet<STATE>();
			((Map<LETTER, Set<STATE>>) mOut1).put(letter, succs);
		}
		succs.add(succ);
	}

	void addInternalIncomingMap(IncomingInternalTransition<LETTER, STATE> internalIncoming) {
		LETTER letter = internalIncoming.getLetter();
		STATE pred = internalIncoming.getPred();
		if (mIn1 == null) {
			mIn1 = new HashMap<LETTER, Set<STATE>>();
		}
		Set<STATE> preds = ((Map<LETTER, Set<STATE>>) mIn1).get(letter);
		if (preds == null) {
			preds = new HashSet<STATE>();
			((Map<LETTER, Set<STATE>>) mIn1).put(letter,preds);
		}
		preds.add(pred);
	}

	void addCallOutgoingMap(OutgoingCallTransition<LETTER, STATE> callOutgoing) {
		LETTER letter = callOutgoing.getLetter();
		STATE succ = callOutgoing.getSucc();
		if (mOut2 == null) {
			mOut2 = new HashMap<LETTER, Set<STATE>>();
		}
		Set<STATE> succs = ((Map<LETTER, Set<STATE>>) mOut2).get(letter);
		if (succs == null) {
			succs = new HashSet<STATE>();
			((Map<LETTER, Set<STATE>>) mOut2).put(letter,succs);
		}
		succs.add(succ);
	}
	void addCallIncomingMap(IncomingCallTransition<LETTER, STATE> callIncoming) {
		LETTER letter = callIncoming.getLetter();
		STATE pred = callIncoming.getPred();
		if (mIn2 == null) {
			mIn2 = new HashMap<LETTER, Set<STATE>>();
		}
		Set<STATE> preds = ((Map<LETTER, Set<STATE>>) mIn2).get(letter);
		if (preds == null) {
			preds = new HashSet<STATE>();
			((Map<LETTER, Set<STATE>>) mIn2).put(letter,preds);
		}
		preds.add(pred);
	}
	void addReturnOutgoingMap(OutgoingReturnTransition<LETTER, STATE> returnOutgoing) {
		LETTER letter = returnOutgoing.getLetter();
		STATE hier = returnOutgoing.getHierPred();
		STATE succ = returnOutgoing.getSucc();
		if (mOut3 == null) {
			mOut3 = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
		}
		Map<STATE, Set<STATE>> hier2succs = ((Map<LETTER, Map<STATE, Set<STATE>>>) mOut3).get(letter);
		if (hier2succs == null) {
			hier2succs = new HashMap<STATE, Set<STATE>>();
			((Map<LETTER, Map<STATE, Set<STATE>>>) mOut3).put(letter, hier2succs);
		}
		Set<STATE> succs = hier2succs.get(hier);
		if (succs == null) {
			succs = new HashSet<STATE>();
			hier2succs.put(hier, succs);
		}
		succs.add(succ);
	}
	void addReturnIncomingMap(IncomingReturnTransition<LETTER, STATE> returnIncoming) {
		LETTER letter = returnIncoming.getLetter();
		STATE hier = returnIncoming.getHierPred();
		STATE pred = returnIncoming.getLinPred();
		if (mIn3 == null) {
			mIn3 = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
		}
		Map<STATE, Set<STATE>> hier2preds = ((Map<LETTER, Map<STATE, Set<STATE>>>) mIn3).get(letter);
		if (hier2preds == null) {
			hier2preds = new HashMap<STATE, Set<STATE>>();
			((Map<LETTER, Map<STATE, Set<STATE>>>) mIn3).put(letter, hier2preds);
		}
		Set<STATE> preds = hier2preds.get(hier);
		if (preds == null) {
			preds = new HashSet<STATE>();
			hier2preds.put(hier, preds);
		}
		preds.add(pred);
	}


	@Override
	public Collection<LETTER> lettersInternal() {
		if (mapModeOutgoing()) {
			Map<LETTER, Set<STATE>> map = (Map<LETTER, Set<STATE>>) mOut1;
			return map == null ? m_EmptySetOfLetters : map.keySet();
		} else {
			Collection<LETTER> result = new ArrayList<LETTER>(3);
			if (mOut1 instanceof OutgoingInternalTransition) {
				LETTER letter = ((OutgoingInternalTransition<LETTER, STATE>) mOut1).getLetter();
				result.add(letter);
				if (mOut2 instanceof OutgoingInternalTransition) {
					letter = ((OutgoingInternalTransition<LETTER, STATE>) mOut2).getLetter();
					if (!result.contains(letter)) {
						result.add(letter);
					}
					if (mOut3 instanceof OutgoingInternalTransition) {
						letter = ((OutgoingInternalTransition<LETTER, STATE>) mOut3).getLetter();
						if (!result.contains(letter)) {
							result.add(letter);
							
						}
					}
				}
			}
			return result;
		}
	}


	@Override
	public Collection<LETTER> lettersInternalIncoming() {
		if (mapModeIncoming()) {
			Map<LETTER, Set<STATE>> map = (Map<LETTER, Set<STATE>>) mIn1;
			return map == null ? m_EmptySetOfLetters : map.keySet();
		} else {
			Collection<LETTER> result = new ArrayList<LETTER>(3);
			if (mIn1 instanceof IncomingInternalTransition) {
				LETTER letter = ((IncomingInternalTransition<LETTER, STATE>) mIn1).getLetter();
				result.add(letter);
				if (mIn2 instanceof IncomingInternalTransition) {
					letter = ((IncomingInternalTransition<LETTER, STATE>) mIn2).getLetter();
					if (!result.contains(letter)) {
						result.add(letter);
					}
					if (mIn3 instanceof IncomingInternalTransition) {
						letter = ((IncomingInternalTransition<LETTER, STATE>) mIn3).getLetter();
						if (!result.contains(letter)) {
							result.add(letter);
							
						}
					}
				}
			}
			return result;
		}
	}

	@Override
	public Collection<LETTER> lettersCall() {
		if (mapModeOutgoing()) {
			Map<LETTER, Set<STATE>> map = (Map<LETTER, Set<STATE>>) mOut2;
			return map == null ? m_EmptySetOfLetters : map.keySet();
		} else {
			Collection<LETTER> result = new ArrayList<LETTER>(1);
			if (mOut2 instanceof OutgoingCallTransition) {
				LETTER letter = ((OutgoingCallTransition<LETTER, STATE>) mOut2).getLetter();
				result.add(letter);
			}
			return result;
		}
	}

	@Override
	public Collection<LETTER> lettersCallIncoming() {
		if (mapModeIncoming()) {
			Map<LETTER, Set<STATE>> map = (Map<LETTER, Set<STATE>>) mIn2;
			return map == null ? m_EmptySetOfLetters : map.keySet();
		} else {
			Collection<LETTER> result = new ArrayList<LETTER>(1);
			if (mIn2 instanceof IncomingCallTransition) {
				LETTER letter = ((IncomingCallTransition<LETTER, STATE>) mIn2).getLetter();
				result.add(letter);
			}
			return result;
		}
	}

	@Override
	public Collection<LETTER> lettersReturn() {
		if (mapModeOutgoing()) {
			Map<LETTER, Map<STATE, Set<STATE>>> map = (Map<LETTER, Map<STATE, Set<STATE>>>) mOut3;
			return map == null ? m_EmptySetOfLetters : map.keySet();
		} else {
			Collection<LETTER> result = new ArrayList<LETTER>(1);
			if (mOut3 instanceof OutgoingReturnTransition) {
				LETTER letter = ((OutgoingReturnTransition<LETTER, STATE>) mOut3).getLetter();
				result.add(letter);
			}
			return result;
		}
	}

	@Override
	public Collection<LETTER> lettersReturnIncoming() {
		if (mapModeIncoming()) {
			Map<LETTER, Map<STATE, Set<STATE>>> map = (Map<LETTER, Map<STATE, Set<STATE>>>) mIn3;
			return map == null ? m_EmptySetOfLetters : map.keySet();
		} else {
			Collection<LETTER> result = new ArrayList<LETTER>(1);
			if (mIn3 instanceof IncomingReturnTransition) {
				LETTER letter = ((IncomingReturnTransition<LETTER, STATE>) mIn3).getLetter();
				result.add(letter);
			}
			return result;
		}
	}


	@Override
	public Collection<STATE> succInternal(LETTER letter) {
		if (mapModeOutgoing()) {
			Map<LETTER, Set<STATE>> map = (Map<LETTER, Set<STATE>>) mOut1;
			if (map == null) {
				return m_EmptySetOfStates;
			}
			Set<STATE> result = map.get(letter);
			return result == null ? m_EmptySetOfStates : result;
		} else {
			Collection<STATE> result = new ArrayList<STATE>(3);
			if (properOutgoingInternalTransitionAtPosition1(letter)) {
				STATE state = ((OutgoingInternalTransition<LETTER, STATE>) mOut1).getSucc();
				result.add(state);
			}
			if (properOutgoingInternalTransitionAtPosition2(letter)) {
				STATE state = ((OutgoingInternalTransition<LETTER, STATE>) mOut2).getSucc();
				if (!result.contains(state)) {
					result.add(state);
				}
			}
			if (properOutgoingInternalTransitionAtPosition3(letter)) {
				STATE state = ((OutgoingInternalTransition<LETTER, STATE>) mOut3).getSucc();
				if (!result.contains(state)) {
					result.add(state);
				}
			}
			return result;
		}
	}

	@Override
	public Collection<STATE> predInternal(LETTER letter) {
		if (mapModeIncoming()) {
			Map<LETTER, Set<STATE>> map = (Map<LETTER, Set<STATE>>) mIn1;
			if (map == null) {
				return m_EmptySetOfStates;
			}
			Set<STATE> result = map.get(letter);
			return result == null ? m_EmptySetOfStates : result;
		} else {
			Collection<STATE> result = new ArrayList<STATE>(3);
			if (properIncomingInternalTransitionAtPosition1(letter)) {
				STATE state = ((IncomingInternalTransition<LETTER, STATE>) mIn1).getPred();
				result.add(state);
			}
			if (properIncomingInternalTransitionAtPosition2(letter)) {
				STATE state = ((IncomingInternalTransition<LETTER, STATE>) mIn2).getPred();
				if (!result.contains(state)) {
					result.add(state);
				}
			}
			if (properIncomingInternalTransitionAtPosition3(letter)) {
				STATE state = ((IncomingInternalTransition<LETTER, STATE>) mIn3).getPred();
				if (!result.contains(state)) {
					result.add(state);
				}
			}
			return result;
		}
	}

	@Override
	public Collection<STATE> succCall(LETTER letter) {
		if (mapModeOutgoing()) {
			Map<LETTER, Set<STATE>> map = (Map<LETTER, Set<STATE>>) mOut2;
			if (map == null) {
				return m_EmptySetOfStates;
			}
			Set<STATE> result = map.get(letter);
			return result == null ? m_EmptySetOfStates : result;
		} else {
			Collection<STATE> result = new ArrayList<STATE>(1);
			if (properOutgoingCallTransitionAtPosition2(letter)) {
				STATE state = ((OutgoingCallTransition<LETTER, STATE>) mOut2).getSucc();
				result.add(state);
			}
			return result;
		}
	}

	@Override
	public Collection<STATE> predCall(LETTER letter) {
		if (mapModeIncoming()) {
			Map<LETTER, Set<STATE>> map = (Map<LETTER, Set<STATE>>) mIn2;
			if (map == null) {
				return m_EmptySetOfStates;
			}
			Set<STATE> result = map.get(letter);
			return result == null ? m_EmptySetOfStates : result;
		} else {
			Collection<STATE> result = new ArrayList<STATE>(1);
			if (properIncomingCallTransitionAtPosition2(letter)) {
				STATE state = ((IncomingCallTransition<LETTER, STATE>) mIn2).getPred();
				result.add(state);
			}
			return result;
		}
	}

	@Override
	public Collection<STATE> hierPred(LETTER letter) {
		if (mapModeOutgoing()) {
			Map<LETTER, Map<STATE, Set<STATE>>> map = (Map<LETTER, Map<STATE, Set<STATE>>>) mOut3;
			if (map == null) {
				return m_EmptySetOfStates;
			}
			Map<STATE, Set<STATE>> hier2succs = map.get(letter);
			return hier2succs == null ? m_EmptySetOfStates : hier2succs.keySet();
		} else {
			Collection<STATE> result = new ArrayList<STATE>(1);
			if (properOutgoingReturnTransitionAtPosition3(null, letter)) {
				STATE state = ((OutgoingReturnTransition<LETTER, STATE>) mOut3).getHierPred();
				result.add(state);
			}
			return result;
		}
	}

	@Override
	public Collection<STATE> succReturn(STATE hier, LETTER letter) {
		if (mapModeOutgoing()) {
			Map<LETTER, Map<STATE, Set<STATE>>> map = (Map<LETTER, Map<STATE, Set<STATE>>>) mOut3;
			if (map == null) {
				return m_EmptySetOfStates;
			}
			Map<STATE, Set<STATE>> hier2succs = map.get(letter);
			if (hier2succs == null) {
				return m_EmptySetOfStates;
			}
			Set<STATE> result = hier2succs.get(hier);
			return result == null ? m_EmptySetOfStates : result;
		} else {
			Collection<STATE> result = new ArrayList<STATE>(1);
			if (properOutgoingReturnTransitionAtPosition3(hier, letter)) {
				STATE state = ((OutgoingReturnTransition<LETTER, STATE>) mOut3).getSucc();
				result.add(state);
			}
			return result;
		}
	}

	@Override
	public Collection<STATE> predReturnLin(LETTER letter, STATE hier) {
		if (mapModeIncoming()) {
			Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds  = (Map<LETTER, Map<STATE, Set<STATE>>>) mIn3;
			if (letter2hier2preds == null) {
				return m_EmptySetOfStates;
			}
			Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
			if (hier2preds == null) {
				return m_EmptySetOfStates;
			}
			Set<STATE> result = hier2preds.get(hier);
			return result == null ? m_EmptySetOfStates : result;
		} else {
			Collection<STATE> result = new ArrayList<STATE>(1);
			if (properIncomingReturnTransitionAtPosition3(hier, letter)) {
				STATE state = ((IncomingReturnTransition<LETTER, STATE>) mIn3).getLinPred();
				result.add(state);
			}
			return result;
		}
	}

	public Collection<STATE> predReturnHier(LETTER letter) {
		if (mapModeIncoming()) {
			Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds  = (Map<LETTER, Map<STATE, Set<STATE>>>) mIn3;
			if (letter2hier2preds == null) {
				return m_EmptySetOfStates ;
			}
			Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
			if (hier2preds == null) {
				return m_EmptySetOfStates;
			}
			return hier2preds.keySet();
		} else {
			Collection<STATE> result = new ArrayList<STATE>(1);
			if (properIncomingReturnTransitionAtPosition3(null, letter)) {
				STATE state = ((IncomingReturnTransition<LETTER, STATE>) mIn3).getHierPred();
				result.add(state);
			}
			return result;
		}
	}



	
	private Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessorsMap(
			final LETTER letter) {
		assert (mapModeIncoming());
		return new Iterable<IncomingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingInternalTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Set<STATE>> letter2pred = (Map<LETTER, Set<STATE>>) mIn1;
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



	private Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessorsMap() {
		assert (mapModeIncoming());
		return new Iterable<IncomingInternalTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all IncomingInternalTransition of succ.
			 * Iterates over all incoming internal letters and uses the 
			 * iterators returned by internalPredecessorsMap(letter, succ)
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
								m_CurrentIterator = internalPredecessorsMap(
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





	private Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessorsMap(
			final LETTER letter) {
		assert (mapModeIncoming());
		return new Iterable<IncomingCallTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingCallTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingCallTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingCallTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Set<STATE>> letter2pred = (Map<LETTER, Set<STATE>>) mIn2;
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



	private Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessorsMap() {
		assert (mapModeIncoming());
		return new Iterable<IncomingCallTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all IncomingCallTransition of succ.
			 * Iterates over all incoming call letters and uses the 
			 * iterators returned by callPredecessorsMap(letter, succ)
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
								m_CurrentIterator = callPredecessorsMap(
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



	private Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessorsMap(
			final STATE hier, final LETTER letter) {
		assert (mapModeIncoming());
		return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingReturnTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = (Map<LETTER, Map<STATE, Set<STATE>>>) mIn3;
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


	private Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessorsMap(
			final LETTER letter) {
		assert (mapModeIncoming());
		return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all IncomingReturnTransition of succ.
			 * Iterates over all incoming return letters and uses the 
			 * iterators returned by returnPredecessorsMap(hier, letter, succ)
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
								m_CurrentIterator = returnPredecessorsMap(
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


	private Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessorsMap() {
		assert (mapModeIncoming());
		return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all IncomingReturnTransition of succ.
			 * Iterates over all incoming return letters and uses the 
			 * iterators returned by returnPredecessorsMap(letter, succ)
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
								m_CurrentIterator = returnPredecessorsMap(
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



	private Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessorsMap(
			final LETTER letter) {
		assert (mapModeOutgoing());
		return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Set<STATE>> letter2succ = (Map<LETTER, Set<STATE>>) mOut1;
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

	private Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessorsMap() {
		assert (mapModeOutgoing());
		return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingInternalTransition of state.
			 * Iterates over all outgoing internal letters and uses the 
			 * iterators returned by internalSuccessorsMap(state, letter)
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
								m_CurrentIterator = internalSuccessorsMap(
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





	private Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessorsMap(
			final LETTER letter) {
		assert (mapModeOutgoing());
		return new Iterable<OutgoingCallTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingCallTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingCallTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Set<STATE>> letter2succ = (Map<LETTER, Set<STATE>>) mOut2;
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

	private Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessorsMap() {
		assert (mapModeOutgoing());
		return new Iterable<OutgoingCallTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingCallTransition of state.
			 * Iterates over all outgoing call letters and uses the 
			 * iterators returned by callSuccessorsMap(state, letter)
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
								m_CurrentIterator = callSuccessorsMap(m_CurrentLetter).iterator();
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








	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsMap(
			final STATE hier, final LETTER letter) {
		assert (mapModeOutgoing());
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
						Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succ = (Map<LETTER, Map<STATE, Set<STATE>>>) mOut3;
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


	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsMap(
			final LETTER letter) {
		assert (mapModeOutgoing());
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingReturnTransition of state.
			 * Iterates over all outgoing return letters and uses the 
			 * iterators returned by returnSuccecessorsMap(state, letter)
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
								m_CurrentIterator = returnSuccessorsMap(
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

	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHierMap(
			final STATE hier) {
		assert (mapModeOutgoing());
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingReturnTransition of state with 
			 * hierarchical successor hier. 
			 * Iterates over all outgoing return letters and uses the 
			 * iterators returned by returnSuccecessorsMap(state, hier, letter)
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
								m_CurrentIterator = returnSuccessorsMap(
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


	private Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsMap(
			) {
		assert (mapModeOutgoing());
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingReturnTransition of state.
			 * Iterates over all outgoing return letters and uses the 
			 * iterators returned by returnSuccessorsMap(state, letter)
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
								m_CurrentIterator = returnSuccessorsMap(m_CurrentLetter).iterator();
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


	
	
	private boolean properOutgoingInternalTransitionAtPosition1(LETTER letter) {
		return (mOut1 instanceof OutgoingInternalTransition) &&
				(letter == null || letter.equals(((OutgoingInternalTransition<LETTER, STATE>) mOut1).getLetter()));
	}
	
	private boolean properOutgoingInternalTransitionAtPosition2(LETTER letter) {
		return (mOut2 instanceof OutgoingInternalTransition) &&
				(letter == null || letter.equals(((OutgoingInternalTransition<LETTER, STATE>) mOut2).getLetter()));
	}
	
	private boolean properOutgoingInternalTransitionAtPosition3(LETTER letter) {
		return (mOut3 instanceof OutgoingInternalTransition) &&
				(letter == null || letter.equals(((OutgoingInternalTransition<LETTER, STATE>) mOut3).getLetter()));
	}

	private Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessorsField(final LETTER letter) {
		return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
					/**
					 * Points to next field that has OutgoingInternalTransition.
					 */
					short mPosition;
					{
						mPosition = 0;
						updatePosition();
					}
					
					private void updatePosition() {
						mPosition++;
						while (mPosition < 4) {
							if (mPosition == 1 && properOutgoingInternalTransitionAtPosition1(letter)) {
								return;
							} else if (mPosition == 2 && properOutgoingInternalTransitionAtPosition2(letter)) {
								return;
							} else if (mPosition == 3 && properOutgoingInternalTransitionAtPosition3(letter)) {
								return;
							} else {
								mPosition++;
							}
						}
					}

					@Override
					public boolean hasNext() {
						return mPosition < 4;
					}

					@Override
					public OutgoingInternalTransition<LETTER, STATE> next() {
						Object result;
						if (mPosition == 1) {
							result = mOut1;
						} else if (mPosition == 2) {
							result = mOut2;
						} else if (mPosition == 3) {
							result = mOut3;
						} else {
							throw new NoSuchElementException();
						}
						updatePosition();
						return (OutgoingInternalTransition<LETTER, STATE>) result;
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



	private boolean properIncomingInternalTransitionAtPosition1(LETTER letter) {
		return (mIn1 instanceof IncomingInternalTransition) &&
				(letter == null || letter.equals(((IncomingInternalTransition<LETTER, STATE>) mIn1).getLetter()));
	}
	
	private boolean properIncomingInternalTransitionAtPosition2(LETTER letter) {
		return (mIn2 instanceof IncomingInternalTransition) &&
				(letter == null || letter.equals(((IncomingInternalTransition<LETTER, STATE>) mIn2).getLetter()));
	}
	
	private boolean properIncomingInternalTransitionAtPosition3(LETTER letter) {
		return (mIn3 instanceof IncomingInternalTransition) &&
				(letter == null || letter.equals(((IncomingInternalTransition<LETTER, STATE>) mIn3).getLetter()));
	}

	private Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessorsField(final LETTER letter) {
		return new Iterable<IncomingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingInternalTransition<LETTER, STATE>> iterator() {
				Iterator<IncomingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
					/**
					 * Points to next field that has IncomingInternalTransition.
					 */
					short mPosition;
					{
						mPosition = 0;
						updatePosition();
					}
					
					private void updatePosition() {
						mPosition++;
						while (mPosition < 4) {
							if (mPosition == 1 && properIncomingInternalTransitionAtPosition1(letter)) {
								return;
							} else if (mPosition == 2 && properIncomingInternalTransitionAtPosition2(letter)) {
								return;
							} else if (mPosition == 3 && properIncomingInternalTransitionAtPosition3(letter)) {
								return;
							} else {
								mPosition++;
							}
						}
					}

					@Override
					public boolean hasNext() {
						return mPosition < 4;
					}

					@Override
					public IncomingInternalTransition<LETTER, STATE> next() {
						Object result;
						if (mPosition == 1) {
							result = mIn1;
						} else if (mPosition == 2) {
							result = mIn2;
						} else if (mPosition == 3) {
							result = mIn3;
						} else {
							throw new NoSuchElementException();
						}
						updatePosition();
						return (IncomingInternalTransition<LETTER, STATE>) result;
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
	
	private boolean properOutgoingCallTransitionAtPosition2(LETTER letter) {
		return (mOut2 instanceof OutgoingCallTransition) &&
				(letter == null || letter.equals(((OutgoingCallTransition<LETTER, STATE>) mOut2).getLetter()));
	}
	
	private boolean properIncomingCallTransitionAtPosition2(LETTER letter) {
		return (mIn2 instanceof IncomingCallTransition) &&
				(letter == null || letter.equals(((IncomingCallTransition<LETTER, STATE>) mIn2).getLetter()));
	}
	
	private boolean properOutgoingReturnTransitionAtPosition3(STATE hier, LETTER letter) {
		return (mOut3 instanceof OutgoingReturnTransition) &&
				(hier == null || hier.equals(((OutgoingReturnTransition<LETTER, STATE>) mOut3).getHierPred())) &&
				(letter == null || letter.equals(((OutgoingReturnTransition<LETTER, STATE>) mOut3).getLetter()));
	}
	
	private boolean properIncomingReturnTransitionAtPosition3(STATE hier, LETTER letter) {
		return (mIn3 instanceof IncomingReturnTransition) &&
				(hier == null || hier.equals(((IncomingReturnTransition<LETTER, STATE>) mIn3).getHierPred())) &&
				(letter == null || letter.equals(((IncomingReturnTransition<LETTER, STATE>) mIn3).getLetter()));
	}
	
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			LETTER letter) {
		if (mapModeOutgoing()) {
			return callSuccessorsMap(letter);
		} else {
			ArrayList<OutgoingCallTransition<LETTER, STATE>> result = 
					new ArrayList<OutgoingCallTransition<LETTER, STATE>>(1);
			if (properOutgoingCallTransitionAtPosition2(letter)) {
				result.add((OutgoingCallTransition<LETTER, STATE>) mOut2);
			}
			return result;
		}
	}


	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors() {
		if (mapModeOutgoing()) {
			return callSuccessorsMap();
		} else {
			ArrayList<OutgoingCallTransition<LETTER, STATE>> result = 
					new ArrayList<OutgoingCallTransition<LETTER, STATE>>(1);
			if (properOutgoingCallTransitionAtPosition2(null)) {
				result.add((OutgoingCallTransition<LETTER, STATE>) mOut2);
			}
			return result;
		}
	}


	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			LETTER letter) {
		if (mapModeIncoming()) {
			return callPredecessorsMap(letter);
		} else {
			ArrayList<IncomingCallTransition<LETTER, STATE>> result = 
					new ArrayList<IncomingCallTransition<LETTER, STATE>>(1);
			if (properIncomingCallTransitionAtPosition2(letter)) {
				result.add((IncomingCallTransition<LETTER, STATE>) mIn2);
			}
			return result;
		}
	}


	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors() {
		if (mapModeIncoming()) {
			return callPredecessorsMap();
		} else {
			ArrayList<IncomingCallTransition<LETTER, STATE>> result = 
					new ArrayList<IncomingCallTransition<LETTER, STATE>>(1);
			if (properIncomingCallTransitionAtPosition2(null)) {
				result.add((IncomingCallTransition<LETTER, STATE>) mIn2);
			}
			return result;
		}
	}


	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE hier, LETTER letter) {
		if (mapModeOutgoing()) {
			return returnSuccessorsMap(hier,letter);
		} else {
			ArrayList<OutgoingReturnTransition<LETTER, STATE>> result = 
					new ArrayList<OutgoingReturnTransition<LETTER, STATE>>(1);
			if (properOutgoingReturnTransitionAtPosition3(hier,letter)) {
				result.add((OutgoingReturnTransition<LETTER, STATE>) mOut3);
			}
			return result;
		}
	}


	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			LETTER letter) {
		if (mapModeOutgoing()) {
			return returnSuccessorsMap(letter);
		} else {
			ArrayList<OutgoingReturnTransition<LETTER, STATE>> result = 
					new ArrayList<OutgoingReturnTransition<LETTER, STATE>>(1);
			if (properOutgoingReturnTransitionAtPosition3(null,letter)) {
				result.add((OutgoingReturnTransition<LETTER, STATE>) mOut3);
			}
			return result;
		}
	}


	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE hier) {
		if (mapModeOutgoing()) {
			return returnSuccessorsGivenHierMap(hier);
		} else {
			ArrayList<OutgoingReturnTransition<LETTER, STATE>> result = 
					new ArrayList<OutgoingReturnTransition<LETTER, STATE>>(1);
			if (properOutgoingReturnTransitionAtPosition3(hier,null)) {
				result.add((OutgoingReturnTransition<LETTER, STATE>) mOut3);
			}
			return result;
		}
	}


	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors() {
		if (mapModeOutgoing()) {
			return returnSuccessorsMap();
		} else {
			ArrayList<OutgoingReturnTransition<LETTER, STATE>> result = 
					new ArrayList<OutgoingReturnTransition<LETTER, STATE>>(1);
			if (properOutgoingReturnTransitionAtPosition3(null,null)) {
				result.add((OutgoingReturnTransition<LETTER, STATE>) mOut3);
			}
			return result;
		}
	}


	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			STATE hier, LETTER letter) {
		if (mapModeIncoming()) {
			return returnPredecessorsMap(hier,letter);
		} else {
			ArrayList<IncomingReturnTransition<LETTER, STATE>> result = 
					new ArrayList<IncomingReturnTransition<LETTER, STATE>>(1);
			if (properIncomingReturnTransitionAtPosition3(hier,letter)) {
				result.add((IncomingReturnTransition<LETTER, STATE>) mIn3);
			}
			return result;
		}
	}


	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			LETTER letter) {
		if (mapModeIncoming()) {
			return returnPredecessorsMap(letter);
		} else {
			ArrayList<IncomingReturnTransition<LETTER, STATE>> result = 
					new ArrayList<IncomingReturnTransition<LETTER, STATE>>(1);
			if (properIncomingReturnTransitionAtPosition3(null,letter)) {
				result.add((IncomingReturnTransition<LETTER, STATE>) mIn3);
			}
			return result;
		}
	}


	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors() {
		if (mapModeIncoming()) {
			return returnPredecessorsMap();
		} else {
			ArrayList<IncomingReturnTransition<LETTER, STATE>> result = 
					new ArrayList<IncomingReturnTransition<LETTER, STATE>>(1);
			if (properIncomingReturnTransitionAtPosition3(null,null)) {
				result.add((IncomingReturnTransition<LETTER, STATE>) mIn3);
			}
			return result;
		}
	}





	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			LETTER letter) {
		if(mapModeOutgoing()) {
			return internalSuccessorsMap(letter);
		} else {
			return internalSuccessorsField(letter);
		}
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors() {
		if(mapModeOutgoing()) {
			return internalSuccessorsMap();
		} else {
			return internalSuccessorsField(null);
		}
	}


	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			LETTER letter) {
		if(mapModeIncoming()) {
			return internalPredecessorsMap(letter);
		} else {
			return internalPredecessorsField(letter);
		}
	}


	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors() {
		if(mapModeIncoming()) {
			return internalPredecessorsMap();
		} else {
			return internalPredecessorsField(null);
		}
	}
}

