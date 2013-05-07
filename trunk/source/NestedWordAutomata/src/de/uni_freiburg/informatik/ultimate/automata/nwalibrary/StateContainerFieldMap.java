package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * Contains STATES and information of transitions in field/Map implementation
 * of NWAs 
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class StateContainerFieldMap<LETTER, STATE> {
	private final STATE m_State;
	private Object mOut1;
	private Object mOut2;
	private Object mOut3;
	
	public StateContainerFieldMap(STATE state) {
		m_State = state;
	}
	
	STATE getState() {
		return m_State;
	}
	
	private boolean inOutMapMode() {
		return (mOut1 instanceof Map);
	}
	
	private void addOutgoingInternal(LETTER letter, STATE succ) {
		OutgoingInternalTransition<LETTER, STATE> trans = 
				new OutgoingInternalTransition<LETTER, STATE>(letter, succ);
		if (inOutMapMode()) {
			addInternalTransitionMap((Map<LETTER, Set<STATE>>) mOut1, letter, succ);
		} else {
			if (mOut1 == null) {
				mOut1 = trans;
			} else if (mOut2 == null) {
				mOut2 = trans;
			} else if (mOut3 == null) {
				mOut3 = trans;
			} else {
				switchOutMode();
				addInternalTransitionMap((Map<LETTER, Set<STATE>>) mOut1, letter, succ);
			}
		}
	}
	
	private void switchOutMode() {
		assert mOut1 != null && !(mOut1 instanceof Map);
		assert mOut2 != null && !(mOut2 instanceof Map);
		assert mOut3 != null && !(mOut3 instanceof Map);
		Object[] outgoings = new Object[]{mOut1, mOut2, mOut3};
		mOut1 = new HashMap<LETTER, Set<STATE>>();
		mOut2 = new HashMap<LETTER, Set<STATE>>();
		mOut3 = new HashMap<Map<LETTER,STATE>, Set<STATE>>();
		for (Object out : outgoings) {
			if (out instanceof OutgoingInternalTransition) {
				OutgoingInternalTransition<LETTER, STATE> internal = (OutgoingInternalTransition<LETTER, STATE>) out;
				addInternalTransitionMap((Map<LETTER, Set<STATE>>) mOut1, internal.getLetter(), internal.getSucc());
			} else {
				throw new AssertionError();
			}
		}
	}
	
	
	private void addInternalTransitionMap(Map<LETTER, Set<STATE>> letter2succs, LETTER letter, STATE succ) {
		Set<STATE> succs = letter2succs.get(letter);
		if (succs == null) {
			succs = new HashSet<STATE>();
			letter2succs.put(letter,succs);
		}
		succs.add(succ);
	}
	
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessorsField() {
		return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
					/**
					 * Points to next field that has OutgoingInternalTransition.
					 */
					int mPosition;
					{
						mPosition = 0;
						updatePosition();
					}
					
					private void updatePosition() {
						mPosition++;
						while (mPosition < 4) {
							if (mPosition == 1 && (mOut1 instanceof OutgoingInternalTransition)) {
								return;
							} else if (mPosition == 2 && (mOut2 instanceof OutgoingInternalTransition)) {
								return;
							} else if (mPosition == 3 && (mOut3 instanceof OutgoingInternalTransition)) {
								return;
							} else {
								throw new AssertionError();
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
	
	
	
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessorsMap(
			final Map<LETTER, Set<STATE>> letter2succ, final LETTER letter) {
		return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
				Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
					Iterator<STATE> m_Iterator;
					{
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
						return m_Iterator == null || m_Iterator.hasNext();
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
	
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessorsMap(
			final Map<LETTER, Set<STATE>> letter2succ) {
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
						m_LetterIterator = letter2succ.keySet().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (m_LetterIterator.hasNext()) {
							do {
								m_CurrentLetter = m_LetterIterator.next();
								m_CurrentIterator = internalSuccessorsMap(letter2succ,
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

}
