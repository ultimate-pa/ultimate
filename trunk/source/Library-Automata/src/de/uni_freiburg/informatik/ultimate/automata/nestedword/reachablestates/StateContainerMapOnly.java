/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * Contains STATES and information of transitions.
 *
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
class StateContainerMapOnly<LETTER,STATE> extends StateContainer<LETTER, STATE> {

	/**
	 * Set of internal transitions PREs x LETTERs x SUCCs stored as map
	 * PREs -> LETTERs -> SUCCs
	 * The keySet of this map is used to store the set of states of this
	 * automaton.
	 */
	private Map<LETTER,Set<STATE>> mInternalOut;

	/**
	 * Set of internal transitions PREs x LETTERs x SUCCs stored as map
	 * SUCCs -> LETTERs -> PREs
	 */
	private Map<LETTER,Set<STATE>> mInternalIn =
			new HashMap<LETTER,Set<STATE>>();

	/**
	 * Set of call transitions PREs x LETTERs x SUCCs stored as map
	 * PREs -> LETTERs -> SUCCs
	 */
	private Map<LETTER,Set<STATE>> mCallOut =
			new HashMap<LETTER,Set<STATE>>();

	/**
	 * Set of call transitions PREs x LETTERs x SUCCs stored as map
	 * SUCCs -> LETTERs -> PREs
	 */
	private Map<LETTER,Set<STATE>> mCallIn =
			new HashMap<LETTER,Set<STATE>>();

	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
	 * map LinPREs -> LETTERs -> HierPREs -> SUCCs
	 * 
	 */
	private Map<LETTER,Map<STATE,Set<STATE>>> mReturnOut =
			new HashMap<LETTER,Map<STATE,Set<STATE>>>();

//	/**
//	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
//	 * map HierPREs -> LETTERs -> LinPREs -> SUCCs
//	 * 
//	 */
//	private final Map<LETTER,Map<STATE,Set<STATE>>> mReturnSummary =
//			new HashMap<LETTER,Map<STATE,Set<STATE>>>();

	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as 
	 * map SUCCs -> LETTERs -> HierPREs -> LinPREs
	 * 
	 */
	private Map<LETTER,Map<STATE,Set<STATE>>> mReturnIn =
			new HashMap<LETTER,Map<STATE,Set<STATE>>>();

	private final Set<LETTER> mEmptySetOfLetters = new HashSet<LETTER>(0);

	private final Collection<STATE> mEmptySetOfStates = new HashSet<STATE>(0);

	StateContainerMapOnly(final STATE state, final int serialNumber, 
			final HashMap<STATE,Integer> downStates, final boolean canHaveOutgoingReturn) {
		super(state, serialNumber, downStates, canHaveOutgoingReturn);
	}


	@Override
	void addInternalOutgoing(final OutgoingInternalTransition<LETTER, STATE> internalOutgoing) {
		final LETTER letter = internalOutgoing.getLetter();
		final STATE succ = internalOutgoing.getSucc();
		if (mInternalOut == null) {
			mInternalOut = new HashMap<LETTER, Set<STATE>>();
		}
		Set<STATE> succs = mInternalOut.get(letter);
		if (succs == null) {
			succs = new HashSet<STATE>();
			mInternalOut.put(letter, succs);
		}
		succs.add(succ);
	}

	@Override
	void addInternalIncoming(final IncomingInternalTransition<LETTER, STATE> internalIncoming) {
		final LETTER letter = internalIncoming.getLetter();
		final STATE pred = internalIncoming.getPred();
		if (mInternalIn == null) {
			mInternalIn = new HashMap<LETTER, Set<STATE>>();
		}
		Set<STATE> preds = mInternalIn.get(letter);
		if (preds == null) {
			preds = new HashSet<STATE>();
			mInternalIn.put(letter,preds);
		}
		preds.add(pred);
	}

	@Override
	void addCallOutgoing(final OutgoingCallTransition<LETTER, STATE> callOutgoing) {
		final LETTER letter = callOutgoing.getLetter();
		final STATE succ = callOutgoing.getSucc();
		if (mCallOut == null) {
			mCallOut = new HashMap<LETTER, Set<STATE>>();
		}
		Set<STATE> succs = mCallOut.get(letter);
		if (succs == null) {
			succs = new HashSet<STATE>();
			mCallOut.put(letter,succs);
		}
		succs.add(succ);
	}
	
	@Override
	void addCallIncoming(final IncomingCallTransition<LETTER, STATE> callIncoming) {
		final LETTER letter = callIncoming.getLetter();
		final STATE pred = callIncoming.getPred();
		if (mCallIn == null) {
			mCallIn = new HashMap<LETTER, Set<STATE>>();
		}
		Set<STATE> preds = mCallIn.get(letter);
		if (preds == null) {
			preds = new HashSet<STATE>();
			mCallIn.put(letter,preds);
		}
		preds.add(pred);
	}
	
	@Override
	void addReturnOutgoing(final OutgoingReturnTransition<LETTER, STATE> returnOutgoing) {
		final LETTER letter = returnOutgoing.getLetter();
		final STATE hier = returnOutgoing.getHierPred();
		final STATE succ = returnOutgoing.getSucc();
		if (mReturnOut == null) {
			mReturnOut = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
		}
		Map<STATE, Set<STATE>> hier2succs = mReturnOut.get(letter);
		if (hier2succs == null) {
			hier2succs = new HashMap<STATE, Set<STATE>>();
			mReturnOut.put(letter, hier2succs);
		}
		Set<STATE> succs = hier2succs.get(hier);
		if (succs == null) {
			succs = new HashSet<STATE>();
			hier2succs.put(hier, succs);
		}
		succs.add(succ);
	}
	
	@Override
	void addReturnIncoming(final IncomingReturnTransition<LETTER, STATE> returnIncoming) {
		final LETTER letter = returnIncoming.getLetter();
		final STATE hier = returnIncoming.getHierPred();
		final STATE pred = returnIncoming.getLinPred();
		if (mReturnIn == null) {
			mReturnIn = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
		}
		Map<STATE, Set<STATE>> hier2preds = mReturnIn.get(letter);
		if (hier2preds == null) {
			hier2preds = new HashMap<STATE, Set<STATE>>();
			mReturnIn.put(letter, hier2preds);
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
		final Map<LETTER, Set<STATE>> map = mInternalOut;
		return map == null ? mEmptySetOfLetters : map.keySet();
	}


	@Override
	public Set<LETTER> lettersInternalIncoming() {
		final Map<LETTER, Set<STATE>> map = mInternalIn;
		return map == null ? mEmptySetOfLetters : map.keySet();
	}

	@Override
	public Set<LETTER> lettersCall() {
		final Map<LETTER, Set<STATE>> map = mCallOut;
		return map == null ? mEmptySetOfLetters : map.keySet();
	}

	@Override
	public Set<LETTER> lettersCallIncoming() {
		final Map<LETTER, Set<STATE>> map = mCallIn;
		return map == null ? mEmptySetOfLetters : map.keySet();
	}

	@Override
	public Set<LETTER> lettersReturn() {
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnOut;
		return map == null ? mEmptySetOfLetters : map.keySet();
	}

	@Override
	public Set<LETTER> lettersReturnIncoming() {
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnIn;
		return map == null ? mEmptySetOfLetters : map.keySet();
	}


	@Override
	public Collection<STATE> succInternal(final LETTER letter) {
		final Map<LETTER, Set<STATE>> map = mInternalOut;
		if (map == null) {
			return mEmptySetOfStates;
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? mEmptySetOfStates : result;
	}

	@Override
	public Collection<STATE> predInternal(final LETTER letter) {
		final Map<LETTER, Set<STATE>> map = mInternalIn;
		if (map == null) {
			return mEmptySetOfStates;
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? mEmptySetOfStates : result;
	}

	@Override
	public Collection<STATE> succCall(final LETTER letter) {
		final Map<LETTER, Set<STATE>> map = mCallOut;
		if (map == null) {
			return mEmptySetOfStates;
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? mEmptySetOfStates : result;
	}

	@Override
	public Collection<STATE> predCall(final LETTER letter) {
		final Map<LETTER, Set<STATE>> map = mCallIn;
		if (map == null) {
			return mEmptySetOfStates;
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? mEmptySetOfStates : result;
	}

	@Override
	public Collection<STATE> hierPred(final LETTER letter) {
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnOut;
		if (map == null) {
			return mEmptySetOfStates;
		}
		final Map<STATE, Set<STATE>> hier2succs = map.get(letter);
		return hier2succs == null ? mEmptySetOfStates : hier2succs.keySet();
	}

	@Override
	public Collection<STATE> succReturn(final STATE hier, final LETTER letter) {
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnOut;
		if (map == null) {
			return mEmptySetOfStates;
		}
		final Map<STATE, Set<STATE>> hier2succs = map.get(letter);
		if (hier2succs == null) {
			return mEmptySetOfStates;
		}
		final Set<STATE> result = hier2succs.get(hier);
		return result == null ? mEmptySetOfStates : result;
	}

	@Override
	public Collection<STATE> predReturnLin(final LETTER letter, final STATE hier) {
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds  = mReturnIn;
		if (letter2hier2preds == null) {
			return mEmptySetOfStates;
		}
		final Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		if (hier2preds == null) {
			return mEmptySetOfStates;
		}
		final Set<STATE> result = hier2preds.get(hier);
		return result == null ? mEmptySetOfStates : result;
	}

	@Override
	public Collection<STATE> predReturnHier(final LETTER letter) {
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds  = mReturnIn;
		if (letter2hier2preds == null) {
			return mEmptySetOfStates ;
		}
		final Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		if (hier2preds == null) {
			return mEmptySetOfStates;
		}
		return hier2preds.keySet();
	}





	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final LETTER letter) {
		return new Iterable<IncomingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingInternalTransition<LETTER, STATE>> iterator() {
				final Iterator<IncomingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
					private Iterator<STATE> mIterator;
					{
						final Map<LETTER, Set<STATE>> letter2pred = mInternalIn;
						if (letter2pred != null) {
							if (letter2pred.get(letter) != null) {
								mIterator = letter2pred.get(letter).iterator();
							} else {
								mIterator = null;
							}
						} else {
							mIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mIterator != null && mIterator.hasNext();
					}

					@Override
					public IncomingInternalTransition<LETTER, STATE> next() {
						if (mIterator == null) {
							throw new NoSuchElementException();
						} else {
							final STATE pred = mIterator.next(); 
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
				final Iterator<IncomingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<IncomingInternalTransition<LETTER, STATE>> mCurrentIterator;
					{
						mLetterIterator = lettersInternalIncoming().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = internalPredecessors(
										mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext()
									&& mLetterIterator.hasNext());
							if (!mCurrentIterator.hasNext()) {
								mCurrentLetter = null;
								mCurrentIterator = null;
							}
						} else {
							mCurrentLetter = null;
							mCurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mCurrentLetter != null;
					}

					@Override
					public IncomingInternalTransition<LETTER, STATE> next() {
						if (mCurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							final IncomingInternalTransition<LETTER, STATE> result = 
									mCurrentIterator.next();
							if (!mCurrentIterator.hasNext()) {
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
				final Iterator<IncomingCallTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingCallTransition<LETTER, STATE>>() {
					private Iterator<STATE> mIterator;
					{
						final Map<LETTER, Set<STATE>> letter2pred = mCallIn;
						if (letter2pred != null) {
							if (letter2pred.get(letter) != null) {
								mIterator = letter2pred.get(letter).iterator();
							} else {
								mIterator = null;
							}
						} else {
							mIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mIterator != null && mIterator.hasNext();
					}

					@Override
					public IncomingCallTransition<LETTER, STATE> next() {
						if (mIterator == null) {
							throw new NoSuchElementException();
						} else {
							final STATE pred = mIterator.next(); 
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
				final Iterator<IncomingCallTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingCallTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<IncomingCallTransition<LETTER, STATE>> mCurrentIterator;
					{
						mLetterIterator = lettersCallIncoming().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = callPredecessors(
										mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext()
									&& mLetterIterator.hasNext());
							if (!mCurrentIterator.hasNext()) {
								mCurrentLetter = null;
								mCurrentIterator = null;
							}
						} else {
							mCurrentLetter = null;
							mCurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mCurrentLetter != null;
					}

					@Override
					public IncomingCallTransition<LETTER, STATE> next() {
						if (mCurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							final IncomingCallTransition<LETTER, STATE> result = 
									mCurrentIterator.next();
							if (!mCurrentIterator.hasNext()) {
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
				final Iterator<IncomingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
					private Iterator<STATE> mIterator;
					{
						final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = mReturnIn;
						if (letter2hier2pred != null) {
							final Map<STATE, Set<STATE>> hier2pred = letter2hier2pred.get(letter);
							if (hier2pred != null) {
								if (hier2pred.get(hier) != null) {
									mIterator = hier2pred.get(hier).iterator();
								} else {
									mIterator = null;
								}
							} else {
								mIterator = null;
							}
						} else {
							mIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mIterator != null && mIterator.hasNext();
					}

					@Override
					public IncomingReturnTransition<LETTER, STATE> next() {
						if (mIterator == null) {
							throw new NoSuchElementException();
						} else {
							final STATE pred = mIterator.next(); 
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
				final Iterator<IncomingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
					private Iterator<STATE> mHierIterator;
					private STATE mCurrentHier;
					private Iterator<IncomingReturnTransition<LETTER, STATE>> mCurrentIterator;
					{
						mHierIterator = predReturnHier(letter).iterator();
						nextHier();
					}

					private void nextHier() {
						if (mHierIterator.hasNext()) {
							do {
								mCurrentHier = mHierIterator.next();
								mCurrentIterator = returnPredecessors(
										mCurrentHier, letter).iterator();
							} while (!mCurrentIterator.hasNext()
									&& mHierIterator.hasNext());
							if (!mCurrentIterator.hasNext()) {
								mCurrentHier = null;
								mCurrentIterator = null;
							}
						} else {
							mCurrentHier = null;
							mCurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mCurrentHier != null;
					}

					@Override
					public IncomingReturnTransition<LETTER, STATE> next() {
						if (mCurrentHier == null) {
							throw new NoSuchElementException();
						} else {
							final IncomingReturnTransition<LETTER, STATE> result = 
									mCurrentIterator.next();
							if (!mCurrentIterator.hasNext()) {
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
				final Iterator<IncomingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<IncomingReturnTransition<LETTER, STATE>> mCurrentIterator;
					{
						mLetterIterator = lettersReturnIncoming().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = returnPredecessors(
										mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext()
									&& mLetterIterator.hasNext());
							if (!mCurrentIterator.hasNext()) {
								mCurrentLetter = null;
								mCurrentIterator = null;
							}
						} else {
							mCurrentLetter = null;
							mCurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mCurrentLetter != null;
					}

					@Override
					public IncomingReturnTransition<LETTER, STATE> next() {
						if (mCurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							final IncomingReturnTransition<LETTER, STATE> result = 
									mCurrentIterator.next();
							if (!mCurrentIterator.hasNext()) {
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
				final Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
					private Iterator<STATE> mIterator;
					{
						final Map<LETTER, Set<STATE>> letter2succ = mInternalOut;
						if (letter2succ != null) {
							if (letter2succ.get(letter) != null) {
								mIterator = letter2succ.get(letter).iterator();
							} else {
								mIterator = null;
							}
						} else {
							mIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mIterator != null && mIterator.hasNext();
					}

					@Override
					public OutgoingInternalTransition<LETTER, STATE> next() {
						if (mIterator == null) {
							throw new NoSuchElementException();
						} else {
							final STATE succ = mIterator.next(); 
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
				final Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<OutgoingInternalTransition<LETTER, STATE>> mCurrentIterator;
					{
						mLetterIterator = lettersInternal().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = internalSuccessors(
										mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext()
									&& mLetterIterator.hasNext());
							if (!mCurrentIterator.hasNext()) {
								mCurrentLetter = null;
								mCurrentIterator = null;
							}
						} else {
							mCurrentLetter = null;
							mCurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mCurrentLetter != null;
					}

					@Override
					public OutgoingInternalTransition<LETTER, STATE> next() {
						if (mCurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							final OutgoingInternalTransition<LETTER, STATE> result = 
									mCurrentIterator.next();
							if (!mCurrentIterator.hasNext()) {
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
				final Iterator<OutgoingCallTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
					private Iterator<STATE> mIterator;
					{
						final Map<LETTER, Set<STATE>> letter2succ = mCallOut;
						if (letter2succ != null) {
							if (letter2succ.get(letter) != null) {
								mIterator = letter2succ.get(letter).iterator();
							} else {
								mIterator = null;
							}
						} else {
							mIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mIterator != null && mIterator.hasNext();
					}

					@Override
					public OutgoingCallTransition<LETTER, STATE> next() {
						if (mIterator == null) {
							throw new NoSuchElementException();
						} else {
							final STATE succ = mIterator.next(); 
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
				final Iterator<OutgoingCallTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<OutgoingCallTransition<LETTER, STATE>> mCurrentIterator;
					{
						mLetterIterator = lettersCall().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = callSuccessors(mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext()
									&& mLetterIterator.hasNext());
							if (!mCurrentIterator.hasNext()) {
								mCurrentLetter = null;
								mCurrentIterator = null;
							}
						} else {
							mCurrentLetter = null;
							mCurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mCurrentLetter != null;
					}

					@Override
					public OutgoingCallTransition<LETTER, STATE> next() {
						if (mCurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							final OutgoingCallTransition<LETTER, STATE> result = 
									mCurrentIterator.next();
							if (!mCurrentIterator.hasNext()) {
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
				final Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					private Iterator<STATE> mIterator;
					{
						final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succ = mReturnOut;
						if (letter2hier2succ != null) {
							final Map<STATE, Set<STATE>> hier2succ = letter2hier2succ.get(letter);
							if (hier2succ != null) {
								if (hier2succ.get(hier) != null) {
									mIterator = hier2succ.get(hier).iterator();
								} else {
									mIterator = null;
								}
							} else {
								mIterator = null;
							}
						} else {
							mIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mIterator != null && mIterator.hasNext();
					}

					@Override
					public OutgoingReturnTransition<LETTER, STATE> next() {
						if (mIterator == null) {
							throw new NoSuchElementException();
						} else {
							final STATE succ = mIterator.next(); 
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
				final Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					private Iterator<STATE> mHierIterator;
					private STATE mCurrentHier;
					private Iterator<OutgoingReturnTransition<LETTER, STATE>> mCurrentIterator;
					{
						mHierIterator = hierPred(letter).iterator();
						nextHier();
					}

					private void nextHier() {
						if (mHierIterator.hasNext()) {
							do {
								mCurrentHier = mHierIterator.next();
								mCurrentIterator = returnSuccessors(
										mCurrentHier, letter).iterator();
							} while (!mCurrentIterator.hasNext()
									&& mHierIterator.hasNext());
							if (!mCurrentIterator.hasNext()) {
								mCurrentHier = null;
								mCurrentIterator = null;
							}
						} else {
							mCurrentHier = null;
							mCurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mCurrentHier != null;
					}

					@Override
					public OutgoingReturnTransition<LETTER, STATE> next() {
						if (mCurrentHier == null) {
							throw new NoSuchElementException();
						} else {
							final OutgoingReturnTransition<LETTER, STATE> result = 
									mCurrentIterator.next();
							if (!mCurrentIterator.hasNext()) {
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
				final Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<OutgoingReturnTransition<LETTER, STATE>> mCurrentIterator;
					{
						mLetterIterator = lettersReturn().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = returnSuccessors(mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext()
									&& mLetterIterator.hasNext());
							if (!mCurrentIterator.hasNext()) {
								mCurrentLetter = null;
								mCurrentIterator = null;
							}
						} else {
							mCurrentLetter = null;
							mCurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mCurrentLetter != null;
					}

					@Override
					public OutgoingReturnTransition<LETTER, STATE> next() {
						if (mCurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							final OutgoingReturnTransition<LETTER, STATE> result = 
									mCurrentIterator.next();
							if (!mCurrentIterator.hasNext()) {
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
				final Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator = 
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<OutgoingReturnTransition<LETTER, STATE>> mCurrentIterator;
					{
						mLetterIterator = lettersReturn().iterator();
						nextLetter();
					}

					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = returnSuccessors(
										hier, mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext()
									&& mLetterIterator.hasNext());
							if (!mCurrentIterator.hasNext()) {
								mCurrentLetter = null;
								mCurrentIterator = null;
							}
						} else {
							mCurrentLetter = null;
							mCurrentIterator = null;
						}
					}

					@Override
					public boolean hasNext() {
						return mCurrentLetter != null;
					}

					@Override
					public OutgoingReturnTransition<LETTER, STATE> next() {
						if (mCurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							final OutgoingReturnTransition<LETTER, STATE> result = 
									mCurrentIterator.next();
							if (!mCurrentIterator.hasNext()) {
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

