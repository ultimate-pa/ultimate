/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.ConcurrentProduct;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Standard implementation of the
 * #{@link de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton}
 * interface.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class NestedWordAutomaton<LETTER, STATE>
		implements INestedWordAutomatonOldApi<LETTER, STATE>,
		INestedWordAutomaton<LETTER, STATE> {
		
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private final Set<LETTER> mInternalAlphabet;
	private final Set<LETTER> mCallAlphabet;
	private final Set<LETTER> mReturnAlphabet;
	
	protected final StateFactory<STATE> mStateFactory;
	
	/**
	 * Set of internal transitions PREs x LETTERs x SUCCs stored as map PREs ->
	 * LETTERs -> SUCCs The keySet of this map is used to store the set of
	 * states of this automaton.
	 */
	private final Map<STATE, Map<LETTER, Set<STATE>>> mInternalOut =
			new HashMap<>();
			
	/**
	 * Set of internal transitions PREs x LETTERs x SUCCs stored as map SUCCs ->
	 * LETTERs -> PREs.
	 */
	private final Map<STATE, Map<LETTER, Set<STATE>>> mInternalIn =
			new HashMap<>();
			
	/**
	 * Set of call transitions PREs x LETTERs x SUCCs stored as map PREs ->
	 * LETTERs -> SUCCs.
	 */
	private final Map<STATE, Map<LETTER, Set<STATE>>> mCallOut =
			new HashMap<>();
			
	/**
	 * Set of call transitions PREs x LETTERs x SUCCs stored as map SUCCs ->
	 * LETTERs -> PREs.
	 */
	private final Map<STATE, Map<LETTER, Set<STATE>>> mCallIn =
			new HashMap<>();
			
	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as
	 * map LinPREs -> LETTERs -> HierPREs -> SUCCs.
	 */
	private final Map<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> mReturnOut =
			new HashMap<>();
			
	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as
	 * map HierPREs -> LETTERs -> LinPREs -> SUCCs.
	 */
	private final Map<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> mReturnSummary =
			new HashMap<>();
			
	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as
	 * map SUCCs -> LETTERs -> HierPREs -> LinPREs.
	 */
	private final Map<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> mReturnIn =
			new HashMap<>();
			
	private final Set<STATE> mInitialStates = new HashSet<STATE>();
	private final Set<STATE> mFinalStates = new HashSet<STATE>();
	
	protected final STATE mEmptyStackState;
	
	private final Set<LETTER> mEmptySetOfLetters = Collections.unmodifiableSet(new HashSet<LETTER>(0));
	private final Set<STATE> mEmptySetOfStates = Collections.unmodifiableSet(new HashSet<STATE>(0));
	
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param internalAlphabet
	 *            internal alphabet
	 * @param callAlphabet
	 *            call alphabet
	 * @param returnAlphabet
	 *            return alphabet
	 * @param stateFactory
	 *            state factory
	 */
	public NestedWordAutomaton(final AutomataLibraryServices services,
			final Set<LETTER> internalAlphabet, final Set<LETTER> callAlphabet, final Set<LETTER> returnAlphabet,
			final StateFactory<STATE> stateFactory) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		if (internalAlphabet == null) {
			throw new IllegalArgumentException("nwa must have internal alphabet");
		}
		if (stateFactory == null) {
			throw new IllegalArgumentException("nwa must have stateFactory");
		}
		this.mInternalAlphabet = internalAlphabet;
		this.mCallAlphabet = callAlphabet;
		this.mReturnAlphabet = returnAlphabet;
		this.mStateFactory = stateFactory;
		this.mEmptyStackState = mStateFactory.createEmptyStackState();
	}
	
	@Override
	public Set<LETTER> getInternalAlphabet() {
		return mInternalAlphabet;
	}
	
	@Override
	public Set<LETTER> getCallAlphabet() {
		return mCallAlphabet == null ? new HashSet<LETTER>(0) : mCallAlphabet;
	}
	
	@Override
	public Set<LETTER> getReturnAlphabet() {
		return mReturnAlphabet == null ? new HashSet<LETTER>(0) : mReturnAlphabet;
	}
	
	@Override
	public Set<STATE> getStates() {
		return Collections.unmodifiableSet(this.mInternalOut.keySet());
	}
	
	@Override
	public STATE getEmptyStackState() {
		return this.mEmptyStackState;
	}
	
	@Override
	public StateFactory<STATE> getStateFactory() {
		return this.mStateFactory;
	}
	
	/**
	 * @param state
	 *            state
	 * @return true iff state is in automaton
	 */
	public boolean contains(final STATE state) {
		return mInternalOut.containsKey(state);
	}
	
	@Override
	public int size() {
		return mInternalOut.size();
	}
	
	@Override
	public Set<LETTER> getAlphabet() {
		return getInternalAlphabet();
	}
	
	@Override
	public Set<STATE> getInitialStates() {
		return Collections.unmodifiableSet(mInitialStates);
	}
	
	@Override
	public boolean isInitial(final STATE state) {
		assert contains(state);
		return mInitialStates.contains(state);
	}
	
	@Override
	public boolean isFinal(final STATE state) {
		assert contains(state);
		return mFinalStates.contains(state);
	}
	
	@Override
	public Collection<STATE> getFinalStates() {
		return Collections.unmodifiableSet(mFinalStates);
	}
	
	public void addState(final boolean isInitial, final boolean isFinal, final STATE state) {
		assert (state != null);
		if (mInternalOut.containsKey(state)) {
			throw new IllegalArgumentException("State already exists");
		}
		assert (!mInternalIn.containsKey(state));
		// FIXME others
		mInternalOut.put(state, null);
		
		if (isInitial) {
			mInitialStates.add(state);
		}
		if (isFinal) {
			mFinalStates.add(state);
		}
		// FIXME remove this
		// return state;
		// assert checkTransitionsReturnedConsistent();
	}
	
	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		final Map<LETTER, Set<STATE>> map = mInternalOut.get(state);
		return map == null ? mEmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersInternalIncoming(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		final Map<LETTER, Set<STATE>> map = mInternalIn.get(state);
		return map == null ? mEmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		final Map<LETTER, Set<STATE>> map = mCallOut.get(state);
		return map == null ? mEmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersCallIncoming(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		final Map<LETTER, Set<STATE>> map = mCallIn.get(state);
		return map == null ? mEmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnOut.get(state);
		return map == null ? mEmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersReturnIncoming(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnIn.get(state);
		return map == null ? mEmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersSummary(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnSummary.get(state);
		return map == null ? mEmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<STATE> succInternal(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<LETTER, Set<STATE>> map = mInternalOut.get(state);
		if (map == null) {
			return mEmptySetOfStates;
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? mEmptySetOfStates : result;
	}
	
	@Override
	public Set<STATE> predInternal(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<LETTER, Set<STATE>> map = mInternalIn.get(state);
		if (map == null) {
			return mEmptySetOfStates;
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? mEmptySetOfStates : result;
	}
	
	@Override
	public Set<STATE> succCall(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<LETTER, Set<STATE>> map = mCallOut.get(state);
		if (map == null) {
			return mEmptySetOfStates;
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? mEmptySetOfStates : result;
	}
	
	@Override
	public Set<STATE> predCall(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<LETTER, Set<STATE>> map = mCallIn.get(state);
		if (map == null) {
			return mEmptySetOfStates;
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? mEmptySetOfStates : result;
	}
	
	@Override
	public Set<STATE> hierarchicalPredecessorsOutgoing(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnOut.get(state);
		if (map == null) {
			return mEmptySetOfStates;
		}
		final Map<STATE, Set<STATE>> hier2succs = map.get(letter);
		return hier2succs == null ? mEmptySetOfStates : hier2succs.keySet();
	}
	
	@Override
	public Set<STATE> succReturn(final STATE state, final STATE hier, final LETTER letter) {
		assert contains(state);
		assert contains(hier);
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnOut.get(state);
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
	
	private Set<STATE> predReturnLin(final STATE state, final LETTER letter, final STATE hier) {
		assert contains(state);
		assert contains(hier);
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds = mReturnIn.get(state);
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
	
	private Set<STATE> predReturnHier(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds = mReturnIn.get(state);
		if (letter2hier2preds == null) {
			return mEmptySetOfStates;
		}
		final Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		if (hier2preds == null) {
			return mEmptySetOfStates;
		}
		return hier2preds.keySet();
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier,
			final LETTER letter) {
		final Set<SummaryReturnTransition<LETTER, STATE>> result =
				new HashSet<SummaryReturnTransition<LETTER, STATE>>();
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = mReturnSummary.get(hier);
		if (letter2pred2succs == null) {
			return result;
		}
		final Map<STATE, Set<STATE>> pred2succs = letter2pred2succs.get(letter);
		if (pred2succs == null) {
			return result;
		}
		for (final Entry<STATE, Set<STATE>> entry : pred2succs.entrySet()) {
			final STATE pred = entry.getKey();
			final Set<STATE> succs = entry.getValue();
			if (succs != null) {
				for (final STATE succ : succs) {
					final SummaryReturnTransition<LETTER, STATE> srt =
							new SummaryReturnTransition<LETTER, STATE>(pred,
									letter, succ);
					result.add(srt);
				}
			}
		}
		return result;
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier) {
		return new Iterable<SummaryReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all SummaryReturnTransition of hier.
			 */
			@Override
			public Iterator<SummaryReturnTransition<LETTER, STATE>> iterator() {
				final Iterator<SummaryReturnTransition<LETTER, STATE>> iterator =
						new Iterator<SummaryReturnTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<SummaryReturnTransition<LETTER, STATE>> mCurrentIterator;
					
					{
						mLetterIterator = lettersSummary(hier).iterator();
						nextLetter();
					}
					
					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = summarySuccessors(hier, mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext() && mLetterIterator.hasNext());
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
					public SummaryReturnTransition<LETTER, STATE> next() {
						if (mCurrentLetter == null) {
							throw new NoSuchElementException();
						} else {
							final SummaryReturnTransition<LETTER, STATE> result = mCurrentIterator.next();
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
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ,
			final LETTER letter) {
		return new Iterable<IncomingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingInternalTransition<LETTER, STATE>> iterator() {
				final Iterator<IncomingInternalTransition<LETTER, STATE>> iterator =
						new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
					private Iterator<STATE> mIterator;
					
					{
						final Map<LETTER, Set<STATE>> letter2pred = mInternalIn.get(succ);
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
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ) {
		return new Iterable<IncomingInternalTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all IncomingInternalTransition of succ. Iterates
			 * over all incoming internal letters and uses the iterators
			 * returned by internalPredecessors(letter, succ)
			 */
			@Override
			public Iterator<IncomingInternalTransition<LETTER, STATE>> iterator() {
				final Iterator<IncomingInternalTransition<LETTER, STATE>> iterator =
						new Iterator<IncomingInternalTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<IncomingInternalTransition<LETTER, STATE>> mCurrentIterator;
					
					{
						mLetterIterator = lettersInternalIncoming(succ).iterator();
						nextLetter();
					}
					
					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = internalPredecessors(succ, mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext() && mLetterIterator.hasNext());
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
							final IncomingInternalTransition<LETTER, STATE> result = mCurrentIterator.next();
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
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ, final LETTER letter) {
		return new Iterable<IncomingCallTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingCallTransition<LETTER, STATE>> iterator() {
				final Iterator<IncomingCallTransition<LETTER, STATE>> iterator =
						new Iterator<IncomingCallTransition<LETTER, STATE>>() {
					private Iterator<STATE> mIterator;
					
					{
						final Map<LETTER, Set<STATE>> letter2pred = mCallIn.get(succ);
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
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ) {
		return new Iterable<IncomingCallTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all IncomingCallTransition of succ. Iterates over
			 * all incoming call letters and uses the iterators returned by
			 * callPredecessors(letter, succ)
			 */
			@Override
			public Iterator<IncomingCallTransition<LETTER, STATE>> iterator() {
				final Iterator<IncomingCallTransition<LETTER, STATE>> iterator =
						new Iterator<IncomingCallTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<IncomingCallTransition<LETTER, STATE>> mCurrentIterator;
					
					{
						mLetterIterator = lettersCallIncoming(succ).iterator();
						nextLetter();
					}
					
					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = callPredecessors(succ, mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext() && mLetterIterator.hasNext());
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
							final IncomingCallTransition<LETTER, STATE> result = mCurrentIterator.next();
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
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final STATE hier,
			final LETTER letter) {
		return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
			@Override
			public Iterator<IncomingReturnTransition<LETTER, STATE>> iterator() {
				final Iterator<IncomingReturnTransition<LETTER, STATE>> iterator =
						new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
					private Iterator<STATE> mIterator;
					
					{
						final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = mReturnIn.get(succ);
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
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final LETTER letter) {
		return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all IncomingReturnTransition of succ. Iterates over
			 * all incoming return letters and uses the iterators returned by
			 * returnPredecessors(hier, letter, succ)
			 */
			@Override
			public Iterator<IncomingReturnTransition<LETTER, STATE>> iterator() {
				final Iterator<IncomingReturnTransition<LETTER, STATE>> iterator =
						new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
					private Iterator<STATE> mHierIterator;
					private STATE mCurrentHier;
					private Iterator<IncomingReturnTransition<LETTER, STATE>> mCurrentIterator;
					
					{
						mHierIterator = predReturnHier(succ, letter).iterator();
						nextHier();
					}
					
					private void nextHier() {
						if (mHierIterator.hasNext()) {
							do {
								mCurrentHier = mHierIterator.next();
								mCurrentIterator = returnPredecessors(succ, mCurrentHier, letter).iterator();
							} while (!mCurrentIterator.hasNext() && mHierIterator.hasNext());
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
							final IncomingReturnTransition<LETTER, STATE> result = mCurrentIterator.next();
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
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ) {
		return new Iterable<IncomingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all IncomingReturnTransition of succ. Iterates over
			 * all incoming return letters and uses the iterators returned by
			 * returnPredecessors(letter, succ)
			 */
			@Override
			public Iterator<IncomingReturnTransition<LETTER, STATE>> iterator() {
				final Iterator<IncomingReturnTransition<LETTER, STATE>> iterator =
						new Iterator<IncomingReturnTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<IncomingReturnTransition<LETTER, STATE>> mCurrentIterator;
					
					{
						mLetterIterator = lettersReturnIncoming(succ).iterator();
						nextLetter();
					}
					
					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = returnPredecessors(succ, mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext() && mLetterIterator.hasNext());
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
							final IncomingReturnTransition<LETTER, STATE> result = mCurrentIterator.next();
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
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
				final Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator =
						new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
					private Iterator<STATE> mIterator;
					
					{
						final Map<LETTER, Set<STATE>> letter2succ = mInternalOut.get(state);
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
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		return new Iterable<OutgoingInternalTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingInternalTransition of state. Iterates
			 * over all outgoing internal letters and uses the iterators
			 * returned by internalSuccessors(state, letter)
			 */
			@Override
			public Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator() {
				final Iterator<OutgoingInternalTransition<LETTER, STATE>> iterator =
						new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<OutgoingInternalTransition<LETTER, STATE>> mCurrentIterator;
					
					{
						mLetterIterator = lettersInternal(state).iterator();
						nextLetter();
					}
					
					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = internalSuccessors(state, mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext() && mLetterIterator.hasNext());
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
							final OutgoingInternalTransition<LETTER, STATE> result = mCurrentIterator.next();
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
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		return new Iterable<OutgoingCallTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingCallTransition<LETTER, STATE>> iterator() {
				final Iterator<OutgoingCallTransition<LETTER, STATE>> iterator =
						new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
					private Iterator<STATE> mIterator;
					
					{
						final Map<LETTER, Set<STATE>> letter2succ = mCallOut.get(state);
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
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		return new Iterable<OutgoingCallTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingCallTransition of state. Iterates over
			 * all outgoing call letters and uses the iterators returned by
			 * callSuccessors(state, letter)
			 */
			@Override
			public Iterator<OutgoingCallTransition<LETTER, STATE>> iterator() {
				final Iterator<OutgoingCallTransition<LETTER, STATE>> iterator =
						new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<OutgoingCallTransition<LETTER, STATE>> mCurrentIterator;
					
					{
						mLetterIterator = lettersCall(state).iterator();
						nextLetter();
					}
					
					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = callSuccessors(state, mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext() && mLetterIterator.hasNext());
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
							final OutgoingCallTransition<LETTER, STATE> result = mCurrentIterator.next();
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
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			@Override
			public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
				final Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator =
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					private Iterator<STATE> mIterator;
					
					{
						final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succ = mReturnOut.get(state);
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
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final LETTER letter) {
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingReturnTransition of state. Iterates
			 * over all outgoing return letters and uses the iterators returned
			 * by returnSuccecessors(state, letter)
			 */
			@Override
			public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
				final Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator =
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					private Iterator<STATE> mHierIterator;
					private STATE mCurrentHier;
					private Iterator<OutgoingReturnTransition<LETTER, STATE>> mCurrentIterator;
					
					{
						mHierIterator = hierarchicalPredecessorsOutgoing(state, letter).iterator();
						nextHier();
					}
					
					private void nextHier() {
						if (mHierIterator.hasNext()) {
							do {
								mCurrentHier = mHierIterator.next();
								mCurrentIterator = returnSuccessors(state, mCurrentHier, letter).iterator();
							} while (!mCurrentIterator.hasNext() && mHierIterator.hasNext());
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
							final OutgoingReturnTransition<LETTER, STATE> result = mCurrentIterator.next();
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
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state) {
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingReturnTransition of state. Iterates
			 * over all outgoing return letters and uses the iterators returned
			 * by returnSuccessors(state, letter)
			 */
			@Override
			public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
				final Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator =
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<OutgoingReturnTransition<LETTER, STATE>> mCurrentIterator;
					
					{
						mLetterIterator = lettersReturn(state).iterator();
						nextLetter();
					}
					
					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = returnSuccessors(state, mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext() && mLetterIterator.hasNext());
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
							final OutgoingReturnTransition<LETTER, STATE> result = mCurrentIterator.next();
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
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		return new Iterable<OutgoingReturnTransition<LETTER, STATE>>() {
			/**
			 * Iterates over all OutgoingReturnTransition of state with
			 * hierarchical successor hier. Iterates over all outgoing return
			 * letters and uses the iterators returned by
			 * returnSuccecessors(state, hier, letter)
			 */
			@Override
			public Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator() {
				final Iterator<OutgoingReturnTransition<LETTER, STATE>> iterator =
						new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
					private Iterator<LETTER> mLetterIterator;
					private LETTER mCurrentLetter;
					private Iterator<OutgoingReturnTransition<LETTER, STATE>> mCurrentIterator;
					
					{
						mLetterIterator = lettersReturn(state).iterator();
						nextLetter();
					}
					
					private void nextLetter() {
						if (mLetterIterator.hasNext()) {
							do {
								mCurrentLetter = mLetterIterator.next();
								mCurrentIterator = returnSuccessors(state, hier, mCurrentLetter).iterator();
							} while (!mCurrentIterator.hasNext() && mLetterIterator.hasNext());
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
							final OutgoingReturnTransition<LETTER, STATE> result = mCurrentIterator.next();
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
	
	private boolean checkTransitionsReturnedConsistent() {
		boolean result = true;
		for (final STATE state : getStates()) {
			for (final IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(state)) {
				result &= containsInternalTransition(inTrans.getPred(), inTrans.getLetter(), state);
				assert result;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : internalSuccessors(state)) {
				result &= containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert result;
			}
			for (final IncomingCallTransition<LETTER, STATE> inTrans : callPredecessors(state)) {
				result &= containsCallTransition(inTrans.getPred(), inTrans.getLetter(), state);
				assert result;
			}
			for (final OutgoingCallTransition<LETTER, STATE> outTrans : callSuccessors(state)) {
				result &= containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert result;
			}
			for (final IncomingReturnTransition<LETTER, STATE> inTrans : returnPredecessors(state)) {
				result &= containsReturnTransition(inTrans.getLinPred(), inTrans.getHierPred(), inTrans.getLetter(),
						state);
				assert result;
			}
			for (final OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state)) {
				result &= containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(),
						outTrans.getSucc());
				assert result;
			}
		}
		
		return result;
	}
	
	public boolean containsInternalTransition(final STATE state, final LETTER letter, final STATE succ) {
		assert contains(state);
		final Map<LETTER, Set<STATE>> map = mInternalOut.get(state);
		if (map == null) {
			return false;
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? false : result.contains(succ);
	}
	
	public boolean containsCallTransition(final STATE state, final LETTER letter, final STATE succ) {
		assert contains(state);
		final Map<LETTER, Set<STATE>> map = mCallOut.get(state);
		if (map == null) {
			return false;
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? false : result.contains(succ);
	}
	
	public boolean containsReturnTransition(final STATE state, final STATE hier, final LETTER letter,
			final STATE succ) {
		assert contains(state);
		assert contains(hier);
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnOut.get(state);
		if (map == null) {
			return false;
		}
		final Map<STATE, Set<STATE>> hier2succs = map.get(letter);
		if (hier2succs == null) {
			return false;
		}
		final Set<STATE> result = hier2succs.get(hier);
		return result == null ? false : result.contains(succ);
	}
	
	public void makeStateNonIntial(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		if (!mInitialStates.contains(state)) {
			throw new AssertionError("Can only make initial state non-Initial");
		}
		mInitialStates.remove(state);
	}
	
	public void removeState(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		mFinalStates.remove(state);
		mInitialStates.remove(state);
		
		for (final LETTER letter : lettersCall(state)) {
			for (final STATE succ : succCall(state, letter)) {
				removeCallIn(state, letter, succ);
			}
		}
		mCallOut.remove(state);
		
		for (final LETTER letter : lettersCallIncoming(state)) {
			for (final STATE pred : predCall(state, letter)) {
				removeCallOut(pred, letter, state);
			}
		}
		mCallIn.remove(state);
		
		for (final LETTER letter : lettersReturn(state)) {
			for (final STATE hier : hierarchicalPredecessorsOutgoing(state, letter)) {
				for (final STATE succ : succReturn(state, hier, letter)) {
					removeReturnIn(state, hier, letter, succ);
					removeReturnSummary(state, hier, letter, succ);
				}
			}
		}
		mReturnOut.remove(state);
		
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = mReturnSummary.get(state);
		if (letter2pred2succs != null) {
			for (final Entry<LETTER, Map<STATE, Set<STATE>>> entry1 : letter2pred2succs.entrySet()) {
				final LETTER letter = entry1.getKey();
				final Map<STATE, Set<STATE>> pred2succs = entry1.getValue();
				if (pred2succs != null) {
					for (final Entry<STATE, Set<STATE>> entry2 : pred2succs.entrySet()) {
						final STATE pred = entry2.getKey();
						final Set<STATE> succs = entry2.getValue();
						if (succs != null) {
							for (final STATE succ : succs) {
								removeReturnIn(pred, state, letter, succ);
								removeReturnOut(pred, state, letter, succ);
							}
						}
					}
				}
			}
		}
		mReturnSummary.remove(state);
		
		for (final LETTER letter : lettersReturnIncoming(state)) {
			final Map<STATE, Set<STATE>> hier2pred = mReturnIn.get(state).get(letter);
			if (hier2pred != null) {
				for (final STATE hier : hier2pred.keySet()) {
					for (final STATE pred : predReturnLin(state, letter, hier)) {
						removeReturnOut(pred, hier, letter, state);
						removeReturnSummary(pred, hier, letter, state);
					}
				}
			}
		}
		mReturnIn.remove(state);
		
		for (final LETTER letter : lettersInternalIncoming(state)) {
			for (final STATE pred : predInternal(state, letter)) {
				removeInternalOut(pred, letter, state);
			}
		}
		mInternalIn.remove(state);
		
		for (final LETTER letter : lettersInternal(state)) {
			for (final STATE succ : succInternal(state, letter)) {
				removeInternalIn(state, letter, succ);
			}
		}
		mInternalOut.remove(state);
		
		// assert checkTransitionsStoredConsistent();
		assert checkTransitionsReturnedConsistent();
		assert sizeInformation().length() > 0;
	}
	
	private void removeInternalIn(final STATE pred, final LETTER letter, final STATE succ) {
		final Map<LETTER, Set<STATE>> letter2preds = mInternalIn.get(succ);
		final Set<STATE> preds = letter2preds.get(letter);
		assert (preds.contains(pred));
		preds.remove(pred);
		if (preds.isEmpty()) {
			letter2preds.remove(letter);
			if (letter2preds.isEmpty()) {
				mInternalIn.remove(succ);
			}
		}
	}
	
	private void removeInternalOut(final STATE pred, final LETTER letter, final STATE succ) {
		final Map<LETTER, Set<STATE>> letter2succs = mInternalOut.get(pred);
		final Set<STATE> succs = letter2succs.get(letter);
		assert (succs.contains(succ));
		succs.remove(succ);
		if (succs.isEmpty()) {
			letter2succs.remove(letter);
			if (letter2succs.isEmpty()) {
				// The keySet of mInternalOut is used to store set of states of
				// this automaton. We don't remove succ, only set image to null.
				mInternalOut.put(pred, null);
			}
		}
	}
	
	private void removeCallIn(final STATE pred, final LETTER letter, final STATE succ) {
		final Map<LETTER, Set<STATE>> letter2preds = mCallIn.get(succ);
		final Set<STATE> preds = letter2preds.get(letter);
		assert (preds.contains(pred));
		preds.remove(pred);
		if (preds.isEmpty()) {
			letter2preds.remove(letter);
			if (letter2preds.isEmpty()) {
				mCallIn.remove(succ);
			}
		}
	}
	
	private void removeCallOut(final STATE pred, final LETTER letter, final STATE succ) {
		final Map<LETTER, Set<STATE>> letter2succs = mCallOut.get(pred);
		final Set<STATE> succs = letter2succs.get(letter);
		assert (succs.contains(succ));
		succs.remove(succ);
		if (succs.isEmpty()) {
			letter2succs.remove(letter);
			if (letter2succs.isEmpty()) {
				mCallOut.remove(pred);
			}
		}
	}
	
	private void removeReturnIn(final STATE pred, final STATE hier, final LETTER letter, final STATE succ) {
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds = mReturnIn.get(succ);
		final Map<STATE, Set<STATE>> hier2preds = letter2hier2preds.get(letter);
		final Set<STATE> preds = hier2preds.get(hier);
		assert (preds.contains(pred));
		preds.remove(pred);
		if (preds.isEmpty()) {
			hier2preds.remove(hier);
			if (hier2preds.isEmpty()) {
				letter2hier2preds.remove(letter);
				if (letter2hier2preds.isEmpty()) {
					mReturnIn.remove(succ);
				}
			}
		}
	}
	
	private void removeReturnOut(final STATE pred, final STATE hier, final LETTER letter, final STATE succ) {
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succs = mReturnOut.get(pred);
		final Map<STATE, Set<STATE>> hier2succs = letter2hier2succs.get(letter);
		final Set<STATE> succs = hier2succs.get(hier);
		assert (succs.contains(succ));
		succs.remove(succ);
		if (succs.isEmpty()) {
			hier2succs.remove(hier);
			if (hier2succs.isEmpty()) {
				letter2hier2succs.remove(letter);
				if (letter2hier2succs.isEmpty()) {
					mReturnOut.remove(pred);
				}
			}
		}
	}
	
	private void removeReturnSummary(final STATE pred, final STATE hier, final LETTER letter, final STATE succ) {
		final Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = mReturnSummary.get(hier);
		final Map<STATE, Set<STATE>> pred2succs = letter2pred2succs.get(letter);
		final Set<STATE> succs = pred2succs.get(pred);
		assert (succs.contains(succ));
		succs.remove(succ);
		if (succs.isEmpty()) {
			pred2succs.remove(pred);
			if (pred2succs.isEmpty()) {
				letter2pred2succs.remove(letter);
				if (letter2pred2succs.isEmpty()) {
					mReturnSummary.remove(hier);
				}
			}
		}
	}
	
	private boolean checkTransitionsStoredConsistent() {
		boolean result = true;
		for (final Entry<STATE, Map<LETTER, Set<STATE>>> entry1 : mInternalOut.entrySet()) {
			final STATE pred = entry1.getKey();
			final Map<LETTER, Set<STATE>> letter2succs = entry1.getValue();
			if (letter2succs == null) {
				// may be null because the keySet is used to store the set of
				// all states, but some state my not have an outgoing internal
				// transition
				continue;
			}
			assert !letter2succs.isEmpty();
			for (final Entry<LETTER, Set<STATE>> entry2 : letter2succs.entrySet()) {
				final LETTER letter = entry2.getKey();
				final Set<STATE> succs = entry2.getValue();
				assert !succs.isEmpty();
				for (final STATE succ : succs) {
					assert (mInternalIn.get(succ).get(letter).contains(pred));
					if (!mInternalIn.get(succ).get(letter).contains(pred)) {
						result = false;
					}
				}
			}
		}
		for (final Entry<STATE, Map<LETTER, Set<STATE>>> entry1 : mInternalIn.entrySet()) {
			final STATE succ = entry1.getKey();
			final Map<LETTER, Set<STATE>> letter2preds = entry1.getValue();
			assert !letter2preds.isEmpty();
			for (final Entry<LETTER, Set<STATE>> entry2 : letter2preds.entrySet()) {
				final LETTER letter = entry2.getKey();
				final Set<STATE> preds = entry2.getValue();
				assert !preds.isEmpty();
				for (final STATE pred : preds) {
					assert (mInternalOut.get(pred).get(letter).contains(succ));
					if (!mInternalOut.get(pred).get(letter).contains(succ)) {
						result = false;
					}
				}
			}
		}
		for (final Entry<STATE, Map<LETTER, Set<STATE>>> entry1 : mCallOut.entrySet()) {
			final STATE pred = entry1.getKey();
			final Map<LETTER, Set<STATE>> letter2succs = entry1.getValue();
			assert !letter2succs.isEmpty();
			for (final Entry<LETTER, Set<STATE>> entry2 : letter2succs.entrySet()) {
				final LETTER letter = entry2.getKey();
				final Set<STATE> succs = entry2.getValue();
				assert !succs.isEmpty();
				for (final STATE succ : succs) {
					assert (mCallIn.get(succ).get(letter).contains(pred));
					if (!mCallIn.get(succ).get(letter).contains(pred)) {
						result = false;
					}
				}
			}
		}
		for (final Entry<STATE, Map<LETTER, Set<STATE>>> entry1 : mCallIn.entrySet()) {
			final STATE succ = entry1.getKey();
			final Map<LETTER, Set<STATE>> letter2preds = entry1.getValue();
			assert !letter2preds.isEmpty();
			for (final Entry<LETTER, Set<STATE>> entry2 : letter2preds.entrySet()) {
				final LETTER letter = entry2.getKey();
				final Set<STATE> preds = entry2.getValue();
				assert !preds.isEmpty();
				for (final STATE pred : preds) {
					assert (mCallOut.get(pred).get(letter).contains(succ));
					if (!mCallOut.get(pred).get(letter).contains(succ)) {
						result = false;
					}
				}
			}
		}
		for (final Entry<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> entry1 : mReturnOut.entrySet()) {
			final STATE pred = entry1.getKey();
			final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succs = entry1.getValue();
			assert !letter2hier2succs.isEmpty();
			for (final Entry<LETTER, Map<STATE, Set<STATE>>> entry2 : letter2hier2succs.entrySet()) {
				final LETTER letter = entry2.getKey();
				final Map<STATE, Set<STATE>> hier2succs = entry2.getValue();
				assert !hier2succs.isEmpty();
				for (final Entry<STATE, Set<STATE>> entry3 : hier2succs.entrySet()) {
					final STATE hier = entry3.getKey();
					final Set<STATE> succs = entry3.getValue();
					assert !succs.isEmpty();
					for (final STATE succ : succs) {
						assert mReturnIn.get(succ).get(letter).get(hier).contains(pred);
						assert mReturnSummary.get(hier).get(letter).get(pred).contains(succ);
						if (!mReturnIn.get(succ).get(letter).get(hier).contains(pred)) {
							result = false;
						}
						if (!mReturnSummary.get(hier).get(letter).get(pred).contains(succ)) {
							result = false;
						}
					}
				}
			}
		}
		for (final Entry<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> entry : mReturnIn.entrySet()) {
			final STATE succ = entry.getKey();
			final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = entry.getValue();
			assert !letter2hier2pred.isEmpty();
			for (final Entry<LETTER, Map<STATE, Set<STATE>>> entry1 : letter2hier2pred.entrySet()) {
				final LETTER letter = entry1.getKey();
				final Map<STATE, Set<STATE>> hier2preds = entry1.getValue();
				assert !hier2preds.isEmpty();
				for (final Entry<STATE, Set<STATE>> entry2 : hier2preds.entrySet()) {
					final STATE hier = entry2.getKey();
					final Set<STATE> preds = entry2.getValue();
					assert !preds.isEmpty();
					for (final STATE pred : preds) {
						assert mReturnOut.get(pred).get(letter).get(hier).contains(succ);
						assert mReturnSummary.get(hier).get(letter).get(pred).contains(succ);
						if (!mReturnOut.get(pred).get(letter).get(hier).contains(succ)) {
							result = false;
						}
						if (!mReturnSummary.get(hier).get(letter).get(pred).contains(succ)) {
							result = false;
						}
					}
				}
			}
		}
		for (final Entry<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> entry1 : mReturnSummary.entrySet()) {
			final STATE hier = entry1.getKey();
			final Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = entry1.getValue();
			assert !letter2pred2succs.isEmpty();
			
			for (final Entry<LETTER, Map<STATE, Set<STATE>>> entry2 : letter2pred2succs.entrySet()) {
				final LETTER letter = entry2.getKey();
				final Map<STATE, Set<STATE>> pred2succs = entry2.getValue();
				assert !pred2succs.isEmpty();
				for (final Entry<STATE, Set<STATE>> entry3 : pred2succs.entrySet()) {
					final STATE pred = entry3.getKey();
					final Set<STATE> succs = entry3.getValue();
					assert !succs.isEmpty();
					for (final STATE succ : succs) {
						assert mReturnOut.get(pred).get(letter).get(hier).contains(succ);
						assert mReturnIn.get(succ).get(letter).get(hier).contains(pred);
						if (!mReturnOut.get(pred).get(letter).get(hier).contains(succ)) {
							result = false;
						}
						if (!mReturnIn.get(succ).get(letter).get(hier).contains(pred)) {
							result = false;
						}
					}
				}
			}
		}
		return result;
	}
	
	private int numberIncomingInternalTransitions(final STATE state) {
		int result = 0;
		for (final IncomingInternalTransition<LETTER, STATE> inTrans : internalPredecessors(state)) {
			result++;
		}
		return result;
	}
	
	private int numberIncomingCallTransitions(final STATE state) {
		int result = 0;
		for (final IncomingCallTransition<LETTER, STATE> caTrans : callPredecessors(state)) {
			result++;
		}
		return result;
	}
	
	private int numberIncomingReturnTransitions(final STATE state) {
		int result = 0;
		for (final IncomingReturnTransition<LETTER, STATE> reTrans : returnPredecessors(state)) {
			result++;
		}
		return result;
	}
	
	@Override
	public String sizeInformation() {
		final boolean verbose = false;
		if (!verbose) {
			final int states = mInternalOut.size();
			return states + " states.";
		}
		int statesWithInternalSuccessors = 0;
		int internalSuccessors = 0;
		for (final Entry<STATE, Map<LETTER, Set<STATE>>> entry1 : mInternalOut.entrySet()) {
			final Map<LETTER, Set<STATE>> letter2succs = entry1.getValue();
			if (letter2succs == null) {
				// may be null because the keySet is used to store the set of
				// all states, but some state my not have an outgoing internal
				// transition
				continue;
			}
			statesWithInternalSuccessors++;
			for (final Entry<LETTER, Set<STATE>> entry2 : letter2succs.entrySet()) {
				final Set<STATE> succs = entry2.getValue();
				internalSuccessors += succs.size();
			}
		}
		int statesWithInternalPredecessors = 0;
		int internalPredecessors = 0;
		for (final Entry<STATE, Map<LETTER, Set<STATE>>> entry1 : mInternalIn.entrySet()) {
			final STATE succ = entry1.getKey();
			final Map<LETTER, Set<STATE>> letter2preds = entry1.getValue();
			int internalPredOfSucc = 0;
			statesWithInternalPredecessors++;
			for (final Entry<LETTER, Set<STATE>> entry2 : letter2preds.entrySet()) {
				final Set<STATE> preds = entry2.getValue();
				internalPredOfSucc += preds.size();
			}
			assert (internalPredOfSucc == numberIncomingInternalTransitions(succ));
			internalPredecessors += internalPredOfSucc;
		}
		int statesWithCallSuccessors = 0;
		int callSuccessors = 0;
		for (final Entry<STATE, Map<LETTER, Set<STATE>>> entry1 : mCallOut.entrySet()) {
			statesWithCallSuccessors++;
			final Map<LETTER, Set<STATE>> letter2succs = entry1.getValue();
			for (final Entry<LETTER, Set<STATE>> entry2 : letter2succs.entrySet()) {
				final Set<STATE> succs = entry2.getValue();
				callSuccessors += succs.size();
			}
		}
		int statesWithCallPredecessors = 0;
		int callPredecessors = 0;
		for (final Entry<STATE, Map<LETTER, Set<STATE>>> entry1 : mCallIn.entrySet()) {
			final STATE succ = entry1.getKey();
			statesWithCallPredecessors++;
			int callPredOfSucc = 0;
			final Map<LETTER, Set<STATE>> letter2preds = entry1.getValue();
			for (final Entry<LETTER, Set<STATE>> entry2 : letter2preds.entrySet()) {
				final Set<STATE> preds = entry2.getValue();
				callPredOfSucc += preds.size();
			}
			assert (callPredOfSucc == numberIncomingCallTransitions(succ));
			callPredecessors += callPredOfSucc;
			
		}
		int statesWithReturnSuccessor = 0;
		int returnSuccessors = 0;
		for (final Entry<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> entry1 : mReturnOut.entrySet()) {
			final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succs = entry1.getValue();
			statesWithReturnSuccessor++;
			for (final Entry<LETTER, Map<STATE, Set<STATE>>> entry2 : letter2hier2succs.entrySet()) {
				final Map<STATE, Set<STATE>> hier2succs = entry2.getValue();
				for (final Entry<STATE, Set<STATE>> entry3 : hier2succs.entrySet()) {
					final Set<STATE> succs = entry3.getValue();
					returnSuccessors += succs.size();
				}
			}
		}
		int statesWithReturnLinearPredecessors = 0;
		int returnLinearPredecessors = 0;
		for (final Entry<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> entry1 : mReturnIn.entrySet()) {
			final STATE succ = entry1.getKey();
			final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2pred = entry1.getValue();
			statesWithReturnLinearPredecessors++;
			int returnLinPredOfSucc = 0;
			for (final Entry<LETTER, Map<STATE, Set<STATE>>> entry2 : letter2hier2pred.entrySet()) {
				final Map<STATE, Set<STATE>> hier2preds = entry2.getValue();
				for (final Entry<STATE, Set<STATE>> entry3 : hier2preds.entrySet()) {
					final Set<STATE> preds = entry3.getValue();
					returnLinPredOfSucc += preds.size();
				}
			}
			assert (returnLinPredOfSucc == numberIncomingReturnTransitions(succ));
			returnLinearPredecessors += returnLinPredOfSucc;
		}
		int statesWithReturnHierarchicalSuccessor = 0;
		int returnHierarchicalSuccessors = 0;
		for (final Entry<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> entry1 : mReturnSummary.entrySet()) {
			final Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = entry1.getValue();
			statesWithReturnHierarchicalSuccessor++;
			for (final Entry<LETTER, Map<STATE, Set<STATE>>> entry2 : letter2pred2succs.entrySet()) {
				final Map<STATE, Set<STATE>> pred2succs = entry2.getValue();
				for (final Entry<STATE, Set<STATE>> entry3 : pred2succs.entrySet()) {
					final Set<STATE> succs = entry3.getValue();
					returnHierarchicalSuccessors += succs.size();
				}
			}
		}
		final StringBuilder sb = new StringBuilder();
		sb.append(" has ").append(mInternalOut.size()).append(" states, " + statesWithInternalSuccessors)
				.append(" states have internal successors, (").append(internalSuccessors).append("), ")
				.append(statesWithInternalPredecessors).append(" states have internal predecessors, (")
				.append(internalPredecessors).append("), ").append(
						
						statesWithCallSuccessors)
				.append(" states have call successors, (").append(callSuccessors)
				.append("), ").append(statesWithCallPredecessors).append(" states have call predecessors, (")
				.append(callPredecessors).append("), ").append(
						
						statesWithReturnSuccessor)
				.append(" states have return successors, (").append(returnSuccessors)
				.append("), ").append(statesWithReturnLinearPredecessors).append(" states have call predecessors, (")
				.append(returnLinearPredecessors).append("), " + statesWithReturnHierarchicalSuccessor)
				.append(" states have call successors, (").append(returnHierarchicalSuccessors).append(")");
		return sb.toString();
		
		// return " has " + mInternalOut.size() + " states, " +
		// statesWithInternalSuccessors + " states have internal successors, ("
		// + internalSuccessors + "), " +
		// statesWithInternalPredecessors +
		// " states have internal predecessors, (" + internalPredecessors +
		// "), " +
		//
		// statesWithCallSuccessors + " states have call successors, (" +
		// callSuccessors + "), " +
		// statesWithCallPredecessors + " states have call predecessors, (" +
		// callPredecessors + "), " +
		//
		// statesWithReturnSuccessor + " states have return successors, (" +
		// returnSuccessors + "), " +
		// statesWithReturnLinearPredecessors +
		// " states have call predecessors, (" + returnLinearPredecessors +
		// "), " +
		// statesWithReturnHierarchicalSuccessor +
		// " states have call successors, (" + returnHierarchicalSuccessors +
		// ")";
	}
	
	public void addInternalTransition(final STATE pred, final LETTER letter, final STATE succ) {
		if (!mInternalAlphabet.contains(letter)) {
			throw new IllegalArgumentException("Letter " + letter + " not in internal alphabet");
		}
		if (!contains(pred)) {
			throw new IllegalArgumentException("State " + pred + " not in automaton");
		}
		assert contains(pred) : "State " + pred + " not in automaton";
		assert contains(succ) : "State " + succ + " not in automaton";
		Map<LETTER, Set<STATE>> letter2succs = mInternalOut.get(pred);
		if (letter2succs == null) {
			letter2succs = new HashMap<LETTER, Set<STATE>>();
			mInternalOut.put(pred, letter2succs);
		}
		Set<STATE> succs = letter2succs.get(letter);
		if (succs == null) {
			succs = new HashSet<STATE>();
			letter2succs.put(letter, succs);
		}
		succs.add(succ);
		
		Map<LETTER, Set<STATE>> letter2preds = mInternalIn.get(succ);
		if (letter2preds == null) {
			letter2preds = new HashMap<LETTER, Set<STATE>>();
			mInternalIn.put(succ, letter2preds);
		}
		Set<STATE> preds = letter2preds.get(letter);
		if (preds == null) {
			preds = new HashSet<STATE>();
			letter2preds.put(letter, preds);
		}
		preds.add(pred);
		// assert checkTransitionsStoredConsistent();
	}
	
	public void addCallTransition(final STATE pred, final LETTER letter, final STATE succ) {
		if (!mCallAlphabet.contains(letter)) {
			throw new IllegalArgumentException("Letter " + letter + " not in call alphabet");
		}
		
		assert contains(pred) : "State " + pred + " not in automaton";
		assert contains(succ) : "State " + succ + " not in automaton";
		Map<LETTER, Set<STATE>> letter2succs = mCallOut.get(pred);
		if (letter2succs == null) {
			letter2succs = new HashMap<LETTER, Set<STATE>>();
			mCallOut.put(pred, letter2succs);
		}
		Set<STATE> succs = letter2succs.get(letter);
		if (succs == null) {
			succs = new HashSet<STATE>();
			letter2succs.put(letter, succs);
		}
		succs.add(succ);
		
		Map<LETTER, Set<STATE>> letter2preds = mCallIn.get(succ);
		if (letter2preds == null) {
			letter2preds = new HashMap<LETTER, Set<STATE>>();
			mCallIn.put(succ, letter2preds);
		}
		Set<STATE> preds = letter2preds.get(letter);
		if (preds == null) {
			preds = new HashSet<STATE>();
			letter2preds.put(letter, preds);
		}
		preds.add(pred);
		// assert checkTransitionsStoredConsistent();
	}
	
	public void addReturnTransition(final STATE pred, final STATE hier, final LETTER letter, final STATE succ) {
		if (!mReturnAlphabet.contains(letter)) {
			throw new IllegalArgumentException("Letter " + letter + " not in return alphabet");
		}
		assert contains(pred) : "State " + pred + " not in automaton";
		assert contains(succ) : "State " + succ + " not in automaton";
		assert contains(hier) : "State " + hier + " not in automaton";
		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succs = mReturnOut.get(pred);
		if (letter2hier2succs == null) {
			letter2hier2succs = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
			mReturnOut.put(pred, letter2hier2succs);
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
		
		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2preds = mReturnIn.get(succ);
		if (letter2hier2preds == null) {
			letter2hier2preds = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
			mReturnIn.put(succ, letter2hier2preds);
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
		
		Map<LETTER, Map<STATE, Set<STATE>>> letter2pred2succs = mReturnSummary.get(hier);
		if (letter2pred2succs == null) {
			letter2pred2succs = new HashMap<LETTER, Map<STATE, Set<STATE>>>();
			mReturnSummary.put(hier, letter2pred2succs);
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
	
	// @Deprecated
	// public NestedWordAutomaton(INestedWordAutomaton<LETTER,STATE> nwa,
	// boolean totalize,
	// boolean complement) {
	// if (totalize && nwa.isTotal()) {
	// throw new IllegalArgumentException(
	// "Automaton is already total");
	// }
	// if (totalize && !nwa.isDeterministic()) {
	// throw new IllegalArgumentException(
	// "I only totalize deterministic NWAs");
	// }
	// if (complement && !(totalize || nwa.isTotal()) ) {
	// throw new IllegalArgumentException(
	// "I only complement total NWAs");
	// }
	// this.mInternalAlphabet = new HashSet<LETTER>();
	// this.mInternalAlphabet.addAll(nwa.getInternalAlphabet());
	// this.mCallAlphabet = new HashSet<LETTER>();
	// this.mCallAlphabet.addAll(nwa.getCallAlphabet());
	// this.mReturnAlphabet = new HashSet<LETTER>();
	// this.mReturnAlphabet.addAll(nwa.getReturnAlphabet());
	// this.mcontentFactory = nwa.getStateFactory();
	//
	// this.states = new HashSet<IAuxiliaryStateContainer<LETTER,STATE>>();
	// this.initialStates = new
	// HashSet<IAuxiliaryStateContainer<LETTER,STATE>>();
	// this.finalStates = new HashSet<IAuxiliaryStateContainer<LETTER,STATE>>();
	//
	// this.emptyStackContent = mcontentFactory.createEmptyStackContent();
	// this.emptyStackState = new AuxiliaryStateContainer<LETTER,STATE>(false,
	// this.emptyStackContent, mConstructedStates++);
	// assert(isFinalStoredConsistent((NestedWordAutomaton<LETTER, STATE>)
	// nwa));
	//
	//
	//
	// for (STATE state : nwa.states()) {
	// boolean isInitial = nwa.getInitial().contains(state);
	// boolean isFinal;
	// if (complement) {
	// isFinal = !nwa.isFinal(state);
	// }
	// else {
	// isFinal = nwa.isFinal(state);
	// }
	// this.addContent(isInitial, isFinal, state);
	// }
	// STATE sink = mcontentFactory.createSinkStateContent();
	// //don't add sink state if automaton is already total
	// if (totalize) {
	// // sinkState is initial if automaton does not have initial states
	// boolean isInitial = this.initialStates.isEmpty();
	// this.addContent(isInitial, complement, sink);
	// }
	//
	// for (STATE state : this.states()) {
	//
	// for (LETTER symbol : this.getInternalAlphabet()) {
	// if (state == sink) {
	// this.addInternalTransition(state, symbol, sink);
	// }
	// else {
	// Collection<STATE> succs = nwa.succInternal(state, symbol);
	// assert (!totalize || succs.size() <= 1);
	// for (STATE succ : succs) {
	// this.addInternalTransition(state, symbol, succ);
	// }
	// if (totalize && succs.isEmpty()) {
	// this.addInternalTransition(state, symbol, sink);
	// }
	// }
	// }
	//
	// for (LETTER symbol : this.getCallAlphabet()) {
	// if (state == sink) {
	// this.addCallTransition(state, symbol, sink);
	// }
	// else {
	// Collection<STATE> succs = nwa.succCall(state, symbol);
	// assert (!totalize || succs.size() <= 1);
	// for (STATE succ : succs) {
	// this.addCallTransition(state, symbol, succ);
	// }
	// if (totalize && succs.isEmpty()) {
	// this.addCallTransition(state, symbol, sink);
	// }
	// }
	// }
	//
	// for (LETTER symbol : this.getReturnAlphabet()) {
	// for (STATE hier : this.states()) {
	// if (state == sink) {
	// this.addReturnTransition(state, hier, symbol, sink);
	// }
	// else if (hier == sink) {
	// this.addReturnTransition(state, hier, symbol, sink);
	// }
	// else {
	// Collection<STATE> succs = nwa.succReturn(state, hier, symbol);
	// assert (!totalize || succs.size() <= 1);
	// for (STATE succ : succs) {
	// this.addReturnTransition(state, hier, symbol, succ);
	// }
	// if (totalize && succs.isEmpty()) {
	// this.addReturnTransition(state, hier, symbol, sink);
	// }
	// }
	// }
	// }
	//
	// }
	// }
	
	/**
	 * Return true iff this automaton is deterministic.
	 */
	@Override
	public boolean isDeterministic() {
		if (getInitialStates().size() > 1) {
			return false;
		}
		for (final STATE state : this.getStates()) {
			for (final LETTER symbol : lettersInternal(state)) {
				if (succInternal(state, symbol).size() > 1) {
					return false;
				}
			}
			for (final LETTER symbol : lettersCall(state)) {
				if (succCall(state, symbol).size() > 1) {
					return false;
				}
			}
			for (final LETTER symbol : lettersReturn(state)) {
				for (final STATE hier : hierarchicalPredecessorsOutgoing(state, symbol)) {
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
		if (getInitialStates().size() < 1) {
			return false;
		}
		for (final STATE state : this.getStates()) {
			for (final LETTER symbol : getInternalAlphabet()) {
				if (succInternal(state, symbol).size() < 1) {
					return false;
				}
			}
			for (final LETTER symbol : getCallAlphabet()) {
				if (succCall(state, symbol).size() < 1) {
					return false;
				}
			}
			for (final LETTER symbol : getReturnAlphabet()) {
				for (final STATE hier : getStates()) {
					if (succReturn(state, hier, symbol).size() < 1) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	@Deprecated
	public NestedRun<LETTER, STATE> getAcceptingNestedRun() throws AutomataLibraryException {
		final NestedRun<LETTER, STATE> result = (new IsEmpty<LETTER, STATE>(mServices, this).getNestedRun());
		return result;
	}
	
	/**
	 * Maximize set of accepting states.
	 */
	public void buchiClosure() {
		mLogger.info("Accepting states before buchiClosure: " + getFinalStates().size());
		final Set<STATE> worklist = new HashSet<STATE>();
		worklist.addAll(getFinalStates());
		while (!worklist.isEmpty()) {
			final STATE state = worklist.iterator().next();
			worklist.remove(state);
			if (!getFinalStates().contains(state)) {
				if (allSuccessorsAccepting(state)) {
					makeStateAccepting(state);
				} else {
					continue;
				}
			}
			for (final LETTER symbol : lettersInternalIncoming(state)) {
				for (final STATE succ : predInternal(state, symbol)) {
					if (!getFinalStates().contains(succ)) {
						worklist.add(succ);
					}
				}
			}
			for (final LETTER symbol : lettersCall(state)) {
				for (final STATE succ : succCall(state, symbol)) {
					if (!getFinalStates().contains(succ)) {
						worklist.add(succ);
					}
				}
			}
			for (final LETTER symbol : lettersReturn(state)) {
				for (final STATE hier : hierarchicalPredecessorsOutgoing(state, symbol)) {
					for (final STATE succ : succReturn(state, hier, symbol)) {
						if (!getFinalStates().contains(succ)) {
							worklist.add(succ);
						}
					}
				}
			}
		}
		mLogger.info("Accepting states after buchiClosure: " + getFinalStates().size());
	}
	
	/**
	 * Return true iff all successors of state state are accepting states.
	 */
	private boolean allSuccessorsAccepting(final STATE state) {
		for (final LETTER symbol : lettersInternal(state)) {
			for (final STATE succ : succInternal(state, symbol)) {
				if (!getFinalStates().contains(succ)) {
					return false;
				}
			}
		}
		for (final LETTER symbol : lettersCall(state)) {
			for (final STATE succ : succCall(state, symbol)) {
				if (!getFinalStates().contains(succ)) {
					return false;
				}
			}
		}
		for (final LETTER symbol : lettersReturn(state)) {
			for (final STATE hier : hierarchicalPredecessorsOutgoing(state, symbol)) {
				for (final STATE succ : succReturn(state, hier, symbol)) {
					if (!getFinalStates().contains(succ)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	/**
	 * Change status of state from non-accepting to accepting.
	 */
	private void makeStateAccepting(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException("State " + state + " unknown");
		}
		if (isFinal(state)) {
			throw new IllegalArgumentException("state " + state + " already final");
		}
		mFinalStates.add(state);
	}
	
	public INestedWordAutomaton<LETTER, STATE> concurrentProduct(final INestedWordAutomaton<LETTER, STATE> nwa) {
		return (new ConcurrentProduct<LETTER, STATE>(mServices, this, nwa, false)).getResult();
	}
	
	public INestedWordAutomaton<LETTER, STATE> concurrentPrefixProduct(
			final INestedWordAutomaton<LETTER, STATE> nwa) {
		return (new ConcurrentProduct<LETTER, STATE>(mServices, this, nwa, true)).getResult();
	}
	
	/**
	 * @return true iff the language of this automaton is closed under
	 *         concatenation with sigma star.
	 */
	@Override
	@Deprecated
	public boolean finalIsTrap() {
		if (!this.getCallAlphabet().isEmpty()) {
			throw new UnsupportedOperationException("only finite automata supported");
		}
		if (!this.getReturnAlphabet().isEmpty()) {
			throw new UnsupportedOperationException("only finite automata supported");
		}
		
		for (final STATE finalState : mFinalStates) {
			for (final LETTER symbol : this.getInternalAlphabet()) {
				final Collection<STATE> succs = succInternal(finalState, symbol);
				if (succs.isEmpty()) {
					return false;
				}
				for (final STATE succ : succs) {
					if (!isFinal(succ)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	public int numberOfOutgoingInternalTransitions(final STATE state) {
		int result = 0;
		for (final LETTER letter : lettersInternal(state)) {
			for (final STATE succ : succInternal(state, letter)) {
				result++;
			}
		}
		return result;
	}
	
	public int numberOfIncomingInternalTransitions(final STATE state) {
		int result = 0;
		for (final LETTER letter : lettersInternalIncoming(state)) {
			for (final STATE pred : predInternal(state, letter)) {
				result++;
			}
		}
		return result;
	}
	
	public static <LETTER, STATE> boolean sameAlphabet(final INestedWordAutomatonSimple<LETTER, STATE> nwa1,
			final INestedWordAutomatonSimple<LETTER, STATE> nwa2) {
		boolean result = true;
		result = result && nwa1.getInternalAlphabet().equals(nwa2.getInternalAlphabet());
		result = result && nwa1.getCallAlphabet().equals(nwa2.getCallAlphabet());
		result = result && nwa1.getReturnAlphabet().equals(nwa2.getReturnAlphabet());
		return result;
	}
	
	// public InternalTransitions
	// getInternalTransitions(IAuxiliaryStateContainer<LETTER,STATE> state,
	// LETTER symbol) {
	// return new InternalTransitions(state, symbol);
	// }
	//
	// public InternalTransitions
	// getInternalTransitions(IAuxiliaryStateContainer<LETTER,STATE> state) {
	// return new InternalTransitions(state);
	// }
	//
	// public InternalTransitions getInternalTransitions() {
	// return new InternalTransitions();
	// }
	//
	//
	// public class InternalTransition {
	// private final IAuxiliaryStateContainer<LETTER,STATE> predecessor;
	// private final LETTER symbol;
	// private final IAuxiliaryStateContainer<LETTER,STATE> successor;
	//
	// public InternalTransition(IAuxiliaryStateContainer<LETTER,STATE>
	// predecessor,
	// LETTER symbol,
	// IAuxiliaryStateContainer<LETTER,STATE> successor) {
	// this.predecessor = predecessor;
	// this.symbol = symbol;
	// this.successor = successor;
	// }
	//
	// public IAuxiliaryStateContainer<LETTER,STATE> getPredecessor() {
	// return predecessor;
	// }
	//
	// public LETTER getSymbol() {
	// return symbol;
	// }
	//
	// public IAuxiliaryStateContainer<LETTER,STATE> getSuccessor() {
	// return successor;
	// }
	//
	// public String toString() {
	// return "( " + predecessor + " , " + symbol + " , " +
	// successor + " )";
	// }
	// }
	
	// public class InternalTransitions implements Iterable<InternalTransition>
	// {
	// private final boolean fixedPredecessor;
	// private IAuxiliaryStateContainer<LETTER,STATE> predecessor;
	// private final boolean fixedSymbol;
	// private LETTER symbol;
	//
	// public InternalTransitions(IAuxiliaryStateContainer<LETTER,STATE> state,
	// LETTER symbol) {
	// fixedPredecessor = true;
	// this.predecessor = state;
	// fixedSymbol = true;
	// this.symbol = symbol;
	// }
	//
	// public InternalTransitions(IAuxiliaryStateContainer<LETTER,STATE> state)
	// {
	// fixedPredecessor = true;
	// this.predecessor = state;
	// fixedSymbol = false;
	// }
	//
	// public InternalTransitions() {
	// fixedPredecessor = false;
	// fixedSymbol = false;
	// }
	//
	//
	// @Override
	// public Iterator<InternalTransition> iterator() {
	// return new InternalTransitionIterator();
	// }
	//
	// public class InternalTransitionIterator implements
	// Iterator<InternalTransition> {
	//
	// public Iterator<IAuxiliaryStateContainer<LETTER, STATE>> predIterator;
	// private Iterator<LETTER> symbolIterator;
	// private Iterator<IAuxiliaryStateContainer<LETTER,STATE>> succIterator;
	//
	// private boolean finished = false;
	//
	//
	//
	// public InternalTransitionIterator() {
	// if (fixedSymbol) {
	// assert (fixedPredecessor);
	// predIterator = null;
	// symbolIterator = null;
	// succIterator = predecessor.getInternalSucc(symbol).iterator();
	// assert (succIterator != null);
	// }
	// else {
	// if (fixedPredecessor) {
	// predIterator = null;
	// symbolIterator = predecessor.getSymbolsInternal().iterator();
	// assert (symbolIterator != null);
	// updateSuccIterator();
	// while (!finished && !succIterator.hasNext()) {
	// updateSymbolIterator();
	// }
	// }
	// else {
	// predIterator = getAllStates().iterator();
	// updateSymbolIterator();
	// updateSuccIterator();
	// while (!finished && !succIterator.hasNext()) {
	// updateSymbolIterator();
	// }
	// }
	// }
	// }
	//
	//
	//
	// private void updateSuccIterator(){
	// if (fixedSymbol) {
	// this.finished = true;
	// return;
	// }
	// else {
	// while (!finished && !symbolIterator.hasNext() ) {
	// updateSymbolIterator();
	// }
	// if (this.finished) {
	// return;
	// }
	// else {
	// assert (symbolIterator.hasNext());
	// symbol = symbolIterator.next();
	// succIterator = predecessor.getInternalSucc(symbol).iterator();
	// }
	// }
	// }
	//
	// private void updateSymbolIterator() {
	// if (fixedPredecessor) {
	// this.finished = true;
	// return;
	// }
	// else {
	// if (predIterator.hasNext()) {
	// predecessor = predIterator.next();
	// symbolIterator = predecessor.getSymbolsInternal().iterator();
	// }
	// else {
	// this.finished = true;
	// }
	// }
	// }
	//
	// @Override
	// public boolean hasNext() {
	// if (finished) {
	// return false;
	// }
	// else {
	// return succIterator.hasNext();
	// }
	//
	// }
	//
	// @Override
	// public InternalTransition next() {
	// IAuxiliaryStateContainer<LETTER,STATE> succ = succIterator.next();
	// InternalTransition result =
	// new InternalTransition(predecessor, symbol, succ);
	// while (!finished && !succIterator.hasNext()) {
	// updateSuccIterator();
	// }
	// return result;
	// }
	//
	// @Override
	// public void remove() {
	// throw new UnsupportedOperationException();
	// }
	//
	// }
	//
	// }
	
	@Override
	public String toString() {
		return (new AutomatonDefinitionPrinter<String, String>(mServices, "nwa", Format.ATS, this))
				.getDefinitionAsString();
	}
	
	/**
	 * Given a nested word (without pending returns) a_0,...,a_n and a sequence
	 * of states q_0,...,q_{n+1}, add for each i
	 * <ul>
	 * <li>the internal transition (q_i, a_i, a_{i+1}) if i is an internal
	 * position,
	 * <li>the call transition (q_i, a_i, a_{i+1}) if i is a call position, and
	 * <li>the return transition (q_i, q_k, a_i, a_{i+1}) where k is the
	 * corresponding call position. Expects that all symbols are contained in
	 * the alphabets and the all states are contained in the automaton.
	 * </ul>
	 */
	public void addTransitions(final NestedWord<LETTER> nw, final List<STATE> stateList) {
		assert nw.length() + 1 == stateList.size();
		for (int i = 0; i < nw.length(); i++) {
			final LETTER symbol = nw.getSymbol(i);
			final STATE pred = stateList.get(i);
			final STATE succ = stateList.get(i + 1);
			
			if (nw.isCallPosition(i)) {
				addCallTransition(pred, symbol, succ);
			} else if (nw.isReturnPosition(i)) {
				assert !nw.isPendingReturn(i);
				final int callPos = nw.getCallPosition(i);
				final STATE hierPred = stateList.get(callPos);
				addReturnTransition(pred, hierPred, symbol, succ);
			} else {
				assert nw.isInternalPosition(i);
				addInternalTransition(pred, symbol, succ);
			}
		}
	}
}
