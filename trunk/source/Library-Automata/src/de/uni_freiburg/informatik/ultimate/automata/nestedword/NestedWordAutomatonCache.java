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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter.Format;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * undocumented!
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class NestedWordAutomatonCache<LETTER, STATE> implements INestedWordAutomatonSimple<LETTER, STATE> {
	private static final String STATE = "State ";
	private static final String NOT_IN_AUTOMATON = " not in automaton";
	private static final String UNKNOWN = " unknown";
	
	protected final IStateFactory<STATE> mStateFactory;
	
	protected final STATE mEmptyStackState;
	
	protected Set<LETTER> mEmptySetOfLetters = Collections.unmodifiableSet(new HashSet<LETTER>(0));
	protected Set<STATE> mEmptySetOfStates = Collections.unmodifiableSet(new HashSet<STATE>(0));
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private final Set<LETTER> mInternalAlphabet;
	private final Set<LETTER> mCallAlphabet;
	private final Set<LETTER> mReturnAlphabet;
	
	/**
	 * Set of internal transitions PREs x LETTERs x SUCCs stored as map
	 * PREs -> LETTERs -> SUCCs.
	 * The keySet of this map is used to store the set of states of this
	 * automaton.
	 */
	private final Map<STATE, Map<LETTER, Set<STATE>>> mInternalOut = new HashMap<>();
	
	/**
	 * Set of call transitions PREs x LETTERs x SUCCs stored as map
	 * PREs -> LETTERs -> SUCCs.
	 */
	private final Map<STATE, Map<LETTER, Set<STATE>>> mCallOut = new HashMap<>();
	
	/**
	 * Set of return transitions LinPREs x HierPREs x LETTERs x SUCCs stored as
	 * map LinPREs -> LETTERs -> HierPREs -> SUCCs.
	 */
	private final Map<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> mReturnOut = new HashMap<>();
	
	private final Set<STATE> mInitialStates = new HashSet<>();
	private final Set<STATE> mFinalStates = new HashSet<>();
	
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
	public NestedWordAutomatonCache(final AutomataLibraryServices services, final Set<LETTER> internalAlphabet,
			final Set<LETTER> callAlphabet, final Set<LETTER> returnAlphabet, final IStateFactory<STATE> stateFactory) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		if (internalAlphabet == null) {
			throw new IllegalArgumentException("nwa must have internal alphabet");
		}
		if (stateFactory == null) {
			throw new IllegalArgumentException("nwa must have stateFactory");
		}
		mInternalAlphabet = internalAlphabet;
		mCallAlphabet = callAlphabet;
		mReturnAlphabet = returnAlphabet;
		mStateFactory = stateFactory;
		mEmptyStackState = mStateFactory.createEmptyStackState();
	}
	
	@Override
	public Set<LETTER> getInternalAlphabet() {
		return mInternalAlphabet;
	}
	
	@Override
	public Set<LETTER> getCallAlphabet() {
		return mCallAlphabet == null ? new HashSet<>(0) : mCallAlphabet;
	}
	
	@Override
	public Set<LETTER> getReturnAlphabet() {
		return mReturnAlphabet == null ? new HashSet<>(0) : mReturnAlphabet;
	}
	
	private Collection<STATE> getStates() {
		return mInternalOut.keySet();
	}
	
	@Override
	public STATE getEmptyStackState() {
		return mEmptyStackState;
	}
	
	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}
	
	/**
	 * @param state
	 *            A state.
	 * @return {@code true} iff the automaton contains the state
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
	public Collection<STATE> getInitialStates() {
		return mInitialStates;
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
	
	/**
	 * @param isInitial
	 *            {@code true} iff state is initial.
	 * @param isFinal
	 *            {@code true} iff state is accepting
	 * @param state
	 *            state
	 */
	@SuppressWarnings("squid:S2301")
	public void addState(final boolean isInitial, final boolean isFinal, final STATE state) {
		assert state != null;
		if (mInternalOut.containsKey(state)) {
			throw new IllegalArgumentException("State already exists");
		}
		mInternalOut.put(state, null);
		
		if (isInitial) {
			mInitialStates.add(state);
		}
		if (isFinal) {
			mFinalStates.add(state);
		}
	}
	
	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException(STATE + state + UNKNOWN);
		}
		final Map<LETTER, Set<STATE>> map = mInternalOut.get(state);
		return map == null ? mEmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException(STATE + state + UNKNOWN);
		}
		final Map<LETTER, Set<STATE>> map = mCallOut.get(state);
		return map == null ? mEmptySetOfLetters : map.keySet();
	}
	
	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		if (!contains(state)) {
			throw new IllegalArgumentException(STATE + state + UNKNOWN);
		}
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnOut.get(state);
		return map == null ? mEmptySetOfLetters : map.keySet();
	}
	
	/**
	 * @param state
	 *            A state.
	 * @param letter
	 *            return letter
	 * @return all respective hierarchical predecessors
	 */
	public Collection<STATE> hierPred(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnOut.get(state);
		if (map == null) {
			return mEmptySetOfStates;
		}
		final Map<STATE, Set<STATE>> hier2succs = map.get(letter);
		return hier2succs == null ? mEmptySetOfStates : hier2succs.keySet();
	}
	
	/**
	 * @param state
	 *            A state.
	 * @param letter
	 *            internal letter
	 * @return all respective internal successors
	 */
	public Collection<STATE> succInternal(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<LETTER, Set<STATE>> map = mInternalOut.get(state);
		if (map == null) {
			return null;
		}
		return map.get(letter);
	}
	
	/**
	 * @param state
	 *            A state.
	 * @param letter
	 *            call letter
	 * @return all respective call successors
	 */
	public Collection<STATE> succCall(final STATE state, final LETTER letter) {
		assert contains(state);
		final Map<LETTER, Set<STATE>> map = mCallOut.get(state);
		if (map == null) {
			return null;
		}
		return map.get(letter);
	}
	
	/**
	 * @param state
	 *            A state.
	 * @param hier
	 *            hierarchical predecessor
	 * @param letter
	 *            return letter
	 * @return all respective return successors
	 */
	public Collection<STATE> succReturn(final STATE state, final STATE hier, final LETTER letter) {
		assert contains(state);
		assert contains(hier);
		final Map<LETTER, Map<STATE, Set<STATE>>> map = mReturnOut.get(state);
		if (map == null) {
			return null;
		}
		final Map<STATE, Set<STATE>> hier2succs = map.get(letter);
		if (hier2succs == null) {
			return null;
		}
		return hier2succs.get(hier);
	}
	
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state, final LETTER letter) {
		return () -> new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
			private final Iterator<STATE> mIterator = initialize();
			
			private Iterator<STATE> initialize() {
				final Map<LETTER, Set<STATE>> letter2succ = mInternalOut.get(state);
				if (letter2succ != null && letter2succ.get(letter) != null) {
					return letter2succ.get(letter).iterator();
				}
				return null;
			}
			
			@Override
			public boolean hasNext() {
				return mIterator != null && mIterator.hasNext();
			}
			
			@Override
			public OutgoingInternalTransition<LETTER, STATE> next() {
				if (mIterator == null) {
					throw new NoSuchElementException();
				}
				final STATE succ = mIterator.next();
				return new OutgoingInternalTransition<>(letter, succ);
			}
		};
	}
	
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state) {
		/**
		 * Iterates over all OutgoingInternalTransition of state.
		 * Iterates over all outgoing internal letters and uses the
		 * iterators returned by internalSuccessors(state, letter)
		 */
		return () -> new Iterator<OutgoingInternalTransition<LETTER, STATE>>() {
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
				}
				final OutgoingInternalTransition<LETTER, STATE> result = mCurrentIterator.next();
				if (!mCurrentIterator.hasNext()) {
					nextLetter();
				}
				return result;
			}
		};
	}
	
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state, final LETTER letter) {
		return () -> new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
			private final Iterator<STATE> mIterator = initialize();
			
			private Iterator<STATE> initialize() {
				final Map<LETTER, Set<STATE>> letter2succ = mCallOut.get(state);
				if (letter2succ != null && letter2succ.get(letter) != null) {
					return letter2succ.get(letter).iterator();
				}
				return null;
			}
			
			@Override
			public boolean hasNext() {
				return mIterator != null && mIterator.hasNext();
			}
			
			@Override
			public OutgoingCallTransition<LETTER, STATE> next() {
				if (mIterator == null) {
					throw new NoSuchElementException();
				}
				final STATE succ = mIterator.next();
				return new OutgoingCallTransition<>(letter, succ);
			}
		};
	}
	
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state) {
		/**
		 * Iterates over all OutgoingCallTransition of state.
		 * Iterates over all outgoing call letters and uses the
		 * iterators returned by callSuccessors(state, letter)
		 */
		return () -> new Iterator<OutgoingCallTransition<LETTER, STATE>>() {
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
				}
				final OutgoingCallTransition<LETTER, STATE> result = mCurrentIterator.next();
				if (!mCurrentIterator.hasNext()) {
					nextLetter();
				}
				return result;
			}
		};
	}
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final STATE hier, final LETTER letter) {
		return () -> new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
			private final Iterator<STATE> mIterator = initialize();
			
			private Iterator<STATE> initialize() {
				final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succ = mReturnOut.get(state);
				if (letter2hier2succ != null) {
					final Map<STATE, Set<STATE>> hier2succ = letter2hier2succ.get(letter);
					if (hier2succ != null && hier2succ.get(hier) != null) {
						return hier2succ.get(hier).iterator();
					}
				}
				return null;
			}
			
			@Override
			public boolean hasNext() {
				return mIterator != null && mIterator.hasNext();
			}
			
			@Override
			public OutgoingReturnTransition<LETTER, STATE> next() {
				if (mIterator == null) {
					throw new NoSuchElementException();
				}
				final STATE succ = mIterator.next();
				return new OutgoingReturnTransition<>(hier, letter, succ);
			}
		};
	}
	
	/*
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final LETTER letter) {
		// Iterates over all OutgoingReturnTransition of state.
		// Iterates over all outgoing return letters and uses the
		// iterators returned by returnSuccecessors(state, letter)
		return () -> new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
			Iterator<STATE> mHierIterator;
			STATE mCurrentHier;
			Iterator<OutgoingReturnTransition<LETTER, STATE>> mCurrentIterator;
			{
				mHierIterator = hierPred(state, letter).iterator();
				nextHier();
			}
			
			private void nextHier() {
				if (mHierIterator.hasNext()) {
					do {
						mCurrentHier = mHierIterator.next();
						mCurrentIterator = returnSucccessors(state, mCurrentHier, letter).iterator();
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
					OutgoingReturnTransition<LETTER, STATE> result = mCurrentIterator.next();
					if (!mCurrentIterator.hasNext()) {
						nextHier();
					}
					return result;
				}
			}
		};
	}
	*/
	
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			final STATE state, final STATE hier) {
		/**
		 * Iterates over all OutgoingReturnTransition of state with
		 * hierarchical successor hier.
		 * Iterates over all outgoing return letters and uses the
		 * iterators returned by returnSuccecessors(state, hier, letter)
		 */
		return () -> new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
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
				}
				final OutgoingReturnTransition<LETTER, STATE> result = mCurrentIterator.next();
				if (!mCurrentIterator.hasNext()) {
					nextLetter();
				}
				return result;
			}
		};
	}
	
	/*
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state) {
		// Iterates over all OutgoingReturnTransition of state.
		// Iterates over all outgoing return letters and uses the
		// iterators returned by returnSuccessors(state, letter)
		return () -> new Iterator<OutgoingReturnTransition<LETTER, STATE>>() {
			Iterator<LETTER> mLetterIterator;
			LETTER mCurrentLetter;
			Iterator<OutgoingReturnTransition<LETTER, STATE>> mCurrentIterator;
			{
				mLetterIterator = lettersReturn(state).iterator();
				nextLetter();
			}
			
			private void nextLetter() {
				if (mLetterIterator.hasNext()) {
					do {
						mCurrentLetter = mLetterIterator.next();
						mCurrentIterator = returnSuccessors(state, mCurrentLetter).iterator();
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
					OutgoingReturnTransition<LETTER, STATE> result =
							mCurrentIterator.next();
					if (!mCurrentIterator.hasNext()) {
						nextLetter();
					}
					return result;
				}
			}
		};
	}
	*/
	
	/**
	 * @param state
	 *            The predecessor state.
	 * @param letter
	 *            internal letter
	 * @param succ
	 *            successor state
	 * @return {@code true} iff automaton contains respective transition
	 */
	public boolean containsInternalTransition(final STATE state, final LETTER letter, final STATE succ) {
		assert contains(state);
		final Map<LETTER, Set<STATE>> map = mInternalOut.get(state);
		if (map == null) {
			return false;
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? false : result.contains(succ);
	}
	
	/**
	 * @param state
	 *            The predecessor state.
	 * @param letter
	 *            call letter
	 * @param succ
	 *            successor state
	 * @return {@code true} iff automaton contains respective transition
	 */
	public boolean containsCallTransition(final STATE state, final LETTER letter, final STATE succ) {
		assert contains(state);
		final Map<LETTER, Set<STATE>> map = mCallOut.get(state);
		if (map == null) {
			return false;
		}
		final Set<STATE> result = map.get(letter);
		return result == null ? false : result.contains(succ);
	}
	
	/**
	 * @param state
	 *            The predecessor state.
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            return letter
	 * @param succ
	 *            successor state
	 * @return {@code true} iff automaton contains respective transition
	 */
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
		int statesWithReturnSuccessor = 0;
		int returnSuccessors = 0;
		for (final Entry<STATE, Map<LETTER, Map<STATE, Set<STATE>>>> entry1 : mReturnOut.entrySet()) {
			statesWithReturnSuccessor++;
			final Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succs = entry1.getValue();
			for (final Entry<LETTER, Map<STATE, Set<STATE>>> entry2 : letter2hier2succs.entrySet()) {
				final Map<STATE, Set<STATE>> hier2succs = entry2.getValue();
				for (final Entry<STATE, Set<STATE>> entry3 : hier2succs.entrySet()) {
					final Set<STATE> succs = entry3.getValue();
					returnSuccessors += succs.size();
				}
			}
		}
		final StringBuilder sb = new StringBuilder();
		sb.append(" has ").append(mInternalOut.size()).append(" states, " + statesWithInternalSuccessors)
				.append(" states have internal successors, (").append(internalSuccessors).append("), ")
				.append(statesWithCallSuccessors).append(" states have call successors, (").append(callSuccessors)
				.append("), ").append(statesWithReturnSuccessor).append(" states have return successors, (")
				.append(returnSuccessors).append("), ");
		return sb.toString();
	}
	
	private boolean assertThatAllStatesAreInAutomaton(final Collection<STATE> succs) {
		boolean result = true;
		for (final STATE state : succs) {
			result &= contains(state);
			assert result : STATE + state + NOT_IN_AUTOMATON;
		}
		return result;
	}
	
	/**
	 * @param pred
	 *            The predecessor state.
	 * @param letter
	 *            internal letter
	 * @param succ
	 *            successor state
	 */
	public void addInternalTransition(final STATE pred, final LETTER letter, final STATE succ) {
		if (!contains(pred)) {
			throw new IllegalArgumentException(STATE + pred + NOT_IN_AUTOMATON);
		}
		assert contains(pred) : STATE + pred + NOT_IN_AUTOMATON;
		assert contains(succ) : STATE + succ + NOT_IN_AUTOMATON;
		assert getInternalAlphabet().contains(letter);
		Map<LETTER, Set<STATE>> letter2succs = mInternalOut.get(pred);
		if (letter2succs == null) {
			letter2succs = new HashMap<>();
			mInternalOut.put(pred, letter2succs);
		}
		Set<STATE> succs = letter2succs.get(letter);
		if (succs == null) {
			succs = new HashSet<>();
			letter2succs.put(letter, succs);
		}
		succs.add(succ);
	}
	
	/**
	 * @param pred
	 *            The predecessor state.
	 * @param letter
	 *            internal letter
	 * @param succs
	 *            successor states
	 */
	public void addInternalTransitions(final STATE pred, final LETTER letter, final Collection<STATE> succs) {
		if (!contains(pred)) {
			throw new IllegalArgumentException(STATE + pred + NOT_IN_AUTOMATON);
		}
		assert contains(pred) : STATE + pred + NOT_IN_AUTOMATON;
		assert assertThatAllStatesAreInAutomaton(succs);
		assert getInternalAlphabet().contains(letter);
		Map<LETTER, Set<STATE>> letter2succs = mInternalOut.get(pred);
		if (letter2succs == null) {
			letter2succs = new HashMap<>();
			mInternalOut.put(pred, letter2succs);
		}
		Set<STATE> oldSuccs = letter2succs.get(letter);
		if (oldSuccs == null) {
			oldSuccs = new HashSet<>();
			letter2succs.put(letter, oldSuccs);
		}
		oldSuccs.addAll(succs);
	}
	
	/**
	 * @param pred
	 *            The predecessor state.
	 * @param letter
	 *            call letter
	 * @param succ
	 *            successor state
	 */
	public void addCallTransition(final STATE pred, final LETTER letter, final STATE succ) {
		assert contains(pred) : STATE + pred + NOT_IN_AUTOMATON;
		assert contains(succ) : STATE + succ + NOT_IN_AUTOMATON;
		assert getCallAlphabet().contains(letter);
		Map<LETTER, Set<STATE>> letter2succs = mCallOut.get(pred);
		if (letter2succs == null) {
			letter2succs = new HashMap<>();
			mCallOut.put(pred, letter2succs);
		}
		Set<STATE> succs = letter2succs.get(letter);
		if (succs == null) {
			succs = new HashSet<>();
			letter2succs.put(letter, succs);
		}
		succs.add(succ);
	}
	
	/**
	 * @param pred
	 *            The predecessor state.
	 * @param letter
	 *            call letter
	 * @param succs
	 *            successor states
	 */
	public void addCallTransitions(final STATE pred, final LETTER letter, final Collection<STATE> succs) {
		assert contains(pred) : STATE + pred + NOT_IN_AUTOMATON;
		assert assertThatAllStatesAreInAutomaton(succs);
		assert getCallAlphabet().contains(letter);
		Map<LETTER, Set<STATE>> letter2succs = mCallOut.get(pred);
		if (letter2succs == null) {
			letter2succs = new HashMap<>();
			mCallOut.put(pred, letter2succs);
		}
		Set<STATE> oldSuccs = letter2succs.get(letter);
		if (oldSuccs == null) {
			oldSuccs = new HashSet<>();
			letter2succs.put(letter, oldSuccs);
		}
		oldSuccs.addAll(succs);
	}
	
	/**
	 * @param pred
	 *            The linear predecessor state.
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            return letter
	 * @param succ
	 *            successor state
	 */
	public void addReturnTransition(final STATE pred, final STATE hier, final LETTER letter, final STATE succ) {
		assert contains(pred) : STATE + pred + NOT_IN_AUTOMATON;
		assert contains(succ) : STATE + succ + NOT_IN_AUTOMATON;
		assert contains(hier) : STATE + hier + NOT_IN_AUTOMATON;
		assert getReturnAlphabet().contains(letter);
		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succs = mReturnOut.get(pred);
		if (letter2hier2succs == null) {
			letter2hier2succs = new HashMap<>();
			mReturnOut.put(pred, letter2hier2succs);
		}
		Map<STATE, Set<STATE>> hier2succs = letter2hier2succs.get(letter);
		if (hier2succs == null) {
			hier2succs = new HashMap<>();
			letter2hier2succs.put(letter, hier2succs);
		}
		Set<STATE> succs = hier2succs.get(hier);
		if (succs == null) {
			succs = new HashSet<>();
			hier2succs.put(hier, succs);
		}
		succs.add(succ);
	}
	
	/**
	 * @param pred
	 *            The linear predecessor state.
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            return letter
	 * @param succs
	 *            successor states
	 */
	public void addReturnTransitions(final STATE pred, final STATE hier, final LETTER letter,
			final Collection<STATE> succs) {
		assert contains(pred) : STATE + pred + NOT_IN_AUTOMATON;
		assert assertThatAllStatesAreInAutomaton(succs);
		assert contains(hier) : STATE + hier + NOT_IN_AUTOMATON;
		assert getReturnAlphabet().contains(letter);
		Map<LETTER, Map<STATE, Set<STATE>>> letter2hier2succs = mReturnOut.get(pred);
		if (letter2hier2succs == null) {
			letter2hier2succs = new HashMap<>();
			mReturnOut.put(pred, letter2hier2succs);
		}
		Map<STATE, Set<STATE>> hier2succs = letter2hier2succs.get(letter);
		if (hier2succs == null) {
			hier2succs = new HashMap<>();
			letter2hier2succs.put(letter, hier2succs);
		}
		Set<STATE> oldSuccs = hier2succs.get(hier);
		if (oldSuccs == null) {
			oldSuccs = new HashSet<>();
			hier2succs.put(hier, oldSuccs);
		}
		oldSuccs.addAll(succs);
	}
	
	/**
	 * @return {@code true} iff this automaton is deterministic.
	 */
	public boolean isDeterministic() {
		if (getInitialStates().size() > 1) {
			return false;
		}
		for (final STATE state : this.getStates()) {
			if (!isDeterministic(state)) {
				return false;
			}
		}
		return true;
	}
	
	private boolean isDeterministic(final STATE state) {
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
			for (final STATE hier : hierPred(state, symbol)) {
				if (succReturn(state, hier, symbol).size() > 1) {
					return false;
				}
			}
		}
		return true;
	}
	
	/**
	 * @return {@code true} iff this automaton is total.
	 */
	public boolean isTotal() {
		if (getInitialStates().isEmpty()) {
			return false;
		}
		for (final STATE state : this.getStates()) {
			if (!isTotal(state)) {
				return false;
			}
		}
		return true;
	}
	
	private boolean isTotal(final STATE state) {
		for (final LETTER symbol : getInternalAlphabet()) {
			if (succInternal(state, symbol).isEmpty()) {
				return false;
			}
		}
		for (final LETTER symbol : getCallAlphabet()) {
			if (succCall(state, symbol).isEmpty()) {
				return false;
			}
		}
		for (final LETTER symbol : getReturnAlphabet()) {
			for (final STATE hier : getStates()) {
				if (succReturn(state, hier, symbol).isEmpty()) {
					return false;
				}
			}
		}
		return true;
	}
	
	/**
	 * @param state
	 *            A state.
	 * @return number of outgoing internal transitions
	 */
	public int numberOfOutgoingInternalTransitions(final STATE state) {
		int result = 0;
		for (final LETTER letter : lettersInternal(state)) {
			result += succInternal(state, letter).size();
		}
		return result;
	}
	
	@Override
	public String toString() {
		return (new AutomatonDefinitionPrinter<String, String>(mServices, "nwa", Format.ATS, this))
				.getDefinitionAsString();
	}
}
