/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IConcurrentProductStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Product of two automata that is similar to the synchronization operator for parallel transition systems. For shared
 * letters of both input automata move if the letter is read. For the other letters only the corresponding automaton
 * moves. 2016-11-18 Matthias: It seems that for similar alphabets the result of this operation is equivalent to the
 * intersection if the parameter concurrentPrefixProduct is true and it is equivalent to the union if the parameter
 * concurrentPrefixProduct if false.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Symbol
 * @param <STATE>
 *            Content
 */
public final class ConcurrentProduct<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;

	private final boolean mConcurrentPrefixProduct;

	private final NestedWordAutomaton<LETTER, STATE> mResult;

	/**
	 * List of state pairs from the input automata for which
	 * <ul>
	 * <li>there has already been a state in the result constructed
	 * <li>outgoing transitions of this state have not yet been constructed.
	 * </ul>
	 */
	private final StatePairQueue mWorklist = new StatePairQueue();

	/**
	 * Map from state pairs of the input automata to corresponding states in the result automaton.
	 */
	private final StatePair2StateMap mInputPair2resultState = new StatePair2StateMap();

	/**
	 * Common symbols of the Alphabets of the input automata.
	 */
	private final HashSet<LETTER> mSynchronizationAlphabet;

	private final IConcurrentProductStateFactory<STATE> mContentFactory;

	/**
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @param concurrentPrefixProduct
	 *            {@code true} iff a concurrent prefix product should be created (i.e., a place is final if at least one
	 *            of the old places was final)
	 */
	@SuppressWarnings("squid:S1067")
	public ConcurrentProduct(final AutomataLibraryServices services,
			final IConcurrentProductStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand, final boolean concurrentPrefixProduct) {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mConcurrentPrefixProduct = concurrentPrefixProduct;
		mContentFactory = stateFactory;
		/*FIXME
		if (mContentFactory != nwa2.getContentFactory()) {
			throw new IllegalArgumentException("Both NWAs have to use" +
					"same ContentFactory");
		}
		*/

		if (mLogger.isWarnEnabled()
				&& (!NestedWordAutomataUtils.isFiniteAutomaton(fstOperand)
						|| !NestedWordAutomataUtils.isFiniteAutomaton(sndOperand))) {
			mLogger.warn("Call alphabet and return alphabet are ignored.");
		}
		mSynchronizationAlphabet = new HashSet<>(fstOperand.getAlphabet());
		mSynchronizationAlphabet.retainAll(sndOperand.getAlphabet());
		final Set<LETTER> commonAlphabet = new HashSet<>(fstOperand.getAlphabet());
		commonAlphabet.addAll(sndOperand.getAlphabet());
		// TODO Christian 2016-09-04: Use Collections.emptySet() or is it intended that a user modifies the result?
		mResult = new NestedWordAutomaton<>(mServices, new VpAlphabet<>(commonAlphabet),
				mContentFactory);
		constructInitialStates();
		while (!mWorklist.isEmpty()) {
			mWorklist.dequeuePair();
			final STATE state1 = mWorklist.getDequeuedPairFst();
			final STATE state2 = mWorklist.getDequeuedPairSnd();
			constructOutgoingTransitions(state1, state2);
		}
	}

	/**
	 * Returns the automaton state that represents the state pair (state1,state2). If this state is not yet constructed,
	 * construct it and enqueue the pair (state1,state2). If it has to be constructed it is an initial state iff
	 * isInitial is true.
	 */
	private STATE getState(final STATE state1, final STATE state2, final boolean isInitial) {
		STATE state = mInputPair2resultState.get(state1, state2);
		if (state == null) {
			boolean isFinal;
			if (mConcurrentPrefixProduct) {
				isFinal = mFstOperand.isFinal(state1) || mSndOperand.isFinal(state2);
			} else {
				isFinal = mFstOperand.isFinal(state1) && mSndOperand.isFinal(state2);
			}
			final STATE content1 = state1;
			final STATE content2 = state2;
			state = mContentFactory.concurrentProduct(content1, content2);
			mResult.addState(isInitial, isFinal, state);
			mInputPair2resultState.put(state1, state2, state);
			mWorklist.enqueue(state1, state2);
		}
		return state;
	}

	private void constructOutgoingTransitions(final STATE state1, final STATE state2) {
		final STATE state = getState(state1, state2, false);
		final HashSet<LETTER> commonOutSymbols = new HashSet<>(mFstOperand.lettersInternal(state1));
		commonOutSymbols.retainAll(mSndOperand.lettersInternal(state2));
		final HashSet<LETTER> state1OnlySymbols = new HashSet<>(mFstOperand.lettersInternal(state1));
		state1OnlySymbols.removeAll(mSynchronizationAlphabet);
		final HashSet<LETTER> state2OnlySymbols = new HashSet<>(mSndOperand.lettersInternal(state2));
		state2OnlySymbols.removeAll(mSynchronizationAlphabet);

		for (final LETTER symbol : commonOutSymbols) {
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> trans1it =
					mFstOperand.internalSuccessors(state1, symbol);
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> trans2it =
					mSndOperand.internalSuccessors(state2, symbol);
			for (final OutgoingInternalTransition<LETTER, STATE> trans1 : trans1it) {
				final STATE succ1 = trans1.getSucc();
				for (final OutgoingInternalTransition<LETTER, STATE> trans2 : trans2it) {
					final STATE succ2 = trans2.getSucc();
					final STATE succ = getState(succ1, succ2, false);
					mResult.addInternalTransition(state, symbol, succ);
				}
			}
		}

		for (final LETTER symbol : state1OnlySymbols) {
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> trans1it =
					mFstOperand.internalSuccessors(state1, symbol);
			for (final OutgoingInternalTransition<LETTER, STATE> trans1 : trans1it) {
				final STATE succ1 = trans1.getSucc();
				final STATE succ = getState(succ1, state2, false);
				mResult.addInternalTransition(state, symbol, succ);
			}
		}

		for (final LETTER symbol : state2OnlySymbols) {
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> trans2it =
					mSndOperand.internalSuccessors(state2, symbol);
			for (final OutgoingInternalTransition<LETTER, STATE> trans2 : trans2it) {
				final STATE succ2 = trans2.getSucc();
				final STATE succ = getState(state1, succ2, false);
				mResult.addInternalTransition(state, symbol, succ);
			}
		}

	}

	private void constructInitialStates() {
		for (final STATE state1 : mFstOperand.getInitialStates()) {
			for (final STATE state2 : mSndOperand.getInitialStates()) {
				getState(state1, state2, true);
			}
		}
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getFirstOperand() {
		return mFstOperand;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getSecondOperand() {
		return mSndOperand;
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	/**
	 * Maps pairs of states to states.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class StatePair2StateMap {
		private final Map<STATE, Map<STATE, STATE>> mBackingMap = new HashMap<>();

		protected STATE get(final STATE state1, final STATE state2) {
			final Map<STATE, STATE> snd2result = mBackingMap.get(state1);
			if (snd2result == null) {
				return null;
			} else {
				return snd2result.get(state2);
			}
		}

		protected void put(final STATE state1, final STATE state2, final STATE state) {
			Map<STATE, STATE> snd2result = mBackingMap.get(state1);
			if (snd2result == null) {
				snd2result = new HashMap<>();
				mBackingMap.put(state1, snd2result);
			}
			snd2result.put(state2, state);
		}
	}

	/**
	 * Queue for pairs of states. Pairs are not dequeued in the same order as inserted.
	 * 
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 */
	private class StatePairQueue {
		private final Map<STATE, Set<STATE>> mQueue = new HashMap<>();

		private STATE mDequeuedPairFst;
		private STATE mDequeuedPairSnd;

		protected void enqueue(final STATE state1, final STATE state2) {
			Set<STATE> secondComponets = mQueue.get(state1);
			if (secondComponets == null) {
				secondComponets = new HashSet<>();
				mQueue.put(state1, secondComponets);
			}
			secondComponets.add(state2);
		}

		protected void dequeuePair() {
			assert mDequeuedPairFst == null
					&& mDequeuedPairSnd == null : "Results from last dequeue not yet collected!";
			final Iterator<STATE> it1 = mQueue.keySet().iterator();
			mDequeuedPairFst = it1.next();
			assert mQueue.get(mDequeuedPairFst) != null;
			final Set<STATE> secondComponets = mQueue.get(mDequeuedPairFst);
			assert secondComponets != null;
			final Iterator<STATE> it2 = secondComponets.iterator();
			mDequeuedPairSnd = it2.next();

			secondComponets.remove(mDequeuedPairSnd);
			if (secondComponets.isEmpty()) {
				mQueue.remove(mDequeuedPairFst);
			}
		}

		protected STATE getDequeuedPairFst() {
			assert mDequeuedPairFst != null : "No pair dequeued";
			final STATE result = mDequeuedPairFst;
			mDequeuedPairFst = null;
			return result;
		}

		public STATE getDequeuedPairSnd() {
			assert mDequeuedPairSnd != null : "No pair dequeued";
			final STATE result = mDequeuedPairSnd;
			mDequeuedPairSnd = null;
			return result;
		}

		public boolean isEmpty() {
			return mQueue.isEmpty();
		}
	}
}
