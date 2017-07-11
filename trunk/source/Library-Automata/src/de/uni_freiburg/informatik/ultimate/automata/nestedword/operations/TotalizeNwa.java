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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Totalized automaton of input. 
 * 
 * Has a special mode in which it expects that input is deterministic. If then 
 * a transition is nondeterministic an empty transition set is returned and 
 * mNondeterminismInInputDetected is set to true.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class TotalizeNwa<LETTER, STATE> implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final ISinkStateFactory<STATE> mStateFactory;
	private STATE mSinkState;
	private boolean mSinkStateWasConstructed;
	private boolean mNondeterministicTransitionsDetected;
	private boolean mNondeterministicInitialsDetected;
	private final boolean mStopIfNondeterminismWasDetected;

	/**
	 * Constructor.
	 * 
	 * @param operand
	 *            operand
	 * @param stateFactory
	 *            state factory
	 * @param stopIfNondeterminismWasDetected 
	 */
	public TotalizeNwa(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final ISinkStateFactory<STATE> stateFactory, final boolean stopIfNondeterminismWasDetected) {
		mOperand = operand;
		mStateFactory = stateFactory;
		mStopIfNondeterminismWasDetected = stopIfNondeterminismWasDetected;
	}

	private void requestSinkState() {
		if (mSinkStateWasConstructed) {
			// do nothing
			assert mSinkState != null;
		} else {
			assert mSinkState == null;
			mSinkState = mStateFactory.createSinkStateContent();
			if (mSinkState == null) {
				throw new IllegalArgumentException("sink state must not be null");
			}
			if (mOperand instanceof INestedWordAutomaton
					&& ((INestedWordAutomaton<?, ?>) mOperand).getStates().contains(mSinkState)) {
				throw new UnsupportedOperationException("Operand already contains the state " + mSinkState);
			}
		}
		mSinkStateWasConstructed = true;
	}

	/**
	 * @param state
	 *            The candidate state.
	 * @return {@code true} iff the sink state was constructed and is equal to the given state
	 */
	@SuppressWarnings("squid:S1698")
	private boolean isNewSinkState(final STATE state) {
		// equality intended here
		return mSinkStateWasConstructed && state == mSinkState;
	}

	/**
	 * @return {@code true} iff automaton is nondeterministic.
	 */
	public boolean nonDeterminismInInputDetected() {
		return mNondeterministicTransitionsDetected || mNondeterministicInitialsDetected;
	}

	/**
	 * @return {@code true} iff automaton has nondeterministic transitions.
	 */
	public boolean nondeterministicTransitionsDetected() {
		return mNondeterministicTransitionsDetected;
	}

	/**
	 * @return {@code true} iff automaton has more than one initial state.
	 */
	public boolean nondeterministicInitialsDetected() {
		return mNondeterministicInitialsDetected;
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		final Iterator<STATE> it = mOperand.getInitialStates().iterator();
		STATE initial;
		if (it.hasNext()) {
			initial = it.next();
		} else {
			requestSinkState();
			initial = mSinkState;
		}
		if (it.hasNext()) {
			mNondeterministicInitialsDetected = true;
		}
		final HashSet<STATE> result = new HashSet<>(1);
		result.add(initial);
		return result;
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public boolean isInitial(final STATE state) {
		/*
		 * There are problems if the input already contains the state that is the sink state of this automaton. We
		 * approach these problems by comparing a state only to the sink state if a new sink state was constructed.
		 */
		if (isNewSinkState(state)) {
			// return true iff operand does not have initial states
			return !mOperand.getInitialStates().iterator().hasNext();
		}
		return mOperand.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		/*
		 * There are problems if the input already contains the state that is the sink state of this automaton. We
		 * approach these problems by comparing a state only to the sink state if a newly sink state was constructed
		 */
		if (isNewSinkState(state)) {
			return false;
		}
		return mOperand.isFinal(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return mOperand.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		return mOperand.getVpAlphabet().getInternalAlphabet();
	}

	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		return mOperand.getVpAlphabet().getCallAlphabet();
	}
	
	@Override
	public Set<LETTER> lettersReturn(final STATE state, final STATE hier) {
		return mOperand.getVpAlphabet().getReturnAlphabet();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		if (mStopIfNondeterminismWasDetected && mNondeterministicTransitionsDetected) {
			return Collections.emptySet();
		}
		if (!isNewSinkState(state)) {
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> it =
					mOperand.internalSuccessors(state, letter).iterator();
			if (it.hasNext()) {
				final OutgoingInternalTransition<LETTER, STATE> trans = it.next();
				if (it.hasNext()) {
					mNondeterministicTransitionsDetected = true;
					if (mStopIfNondeterminismWasDetected) {
						return Collections.emptySet();
					} else {
						return mOperand.internalSuccessors(state, letter);
					}
				}
				return Collections.singleton(trans);
			}
		}
		requestSinkState();
		final OutgoingInternalTransition<LETTER, STATE> trans = new OutgoingInternalTransition<>(letter, mSinkState);
		return Collections.singleton(trans);
	}

	@SuppressWarnings("squid:S1941")
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		if (mStopIfNondeterminismWasDetected && mNondeterministicTransitionsDetected) {
			return Collections.emptySet();
		}
		final Set<LETTER> alphabet = getVpAlphabet().getInternalAlphabet();
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>(alphabet.size());
		for (final LETTER letter : alphabet) {
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> it = internalSuccessors(state, letter).iterator();
			if (mStopIfNondeterminismWasDetected && mNondeterministicTransitionsDetected) {
				return Collections.emptySet();
			}
			while (it.hasNext()) {
				result.add(it.next());
			}
			assert !it.hasNext();
		}
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		if (mStopIfNondeterminismWasDetected && mNondeterministicTransitionsDetected) {
			return Collections.emptySet();
		}
		if (!isNewSinkState(state)) {
			final Iterator<OutgoingCallTransition<LETTER, STATE>> it =
					mOperand.callSuccessors(state, letter).iterator();
			if (it.hasNext()) {
				final OutgoingCallTransition<LETTER, STATE> trans = it.next();
				if (it.hasNext()) {
					mNondeterministicTransitionsDetected = true;
					if (mStopIfNondeterminismWasDetected) {
						return Collections.emptySet();
					} else {
						return mOperand.callSuccessors(state, letter);
					}
				}
				return Collections.singleton(trans);
			}
		}
		requestSinkState();
		final OutgoingCallTransition<LETTER, STATE> trans = new OutgoingCallTransition<>(letter, mSinkState);
		return Collections.singleton(trans);
	}

	@SuppressWarnings("squid:S1941")
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		if (mStopIfNondeterminismWasDetected && mNondeterministicTransitionsDetected) {
			return Collections.emptySet();
		}
		final Set<LETTER> alphabet = getVpAlphabet().getCallAlphabet();
		final ArrayList<OutgoingCallTransition<LETTER, STATE>> result = new ArrayList<>(alphabet.size());
		for (final LETTER letter : alphabet) {
			final Iterator<OutgoingCallTransition<LETTER, STATE>> it = callSuccessors(state, letter).iterator();
			if (mStopIfNondeterminismWasDetected && mNondeterministicTransitionsDetected) {
				return Collections.emptySet();
			}
			while (it.hasNext()) {
				result.add(it.next());
			}
			assert !it.hasNext();
		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		if (mStopIfNondeterminismWasDetected && mNondeterministicTransitionsDetected) {
			return Collections.emptySet();
		}
		if (!isNewSinkState(state)) {
			final Iterator<OutgoingReturnTransition<LETTER, STATE>> it =
					mOperand.returnSuccessors(state, hier, letter).iterator();
			if (it.hasNext()) {
				final OutgoingReturnTransition<LETTER, STATE> trans = it.next();
				if (it.hasNext()) {
					mNondeterministicTransitionsDetected = true;
					if (mStopIfNondeterminismWasDetected) {
						return Collections.emptySet();
					} else {
						return mOperand.returnSuccessors(state, hier, letter);
					}
				}
				return Collections.singleton(trans);
			}
		}
		requestSinkState();
		final OutgoingReturnTransition<LETTER, STATE> trans = new OutgoingReturnTransition<>(hier, letter, mSinkState);
		return Collections.singleton(trans);
	}

	@SuppressWarnings("squid:S1941")
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		if (mStopIfNondeterminismWasDetected && mNondeterministicTransitionsDetected) {
			return Collections.emptySet();
		}
		final Set<LETTER> alphabet = getVpAlphabet().getReturnAlphabet();
		final ArrayList<OutgoingReturnTransition<LETTER, STATE>> result = new ArrayList<>(alphabet.size());
		for (final LETTER letter : alphabet) {
			final Iterator<OutgoingReturnTransition<LETTER, STATE>> it =
					returnSuccessors(state, hier, letter).iterator();
			if (mStopIfNondeterminismWasDetected && mNondeterministicTransitionsDetected) {
				return Collections.emptySet();
			}
			while (it.hasNext()) {
				result.add(it.next());
			}
			assert !it.hasNext();
		}
		return result;
	}

	@Override
	public int size() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		throw new UnsupportedOperationException();
	}

	@Override
	public String sizeInformation() {
		return "size Information not available";
	}
}
