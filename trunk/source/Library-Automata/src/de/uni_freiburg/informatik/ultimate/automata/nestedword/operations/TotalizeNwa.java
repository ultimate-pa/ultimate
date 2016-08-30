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
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Totalized automaton of input. Expects that input is deterministic.
 * If a transition is nondeterministic an empty transition set is returned and
 * mNondeterminismInInputDetected is set to true.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class TotalizeNwa<LETTER, STATE>
		implements INestedWordAutomatonSimple<LETTER, STATE> {
	
	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand;
	private final IStateFactory<STATE> mStateFactory;
	private final STATE mSinkState;
	private boolean mNondeterministicTransitionsDetected = false;
	private boolean mNondeterministicInitialsDetected = false;

	/**
	 * @param operand operand
	 * @param stateFactory state factory
	 */
	public TotalizeNwa(final INestedWordAutomatonSimple<LETTER, STATE> operand,
			final IStateFactory<STATE> stateFactory) {
		mOperand = operand;
		mStateFactory = stateFactory;
		mSinkState = stateFactory.createSinkStateContent();
		if (mSinkState == null) {
			throw new IllegalArgumentException("sink state must not be null");
		}
	}

	public boolean nonDeterminismInInputDetected() {
		return mNondeterministicTransitionsDetected || mNondeterministicInitialsDetected;
	}
	
	public boolean nondeterministicTransitionsDetected() {
		return mNondeterministicTransitionsDetected;
	}

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
			initial = mSinkState;
		}
		if (it.hasNext()) {
			mNondeterministicInitialsDetected = true;
		}
		final HashSet<STATE> result = new HashSet<STATE>(1);
		result.add(initial);
		return result;
	}

	@Override
	public Set<LETTER> getInternalAlphabet() {
		return mOperand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return mOperand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return mOperand.getReturnAlphabet();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}
	
	@Override
	public boolean isInitial(final STATE state) {
		if (state == mSinkState) {
			return false;
		} else {
			return mOperand.isInitial(state);
		}
	}

	@Override
	public boolean isFinal(final STATE state) {
		if (state == mSinkState) {
			/*
			 * TODO Christian 2016-08-29: This is a bug: If the input automaton was a totalized and complemented
			 *      automaton, the sink state could already exist and be final. This worked before because the
			 *      StateFactory created a fresh sink state.
			 */
			return false;
		} else {
			return mOperand.isFinal(state);
		}
	}

	@Override
	public STATE getEmptyStackState() {
		return mOperand.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		return mOperand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		return mOperand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> lettersReturn(final STATE state) {
		return mOperand.getReturnAlphabet();
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state, final LETTER letter) {
		if (mNondeterministicTransitionsDetected) {
			return new HashSet<OutgoingInternalTransition<LETTER, STATE>>(0);
		}
		if (state != mSinkState) {
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> it =
					mOperand.internalSuccessors(state, letter).iterator();
			if (it.hasNext()) {
				it.next();
				if (it.hasNext()) {
					mNondeterministicTransitionsDetected = true;
					return new HashSet<OutgoingInternalTransition<LETTER, STATE>>(0);
				} else {
					return mOperand.internalSuccessors(state, letter);
				}
			}
		}
		final OutgoingInternalTransition<LETTER, STATE> trans =
				new OutgoingInternalTransition<LETTER, STATE>(letter, mSinkState);
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result =
				new ArrayList<OutgoingInternalTransition<LETTER, STATE>>(1);
		result.add(trans);
		return result;
	}

	@SuppressWarnings("squid:S1941")
	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state) {
		if (mNondeterministicTransitionsDetected) {
			return new HashSet<OutgoingInternalTransition<LETTER, STATE>>(0);
		}
		final ArrayList<OutgoingInternalTransition<LETTER, STATE>> result =
				new ArrayList<OutgoingInternalTransition<LETTER, STATE>>();
		for (final LETTER letter : getInternalAlphabet()) {
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> it =
					internalSuccessors(state, letter).iterator();
			if (mNondeterministicTransitionsDetected) {
				return new HashSet<OutgoingInternalTransition<LETTER, STATE>>(0);
			}
			result.add(it.next());
			assert !it.hasNext();
		}
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state, final LETTER letter) {
		if (mNondeterministicTransitionsDetected) {
			return new HashSet<OutgoingCallTransition<LETTER, STATE>>(0);
		}
		if (state != mSinkState) {
			final Iterator<OutgoingCallTransition<LETTER, STATE>> it =
					mOperand.callSuccessors(state, letter).iterator();
			if (it.hasNext()) {
				it.next();
				if (it.hasNext()) {
					mNondeterministicTransitionsDetected = true;
					return new HashSet<OutgoingCallTransition<LETTER, STATE>>(0);
				} else {
					return mOperand.callSuccessors(state, letter);
				}
			}
		}
		final OutgoingCallTransition<LETTER, STATE> trans =
				new OutgoingCallTransition<LETTER, STATE>(letter, mSinkState);
		final ArrayList<OutgoingCallTransition<LETTER, STATE>> result =
				new ArrayList<OutgoingCallTransition<LETTER, STATE>>(1);
		result.add(trans);
		return result;
	}

	@SuppressWarnings("squid:S1941")
	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state) {
		if (mNondeterministicTransitionsDetected) {
			return new HashSet<OutgoingCallTransition<LETTER, STATE>>(0);
		}
		final ArrayList<OutgoingCallTransition<LETTER, STATE>> result =
				new ArrayList<OutgoingCallTransition<LETTER, STATE>>();
		for (final LETTER letter : getCallAlphabet()) {
			final Iterator<OutgoingCallTransition<LETTER, STATE>> it =
					callSuccessors(state, letter).iterator();
			if (mNondeterministicTransitionsDetected) {
				return new HashSet<OutgoingCallTransition<LETTER, STATE>>(0);
			}
			result.add(it.next());
			assert !it.hasNext();
		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final STATE hier, final LETTER letter) {
		if (mNondeterministicTransitionsDetected) {
			return new HashSet<OutgoingReturnTransition<LETTER, STATE>>(0);
		}
		if (state != mSinkState) {
			final Iterator<OutgoingReturnTransition<LETTER, STATE>> it =
					mOperand.returnSuccessors(state, hier, letter).iterator();
			if (it.hasNext()) {
				it.next();
				if (it.hasNext()) {
					mNondeterministicTransitionsDetected = true;
					return new HashSet<OutgoingReturnTransition<LETTER, STATE>>(0);
				} else {
					return mOperand.returnSuccessors(state, hier, letter);
				}
			}
		}
		final OutgoingReturnTransition<LETTER, STATE> trans =
				new OutgoingReturnTransition<LETTER, STATE>(hier, letter, mSinkState);
		final ArrayList<OutgoingReturnTransition<LETTER, STATE>> result =
				new ArrayList<OutgoingReturnTransition<LETTER, STATE>>(1);
		result.add(trans);
		return result;
	}

	@SuppressWarnings("squid:S1941")
	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			final STATE state, final STATE hier) {
		if (mNondeterministicTransitionsDetected) {
			return new HashSet<OutgoingReturnTransition<LETTER, STATE>>(0);
		}
		final ArrayList<OutgoingReturnTransition<LETTER, STATE>> result =
				new ArrayList<OutgoingReturnTransition<LETTER, STATE>>();
		for (final LETTER letter : getReturnAlphabet()) {
			final Iterator<OutgoingReturnTransition<LETTER, STATE>> it =
					returnSuccessors(state, hier, letter).iterator();
			if (mNondeterministicTransitionsDetected) {
				return new HashSet<OutgoingReturnTransition<LETTER, STATE>>(0);
			}
			result.add(it.next());
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
