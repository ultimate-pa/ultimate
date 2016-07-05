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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;

/**
 * Totalized automaton of input. Expects that input is deterministic.
 * If a transition is nondeterminisic an empty transition set is returned and
 * mNondeterminismInInputDetected is set to true.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class TotalizeNwa<LETTER, STATE> implements INestedWordAutomatonSimple<LETTER, STATE> {
	
	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand;
	private final StateFactory<STATE> mStateFactory;
	private final STATE mSinkState;
	private boolean mNondeterministicTransitionsDetected = false;
	private boolean mNondeterministicInitialsDetected = false;

	public boolean nonDeterminismInInputDetected() {
		return mNondeterministicTransitionsDetected || mNondeterministicInitialsDetected;
	}
	
	public boolean nondeterministicTransitionsDetected() {
		return mNondeterministicTransitionsDetected;
	}

	public boolean nondeterministicInitialsDetected() {
		return mNondeterministicInitialsDetected;
	}

	public TotalizeNwa(INestedWordAutomatonSimple<LETTER, STATE> operand, 
			StateFactory<STATE> sf) {
		mOperand = operand;
		mStateFactory = sf;
		mSinkState = sf.createSinkStateContent();
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
	public StateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}
	
	@Override
	public boolean isInitial(STATE state) {
		if (state == mSinkState) {
			return false;
		} else {
			return mOperand.isInitial(state);
		}
	}

	@Override
	public boolean isFinal(STATE state) {
		if (state == mSinkState) {
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
	public Set<LETTER> lettersInternal(STATE state) {
		return mOperand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		return mOperand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		return mOperand.getReturnAlphabet();
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
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

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
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
			STATE state, LETTER letter) {
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

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
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
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		if (mNondeterministicTransitionsDetected) {
			return new HashSet<OutgoingReturnTransition<LETTER, STATE>>(0);
		}
		if (state != mSinkState) {
			final Iterator<OutgoingReturnTransition<LETTER, STATE>> it = 
					mOperand.returnSucccessors(state, hier, letter).iterator();
			if (it.hasNext()) {
				it.next();
				if (it.hasNext()) {
					mNondeterministicTransitionsDetected = true;
					return new HashSet<OutgoingReturnTransition<LETTER, STATE>>(0);
				} else {
					return mOperand.returnSucccessors(state, hier, letter);
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

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		if (mNondeterministicTransitionsDetected) {
			return new HashSet<OutgoingReturnTransition<LETTER, STATE>>(0);
		}
		final ArrayList<OutgoingReturnTransition<LETTER, STATE>> result = 
				new ArrayList<OutgoingReturnTransition<LETTER, STATE>>();
		for (final LETTER letter : getReturnAlphabet()) {
			final Iterator<OutgoingReturnTransition<LETTER, STATE>> it = 
					returnSucccessors(state, hier, letter).iterator();
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
		throw new UnsupportedOperationException();	}

	@Override
	public String sizeInformation() {
		return "size Information not available";
	}


}
