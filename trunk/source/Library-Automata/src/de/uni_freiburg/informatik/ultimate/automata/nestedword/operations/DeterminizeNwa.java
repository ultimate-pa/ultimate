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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * On-the-fly determinized nested word automaton.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class DeterminizeNwa<LETTER, STATE> implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final NestedWordAutomaton<LETTER, STATE> mCache;
	private final IStateDeterminizer<LETTER, STATE> mStateDeterminizer;
	private final IStateFactory<STATE> mStateFactory;
	private final Set<STATE> mPredefinedInitials;
	private final boolean mMakeAutomatonTotal;

	private final Map<STATE, DeterminizedState<LETTER, STATE>> mRes2det = new HashMap<>();
	private final Map<DeterminizedState<LETTER, STATE>, STATE> mDet2res = new HashMap<>();

	/**
	 * Default constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param stateDeterminizer
	 *            state determinizer
	 * @param stateFactory
	 *            state factory
	 */
	public DeterminizeNwa(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer, final IEmptyStackStateFactory<STATE> stateFactory) {
		this(services, operand, stateDeterminizer, stateFactory, null, false);
	}

	/**
	 * Extended constructor.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            operand
	 * @param stateDeterminizer
	 *            state determinizer
	 * @param stateFactory
	 *            state factory
	 * @param predefinedInitials
	 *            predefined initial states
	 * @param makeAutomatonTotal
	 *            make automaton total?
	 */
	public DeterminizeNwa(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer, final IEmptyStackStateFactory<STATE> stateFactory,
			final Set<STATE> predefinedInitials, final boolean makeAutomatonTotal) {
		mOperand = operand;
		mStateDeterminizer = stateDeterminizer;
		mStateFactory = stateFactory;
		mCache = new NestedWordAutomaton<>(services, operand.getVpAlphabet(), stateFactory);
		mPredefinedInitials = predefinedInitials;
		mMakeAutomatonTotal = makeAutomatonTotal;
	}

	public boolean isTotal() {
		return mMakeAutomatonTotal;
	}

	private void constructInitialState() {
		if (mPredefinedInitials == null) {
			final DeterminizedState<LETTER, STATE> initialDet = mStateDeterminizer.initialState();
			final STATE initialState = mStateDeterminizer.getState(initialDet);
			mDet2res.put(initialDet, initialState);
			mRes2det.put(initialState, initialDet);
			mCache.addState(true, initialDet.containsFinal(), initialState);
		} else {
			// add singleton DoubleDecker for each initial state of operand
			for (final STATE initialOperand : mPredefinedInitials) {
				final DeterminizedState<LETTER, STATE> initialDet = new DeterminizedState<>(mOperand);
				initialDet.addPair(mOperand.getEmptyStackState(), initialOperand, mOperand);
				final STATE initialState = mStateDeterminizer.getState(initialDet);
				mDet2res.put(initialDet, initialState);
				mRes2det.put(initialState, initialDet);
				mCache.addState(true, initialDet.containsFinal(), initialState);
			}
		}
	}

	private STATE getOrConstructState(final DeterminizedState<LETTER, STATE> detState) {
		STATE state = mDet2res.get(detState);
		if (state == null) {
			state = mStateDeterminizer.getState(detState);
			mDet2res.put(detState, state);
			mRes2det.put(state, detState);
			mCache.addState(false, detState.containsFinal(), state);
		}
		return state;
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		if (mCache.getInitialStates().isEmpty()) {
			constructInitialState();
		}
		return mCache.getInitialStates();
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mCache.getVpAlphabet();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mCache.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mCache.isFinal(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return mCache.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(final STATE state) {
		if (mMakeAutomatonTotal) {
			return getVpAlphabet().getInternalAlphabet();
		}
		final Set<LETTER> result = new HashSet<>();
		final DeterminizedState<LETTER, STATE> detState = mRes2det.get(state);
		for (final STATE downState : detState.getDownStates()) {
			for (final STATE upState : detState.getUpStates(downState)) {
				result.addAll(mOperand.lettersInternal(upState));
			}
		}
		return result;
	}

	@Override
	public Set<LETTER> lettersCall(final STATE state) {
		if (mMakeAutomatonTotal) {
			return getVpAlphabet().getCallAlphabet();
		}
		final Set<LETTER> result = new HashSet<>();
		final DeterminizedState<LETTER, STATE> detState = mRes2det.get(state);
		for (final STATE downState : detState.getDownStates()) {
			for (final STATE upState : detState.getUpStates(downState)) {
				result.addAll(mOperand.lettersCall(upState));
			}
		}
		return result;
	}

	@Override
	public Set<LETTER> lettersReturn(final STATE state, final STATE hier) {
		if (mMakeAutomatonTotal) {
			return getVpAlphabet().getReturnAlphabet();
		}
		final Set<LETTER> result = new HashSet<>();
		final DeterminizedState<LETTER, STATE> detState = mRes2det.get(state);
		final DeterminizedState<LETTER, STATE> detHier = mRes2det.get(hier);
		for (final STATE hierDown : detHier.getDownStates()) {
			for (final STATE downState : detHier.getUpStates(hierDown)) {
				final Set<STATE> ups = detState.getUpStates(downState);
				if (ups != null) {
					for (final STATE upState : ups) {
						result.addAll(mOperand.lettersReturn(upState, downState));
					}
				}
			}
		}
		return result;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state,
			final LETTER letter) {
		final Iterator<OutgoingInternalTransition<LETTER, STATE>> succs =
				mCache.internalSuccessors(state, letter).iterator();
		if (!succs.hasNext()) {
			final DeterminizedState<LETTER, STATE> detState = mRes2det.get(state);
			assert detState != null;
			final DeterminizedState<LETTER, STATE> detSucc = mStateDeterminizer.internalSuccessor(detState, letter);
			final STATE succ = getOrConstructState(detSucc);
			mCache.addInternalTransition(state, letter, succ);
		}
		return mCache.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		for (final LETTER letter : lettersInternal(state)) {
			internalSuccessors(state, letter);
		}
		return mCache.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter) {
		final Iterator<OutgoingCallTransition<LETTER, STATE>> succs = mCache.callSuccessors(state, letter).iterator();
		if (!succs.hasNext()) {
			final DeterminizedState<LETTER, STATE> detState = mRes2det.get(state);
			assert detState != null;
			final DeterminizedState<LETTER, STATE> detSucc = mStateDeterminizer.callSuccessor(detState, letter);
			final STATE succ = getOrConstructState(detSucc);
			mCache.addCallTransition(state, letter, succ);
		}
		return mCache.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		for (final LETTER letter : lettersCall(state)) {
			callSuccessors(state, letter);
		}
		return mCache.callSuccessors(state);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter) {
		final Iterator<OutgoingReturnTransition<LETTER, STATE>> succs =
				mCache.returnSuccessors(state, hier, letter).iterator();
		if (!succs.hasNext()) {
			final DeterminizedState<LETTER, STATE> detState = mRes2det.get(state);
			assert detState != null;
			final DeterminizedState<LETTER, STATE> detHier = mRes2det.get(hier);
			assert detHier != null;
			final DeterminizedState<LETTER, STATE> detSucc =
					mStateDeterminizer.returnSuccessor(detState, detHier, letter);
			final STATE succ = getOrConstructState(detSucc);
			mCache.addReturnTransition(state, hier, letter, succ);
		}
		return mCache.returnSuccessors(state, hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		for (final LETTER letter : lettersReturn(state, hier)) {
			returnSuccessors(state, hier, letter);
		}
		return mCache.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public int size() {
		throw new UnsupportedOperationException();
	}

	@Override
	public String sizeInformation() {
		return "size Information not available";
	}
}
