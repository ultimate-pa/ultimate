/*
 * Copyright (C) 2024 Emma Bach
 * Copyright (C) 2024 Marcel Ebbinghaus
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder.ProductPreferenceOrder.IProductPreferenceOrderStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Automaton representing the product of two given monitors mLeftAutomaton and mRightAutomaton. This corresponds to the
 * Automaton needed to solve thread-based problems.
 *
 * @param <L>
 *            letter type
 * @param <S1>
 *            state type of mLeftAutomaton
 * @param <S2>
 *            state type of mRightAutomaton
 * @param <S>
 *            state type of the product Monitor
 */
class ProductPreferenceOrderAutomaton<L, S1, S2, S> implements INwaOutgoingLetterAndTransitionProvider<L, S> {
	private final INwaOutgoingLetterAndTransitionProvider<L, S1> mLeftAutomaton;
	private final INwaOutgoingLetterAndTransitionProvider<L, S2> mRightAutomaton;
	private final IProductPreferenceOrderStateFactory<S1, S2, S> mStateFactory;

	public ProductPreferenceOrderAutomaton(final INwaOutgoingLetterAndTransitionProvider<L, S1> leftAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<L, S2> rightAutomaton,
			final IProductPreferenceOrderStateFactory<S1, S2, S> stateFactory) {
		mLeftAutomaton = leftAutomaton;
		mRightAutomaton = rightAutomaton;
		mStateFactory = stateFactory;

		assert NestedWordAutomataUtils.isFiniteAutomaton(leftAutomaton) : "calls and returns are not supported";
		assert NestedWordAutomataUtils.isFiniteAutomaton(rightAutomaton) : "calls and returns are not supported";
		assert leftAutomaton.getAlphabet().equals(rightAutomaton.getAlphabet()) : "Alphabets must be the same";
	}

	@Override
	@Deprecated
	public IStateFactory<S> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		// In the constructor, we assert that mLeftAutomaton and mRightAutomaton
		// must have the same Alphabet, so it doesn't matter which one gets returned.
		return mLeftAutomaton.getVpAlphabet();
	}

	@Override
	public S getEmptyStackState() {
		return null;
	}

	@Override
	public Iterable<S> getInitialStates() {
		final var initials = new ArrayList<S>();
		for (final var s1 : mLeftAutomaton.getInitialStates()) {
			for (final var s2 : mRightAutomaton.getInitialStates()) {
				initials.add(mStateFactory.createProductState(s1, s2));
			}
		}
		return initials;
	}

	@Override
	// State (a,b) is initial if a is initial in mLeftAutomaton and b is initial in mRightAutomaton
	public boolean isInitial(final S state) {
		return mLeftAutomaton.isInitial(mStateFactory.getLeftState(state))
				&& mRightAutomaton.isInitial(mStateFactory.getRightState(state));
	}

	@Override
	// State (a,b) is final if a is initial in mLeftAutomaton or b is initial in mRightAutomaton
	// Worth considering if and would be more sensible
	public boolean isFinal(final S state) {
		return mLeftAutomaton.isFinal(mStateFactory.getLeftState(state))
				|| mRightAutomaton.isFinal(mStateFactory.getRightState(state));
	}

	@Override
	public int size() {
		return mLeftAutomaton.size() * mRightAutomaton.size();
	}

	@Override
	public String sizeInformation() {
		return "The product automaton has " + size() + " states.";
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state, final L letter) {
		final Iterable<OutgoingInternalTransition<L, S1>> leftTransitions =
				mLeftAutomaton.internalSuccessors(mStateFactory.getLeftState(state), letter);
		final Iterable<OutgoingInternalTransition<L, S2>> rightTransitions =
				mRightAutomaton.internalSuccessors(mStateFactory.getRightState(state), letter);

		// return iterable (specifically an ArrayList) that contains all transitions ((a,b),letter)
		// where a is an internal successor of (mStateFactory.getLeftState(state),letter) in mLeftAutomaton
		// and b is an internal successor of (mStateFactory.getRightState(state),letter) in mRightAutomaton

		final ArrayList<OutgoingInternalTransition<L, S>> successors = new ArrayList<>();

		for (final OutgoingInternalTransition<L, S1> leftTransition : leftTransitions) {
			for (final OutgoingInternalTransition<L, S2> rightTransition : rightTransitions) {
				final S productState =
						mStateFactory.createProductState(leftTransition.getSucc(), rightTransition.getSucc());
				final OutgoingInternalTransition<L, S> productTransition =
						new OutgoingInternalTransition<>(letter, productState);
				successors.add(productTransition);
			}
		}
		return successors;
	}

	@Override
	public Iterable<OutgoingCallTransition<L, S>> callSuccessors(final S state, final L letter) {
		throw new UnsupportedOperationException("calls are not supported");
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, S>> returnSuccessors(final S state, final S hier, final L letter) {
		throw new UnsupportedOperationException("returns are not supported");
	}
}
