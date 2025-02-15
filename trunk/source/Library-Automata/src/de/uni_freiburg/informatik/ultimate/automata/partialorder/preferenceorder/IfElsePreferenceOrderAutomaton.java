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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DeterminismUtil;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Automaton representing a combination of two given monitors mFirstAutomaton and mSecondAutomaton that chooses which of
 * the two monitors to use based on which branch of an if-statement the program enters.
 *
 * @param <L>
 *            The type of the transition letters.
 * @param <S1>
 *            The state type of mLeftAutomaton.
 * @param <S2>
 *            The state type of mRightAutomaton.
 * @param <S>
 *            The state type of the combination.
 */
class IfElsePreferenceOrderAutomaton<L, S1, S2, S> implements INwaOutgoingLetterAndTransitionProvider<L, S> {
	private final S mInitialState;
	private final INwaOutgoingLetterAndTransitionProvider<L, S1> mLeftAutomaton;
	private final INwaOutgoingLetterAndTransitionProvider<L, S2> mRightAutomaton;
	private final ImmutableSet<L> mIfBranchLetters;
	private final IIfElseStateFactory<S1, S2, S> mStateFactory;

	public IfElsePreferenceOrderAutomaton(final INwaOutgoingLetterAndTransitionProvider<L, S1> leftAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<L, S2> rightAutomaton, final ImmutableSet<L> ifBranchLetters,
			final IIfElseStateFactory<S1, S2, S> stateFactory) {
		mLeftAutomaton = leftAutomaton;
		mRightAutomaton = rightAutomaton;
		mIfBranchLetters = ifBranchLetters;
		mStateFactory = stateFactory;
		mInitialState = stateFactory.createNewBeginningState();

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
		return List.of(mInitialState);
	}

	@Override
	public boolean isInitial(final S state) {
		return switch (mStateFactory.getOriginalState(state)) {
		case IfThenElseState.Else(final S2 original) -> false;
		case IfThenElseState.Then(final S1 original) -> false;
		case IfThenElseState.Initial() -> true;
		};
	}

	@Override
	public boolean isFinal(final S state) {
		return switch (mStateFactory.getOriginalState(state)) {
		case IfThenElseState.Then(final S1 original) -> mLeftAutomaton.isFinal(original);
		case IfThenElseState.Else(final S2 original) -> mRightAutomaton.isFinal(original);
		case IfThenElseState.Initial() -> false;
		};
	}

	@Override
	public int size() {
		return mLeftAutomaton.size() + mRightAutomaton.size() + 1;
	}

	@Override
	public String sizeInformation() {
		return "The combined if/else-automaton has " + size() + " states.";
	}

	@Override
	public List<OutgoingInternalTransition<L, S>> internalSuccessors(final S state, final L letter) {
		switch (mStateFactory.getOriginalState(state)) {
		// Automaton is currently in the initial State
		// letter represents transition into if branch -> transition into left automaton
		case IfThenElseState.Initial() when mIfBranchLetters.contains(letter):
			// TODO (Dominik 2025-02-12) We duplicate some logic here that should not be necessary.
			// The reason for this duplication is that we observed strange behaviour that we can currently only explain
			// by an apparent compiler bug: the "when" guard in the line above seems to be simply ignored; and this
			// case body is entered regardless of what the guard evaluates to.
			//
			// To reproduce this strange behaviour, follow the instructions in mattermost [1] for the example ex08.bpl,
			// and set breakpoints in this as well as the next case body. You will observe that the breakpoint in this
			// case body is also hit for letter=[76] despite it not being in mIfBranchLetters, and the breakpoint in the
			// next case body is never hit.
			//
			// [1] https://chat.sopranium.de/swt/pl/8jye3n4jqjyijqrtgnr8itdbbe
			if (mIfBranchLetters.contains(letter)) {
				final S1 leftInitial = DeterminismUtil.getInitialState(mLeftAutomaton);
				final var successor =
						DeterminismUtil.getTotalDeterministicInternalSuccessor(mLeftAutomaton, leftInitial, letter);
				return List.of(new OutgoingInternalTransition<>(letter, mStateFactory.createNewStateLeft(successor)));
			} else {
				System.err.println(
						getClass().getSimpleName() + ": Inconsistent evaluation of switch guard and if condition");
				final S2 rightInitial = DeterminismUtil.getInitialState(mRightAutomaton);
				final var successor =
						DeterminismUtil.getTotalDeterministicInternalSuccessor(mRightAutomaton, rightInitial, letter);
				return List.of(new OutgoingInternalTransition<>(letter, mStateFactory.createNewStateRight(successor)));
			}

			// Automaton is currently in the initial State
			// but letter doesn't represent transition into if branch
			// -> letter leads into else branch -> transition into right automaton
		case IfThenElseState.Initial():
			final S2 rightInitial = DeterminismUtil.getInitialState(mRightAutomaton);
			final S2 successor =
					DeterminismUtil.getTotalDeterministicInternalSuccessor(mRightAutomaton, rightInitial, letter);
			return List.of(new OutgoingInternalTransition<>(letter, mStateFactory.createNewStateRight(successor)));

		// Automaton is already in if branch
		case IfThenElseState.Then(final S1 original):
			final S1 thenSuccessor =
					DeterminismUtil.getTotalDeterministicInternalSuccessor(mLeftAutomaton, original, letter);
			return List.of(new OutgoingInternalTransition<>(letter, mStateFactory.createNewStateLeft(thenSuccessor)));

		// Automaton is already in else branch
		case IfThenElseState.Else(final S2 original):
			final S2 elseSuccessor =
					DeterminismUtil.getTotalDeterministicInternalSuccessor(mRightAutomaton, original, letter);
			return List.of(new OutgoingInternalTransition<>(letter, mStateFactory.createNewStateRight(elseSuccessor)));
		}
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
