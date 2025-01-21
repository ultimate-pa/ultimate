/*
 * Copyright (C) 2024 Emma Bach
 * Copyright (C) 2024 Marcel Ebbinghaus
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.OptionalEither;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedIteratorNoopConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TransformIterator;

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
 *            The state type of the combination. Using the default state factory, this will be
 *            {@code OptionalEither<S1,S2>}.
 *
 *
 */

public class IfElsePreferenceOrderAutomaton<L, S1, S2, S> implements INwaOutgoingLetterAndTransitionProvider<L, S> {

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
		throw new UnsupportedOperationException("preference order automata do not have stacks");
	}

	@Override
	public Iterable<S> getInitialStates() {
		final var stateList = new ArrayList<S>();
		stateList.add(mStateFactory.createNewBeginningState());
		return stateList;
	}

	@Override
	public boolean isInitial(final S state) {
		return switch (mStateFactory.getOriginalState(state)) {
		case OptionalEither.Right(final S2 original) -> false;
		case OptionalEither.Left(final S1 original) -> false;
		case OptionalEither.Neither() -> true;
		};
	}

	@Override
	public boolean isFinal(final S state) {
		return switch (mStateFactory.getOriginalState(state)) {
		case OptionalEither.Left(final S1 original) -> mLeftAutomaton.isFinal(original);
		case OptionalEither.Right(final S2 original) -> mRightAutomaton.isFinal(original);
		case OptionalEither.Neither() -> false;
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
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state, final L letter) {
		switch (mStateFactory.getOriginalState(state)) {

		// Automaton is currently in the initial State
		case OptionalEither.Neither():
			// letter represents transition into if branch -> transition into left automaton
			if (mIfBranchLetters.contains(letter)) {
				return () -> new TransformIterator<>(
						new NestedIteratorNoopConstruction<>(mLeftAutomaton.getInitialStates().iterator(),
								q -> mLeftAutomaton.internalSuccessors(q, letter).iterator()),
						transition -> new OutgoingInternalTransition<>(transition.getLetter(),
								mStateFactory.createNewStateLeft(transition.getSucc())));
			}
			// letter doesn't represent transition into if branch
			// -> letter leads into else branch -> transition into right automaton
			return () -> new TransformIterator<>(
					new NestedIteratorNoopConstruction<>(mLeftAutomaton.getInitialStates().iterator(),
							q -> mLeftAutomaton.internalSuccessors(q, letter).iterator()),
					transition -> new OutgoingInternalTransition<>(transition.getLetter(),
							mStateFactory.createNewStateLeft(transition.getSucc())));

		// Automaton is already in if branch
		case OptionalEither.Left(final S1 original):
			return () -> new TransformIterator<>(mLeftAutomaton.internalSuccessors(original, letter).iterator(),
					transition -> new OutgoingInternalTransition<>(transition.getLetter(),
							mStateFactory.createNewStateLeft(transition.getSucc())));

		// Automaton is already in else branch
		case OptionalEither.Right(final S2 original):
			return () -> new TransformIterator<>(mRightAutomaton.internalSuccessors(original, letter).iterator(),
					transition -> new OutgoingInternalTransition<>(transition.getLetter(),
							mStateFactory.createNewStateRight(transition.getSucc())));
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

	public interface IIfElseStateFactory<S1, S2, S> extends IStateFactory<S> {
		S createNewStateLeft(S1 state);

		S createNewStateRight(S2 state);

		S createNewBeginningState();

		OptionalEither<S1, S2> getOriginalState(S state);

		public class Default<S1, S2> implements IIfElseStateFactory<S1, S2, OptionalEither<S1, S2>> {

			@Override
			public OptionalEither<S1, S2> createNewStateLeft(final S1 state) {
				return new OptionalEither.Left<>(state);
			}

			@Override
			public OptionalEither<S1, S2> createNewStateRight(final S2 state) {
				return new OptionalEither.Right<>(state);
			}

			@Override
			public OptionalEither<S1, S2> createNewBeginningState() {
				return new OptionalEither.Neither<>();
			}

			@Override
			public OptionalEither<S1, S2> getOriginalState(final OptionalEither<S1, S2> state) {
				return state;
			}
		}
	}
}
