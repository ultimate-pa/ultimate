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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Either;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TransformIterator;

/**
 * Automaton representing the monitor of the sequentialization of two given orders fst and snd.
 *
 * @param <L>
 *            letter type
 * @param <S>
 *            state type
 */
public class SequentialPreferenceOrderAutomaton<L, S1, S2, S> implements INwaOutgoingLetterAndTransitionProvider<L, S> {

	private final INwaOutgoingLetterAndTransitionProvider<L, S1> mLeftAutomaton;
	private final INwaOutgoingLetterAndTransitionProvider<L, S2> mRightAutomaton;
	private final ImmutableSet<L> mTransitionLetters;
	private final ISequentialStateFactory<S1, S2, S> mStateFactory;
	private final boolean mApplyFunctionAfterTransition;

	public SequentialPreferenceOrderAutomaton(final INwaOutgoingLetterAndTransitionProvider<L, S1> leftAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<L, S2> rightAutomaton,
			final ImmutableSet<L> transitionLetters, final ISequentialStateFactory<S1, S2, S> stateFactory,
			final boolean applyFunctionAfterTransition) {
		mLeftAutomaton = leftAutomaton;
		mRightAutomaton = rightAutomaton;
		mTransitionLetters = transitionLetters;
		mStateFactory = stateFactory;
		mApplyFunctionAfterTransition = applyFunctionAfterTransition;

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
		// We assume both automata have the same alphabet,
		// so it doesn't matter which one gets returned
		return mLeftAutomaton.getVpAlphabet();
	}

	@Override
	public S getEmptyStackState() {
		throw new UnsupportedOperationException("sequential preference order automata do not have stacks");
	}

	@Override
	public Iterable<S> getInitialStates() {
		final var initials = new ArrayList<S>();
		for (final var s : mLeftAutomaton.getInitialStates()) {
			initials.add(mStateFactory.createNewStateLeft(s));
		}
		return initials;
	}

	@Override
	public boolean isInitial(final S state) {
		final var original = mStateFactory.getOriginalState(state);
		if (original instanceof final Either.Left<S1, S2> originalS1) {
			return mLeftAutomaton.isInitial(originalS1.value());
		}
		return false;
	}

	@Override
	public boolean isFinal(final S state) {
		final var original = mStateFactory.getOriginalState(state);
		if (original instanceof final Either.Right<S1, S2> originalS2) {
			return mRightAutomaton.isFinal(originalS2.value());
		}
		return false;
	}

	@Override
	public int size() {
		return mLeftAutomaton.size() + mRightAutomaton.size();
	}

	@Override
	public String sizeInformation() {
		return "The first automaton has " + mLeftAutomaton.size() + " states, while the second one has "
				+ mRightAutomaton.size() + ".";
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, S>> internalSuccessors(final S state, final L letter) {
		switch (mStateFactory.getOriginalState(state)) {
		case Either.Left(final S1 original):
			if (mLeftAutomaton.isFinal(original) && mTransitionLetters.contains(letter)) {
				// Transition from the final states of mLeftAutomaton to the initial state of mRightAutomaton
				if (mApplyFunctionAfterTransition) {
					// It is assumed here that if mRightAutomaton has multiple initial states,
					// then it doesnt matter which one we transition to.
					// If needed this could probably be fixed by applying TransformIterator twice?
					return () -> new TransformIterator<>(
							mRightAutomaton
									.internalSuccessors(mRightAutomaton.getInitialStates().iterator().next(), letter)
									.iterator(),
							transition -> new OutgoingInternalTransition<>(transition.getLetter(),
									mStateFactory.createNewStateRight(transition.getSucc())));
				}
				return () -> new TransformIterator<>(mRightAutomaton.getInitialStates().iterator(),
						successor -> new OutgoingInternalTransition<>(letter,
								mStateFactory.createNewStateRight(successor)));
			}
			return () -> new TransformIterator<>(mLeftAutomaton.internalSuccessors(original, letter).iterator(),
					transition -> new OutgoingInternalTransition<>(transition.getLetter(),
							mStateFactory.createNewStateLeft(transition.getSucc())));
		case Either.Right(final S2 original):
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

	public interface ISequentialStateFactory<S1, S2, S> extends IStateFactory<S> {
		S createNewStateLeft(S1 state);

		S createNewStateRight(S2 state);

		Either<S1, S2> getOriginalState(S state);

		public class Default<S1, S2> implements ISequentialStateFactory<S1, S2, Either<S1, S2>> {
			@Override
			public Either<S1, S2> createNewStateLeft(final S1 state) {
				return new Either.Left<>(state);
			}

			@Override
			public Either<S1, S2> createNewStateRight(final S2 state) {
				return new Either.Right<>(state);
			}

			@Override
			public Either<S1, S2> getOriginalState(final Either<S1, S2> state) {
				return state;
			}
		}
	}
}
