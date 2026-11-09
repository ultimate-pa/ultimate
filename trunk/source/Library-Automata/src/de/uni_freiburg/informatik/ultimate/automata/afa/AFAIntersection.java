/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 Ecole Polytechnique
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
package de.uni_freiburg.informatik.ultimate.automata.afa;

import java.util.Set;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * Implements an intersection operation for two AFAs. The intersection AFA is represented simply by the disjoint union
 * of the two state spaces, together with a dedicated new initial state.
 *
 * @param <L>
 *            the type of letters
 * @param <S1>
 *            the type of states in the first operand
 * @param <S2>
 *            the type of states in the second operand
 * @param <S>
 *            the type of states in the intersection automaton
 */
public class AFAIntersection<L, S1, S2, S> implements IAlternatingFiniteAutomaton<L, S> {
	private final IAlternatingFiniteAutomaton<L, S1> mLeftOperand;
	private final IAlternatingFiniteAutomaton<L, S2> mRightOperand;
	private final IAFAIntersectionStateFactory<S1, S2, S> mStateFactory;

	private final S mInitialState;
	private final boolean mAcceptsEmpty;

	public AFAIntersection(final IAlternatingFiniteAutomaton<L, S1> leftOperand,
			final IAlternatingFiniteAutomaton<L, S2> rightOperand,
			final IAFAIntersectionStateFactory<S1, S2, S> stateFactory) {
		mLeftOperand = leftOperand;
		mRightOperand = rightOperand;
		mStateFactory = stateFactory;

		// TODO use IAutomaton.sameAlphabet() once IAlternatingFiniteAutomaton extends IAutomaton
		assert leftOperand.getAlphabet().equals(rightOperand.getAlphabet()) : "different alphabets";

		mInitialState = mStateFactory.makeInitial();
		mAcceptsEmpty = acceptsEmptyWord(leftOperand) && acceptsEmptyWord(rightOperand);
	}

	private static <X> Stream<X> stream(final Iterable<X> iterable) {
		return StreamSupport.stream(iterable.spliterator(), false);
	}

	private static <S, L> boolean acceptsEmptyWord(final IAlternatingFiniteAutomaton<L, S> automaton) {
		return stream(automaton.getInitialStates()).anyMatch(automaton::isInitial);
	}

	@Override
	public Set<L> getAlphabet() {
		return mLeftOperand.getAlphabet();
	}

	@Override
	public int size() {
		// automaton is constructed on-demand
		return -1;
	}

	@Override
	public Iterable<S> getInitialStates() {
		return Set.of(mInitialState);
	}

	@Override
	public boolean isInitial(final S state) {
		return mInitialState.equals(state);
	}

	@Override
	public boolean isFinal(final S state) {
		return switch (mStateFactory.deconstruct(state)) {
		case IntersectionState.Initial() -> mAcceptsEmpty;
		case IntersectionState.Left(final S1 leftState) -> mLeftOperand.isFinal(leftState);
		case IntersectionState.Right(final S2 rightState) -> mRightOperand.isFinal(rightState);
		};
	}

	@Override
	public Bdd getSuccessors(final S state, final L letter, final BddFactory<S> bddFactory) {
		return switch (mStateFactory.deconstruct(state)) {
		case IntersectionState.Initial() -> getInitialSuccessors(letter, bddFactory);
		case IntersectionState.Left(final S1 leftState) ->
				mLeftOperand.getSuccessors(leftState, letter, bddFactory.withRenaming(mStateFactory::makeLeft));
		case IntersectionState.Right(final S2 rightState) ->
				mRightOperand.getSuccessors(rightState, letter, bddFactory.withRenaming(mStateFactory::makeRight));
		};
	}

	private Bdd getInitialSuccessors(final L letter, final BddFactory<S> bddFactory) {
		final var leftFactory = bddFactory.withRenaming(mStateFactory::makeLeft);
		final var leftSuccessors = stream(mLeftOperand.getInitialStates())
				.map(s -> mLeftOperand.getSuccessors(s, letter, leftFactory)).collect(leftFactory.toDisjunction());

		final var rightFactory = bddFactory.withRenaming(mStateFactory::makeRight);
		final var rightSuccessors = stream(mRightOperand.getInitialStates())
				.map(s -> mRightOperand.getSuccessors(s, letter, rightFactory)).collect(rightFactory.toDisjunction());

		return leftSuccessors.and(rightSuccessors);
	}

	public interface IAFAIntersectionStateFactory<S1, S2, S> {
		S makeInitial();

		S makeLeft(S1 state);

		S makeRight(S2 state);

		IntersectionState<S1, S2> deconstruct(S state);

		class Default<S1, S2> implements IAFAIntersectionStateFactory<S1, S2, IntersectionState<S1, S2>> {
			@Override
			public IntersectionState<S1, S2> makeInitial() {
				return new IntersectionState.Initial<>();
			}

			@Override
			public IntersectionState<S1, S2> makeLeft(final S1 state) {
				return new IntersectionState.Left<>(state);
			}

			@Override
			public IntersectionState<S1, S2> makeRight(final S2 state) {
				return new IntersectionState.Right<>(state);
			}

			@Override
			public IntersectionState<S1, S2> deconstruct(final IntersectionState<S1, S2> state) {
				return state;
			}
		}
	}

	sealed interface IntersectionState<S1, S2> {
		record Initial<S1, S2>() implements IntersectionState<S1, S2> {
		}

		record Left<S1, S2>(S1 value) implements IntersectionState<S1, S2> {
		}

		record Right<S1, S2>(S2 value) implements IntersectionState<S1, S2> {
		}
	}
}
