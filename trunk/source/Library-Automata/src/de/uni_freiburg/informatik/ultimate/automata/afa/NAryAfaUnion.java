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

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.SequencedSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Implements a union operation between n AFAs (for n >= 1). The union AFA is represented by the disjoint union of the
 * state spaces, where the initial states of all automata are initial states of the union.
 *
 * @param <L>
 * @param <S>
 * @param <U>
 */
public class NAryAfaUnion<L, S, U> implements IAlternatingFiniteAutomaton<L, U> {
	private final List<IAlternatingFiniteAutomaton<L, S>> mOperands;
	private final INAryAfaUnionStateFactory<S, U> mStateFactory;

	private final SequencedSet<U> mInitialStates;

	public NAryAfaUnion(final List<IAlternatingFiniteAutomaton<L, S>> operands,
			final INAryAfaUnionStateFactory<S, U> stateFactory) {
		mOperands = operands;
		mStateFactory = stateFactory;

		assert !mOperands.isEmpty() : "union must have at least one operand";
		// TODO use IAutomaton.sameAlphabet() once IAlternatingFiniteAutomaton extends IAutomaton
		assert mOperands.stream().allMatch(op -> op.getAlphabet().equals(operands.getFirst().getAlphabet()));

		mInitialStates = constructInitialStates();
	}

	private SequencedSet<U> constructInitialStates() {
		final var result = new LinkedHashSet<U>();
		int i = 0;
		for (final var operand : mOperands) {
			for (final var initial : operand.getInitialStates()) {
				result.add(mStateFactory.tagUnionState(initial, i));
			}
			i++;
		}
		return Collections.unmodifiableSequencedSet(result);
	}

	@Override
	public Set<L> getAlphabet() {
		return mOperands.getFirst().getAlphabet();
	}

	@Override
	public int size() {
		// automaton constructed on-demand
		return -1;
	}

	@Override
	public Iterable<U> getInitialStates() {
		return mInitialStates;
	}

	@Override
	public boolean isInitial(final U state) {
		return mInitialStates.contains(state);
	}

	@Override
	public boolean isFinal(final U state) {
		return mOperands.get(mStateFactory.getTagFromUnion(state)).isFinal(mStateFactory.getStateFromUnion(state));
	}

	@Override
	public Bdd getSuccessors(final U state, final L letter, final BddFactory<U> bddFactory) {
		final int tag = mStateFactory.getTagFromUnion(state);
		final S originalState = mStateFactory.getStateFromUnion(state);
		final var renamingFactory = bddFactory.withRenaming((final S s) -> mStateFactory.tagUnionState(s, tag));
		return mOperands.get(tag).getSuccessors(originalState, letter, renamingFactory);
	}

	public interface INAryAfaUnionStateFactory<S, U> {
		U tagUnionState(S state, int operandIndex);

		S getStateFromUnion(U taggedState);

		int getTagFromUnion(U taggedState);

		class Default<S> implements INAryAfaUnionStateFactory<S, Pair<S, Integer>> {
			@Override
			public Pair<S, Integer> tagUnionState(final S state, final int operandIndex) {
				return new Pair<>(state, operandIndex);
			}

			@Override
			public S getStateFromUnion(final Pair<S, Integer> taggedState) {
				return taggedState.getFirst();
			}

			@Override
			public int getTagFromUnion(final Pair<S, Integer> taggedState) {
				return taggedState.getSecond();
			}
		}
	}
}
