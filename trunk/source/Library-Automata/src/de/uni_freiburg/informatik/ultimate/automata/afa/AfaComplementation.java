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

import java.util.List;
import java.util.Set;
import java.util.stream.StreamSupport;

/**
 * Represents an AFA that recognizes the complement of a given AFA's language.
 *
 * The complement automaton is constructed by switching accepting and non-accepting states, and dualizing each
 * transition formula (swapping true/false and conjunction/disjunction). In the case that the given AFA does not have
 * exactly one initial state, we must also introduce an additional initial state representing the conjunction of these
 * initial states.
 *
 * @param <L>
 *            the type of letters
 * @param <S>
 *            the type of the states in the given AFA
 * @param <C>
 *            the type of states in the complement AFA
 */
public class AfaComplementation<L, S, C> implements IAlternatingFiniteAutomaton<L, C> {
	private final IAlternatingFiniteAutomaton<L, S> mOperand;
	private final IAfaComplementationStateFactory<S, C> mStateFactory;

	private final C mInitialState;
	private final boolean mAdditionalInitialState;
	private final boolean mAdditionalInitialStateIsAccepting;

	public AfaComplementation(final IAlternatingFiniteAutomaton<L, S> operand,
			final IAfaComplementationStateFactory<S, C> stateFactory) {
		mOperand = operand;
		mStateFactory = stateFactory;

		final var operandInitials = operand.getInitialStates();
		final var initialIterator = operandInitials.iterator();
		if (initialIterator.hasNext()) {
			final S operandInitial = initialIterator.next();
			if (initialIterator.hasNext()) {
				// The operand has a disjunction of multiple initial states. We introduce a single new initial state.
				// It is accepting (the complement contains the empty word) iff no operand initial state is accepting.
				mInitialState = mStateFactory.makeInitial();
				mAdditionalInitialState = true;
				mAdditionalInitialStateIsAccepting =
						StreamSupport.stream(operandInitials.spliterator(), false).noneMatch(mOperand::isFinal);
			} else {
				// The operand has a single initial state. We re-use this state as the initial state of the complement.
				mInitialState = mStateFactory.makeComplementationState(operandInitial);
				mAdditionalInitialState = false;
				mAdditionalInitialStateIsAccepting = false;
			}
		} else {
			// The operand has no initial states at all (it recognizes the empty language).
			// The complement must accept all words, so we introduce a new, accepting initial state.
			mInitialState = mStateFactory.makeInitial();
			mAdditionalInitialState = true;
			mAdditionalInitialStateIsAccepting = true;
		}
	}

	@Override
	public Set<L> getAlphabet() {
		return mOperand.getAlphabet();
	}

	@Override
	public int size() {
		final int size = mOperand.size();
		if (size >= 0) {
			return size + (mAdditionalInitialState ? 1 : 0);
		}
		return size;
	}

	@Override
	public Iterable<C> getInitialStates() {
		return List.of(mInitialState);
	}

	@Override
	public boolean isInitial(final C state) {
		return mInitialState.equals(state);
	}

	@Override
	public boolean isFinal(final C state) {
		if (mAdditionalInitialState && mInitialState.equals(state)) {
			return mAdditionalInitialStateIsAccepting;
		}
		return !mOperand.isFinal(mStateFactory.getOriginal(state));
	}

	@Override
	public Bdd getSuccessors(final C state, final L letter, final BddFactory<C> bddFactory) {
		final var renamedFactory = bddFactory.withRenaming(mStateFactory::makeComplementationState);
		if (mAdditionalInitialState && mInitialState.equals(state)) {
			// The operand has a disjunction of multiple (or 0) initial states.
			// By dualization, this becomes a conjunction of the dualizations of each initial state's successor formula.
			// (In the case of 0 initial states, the empty conjunction is true, so all words are accepted.)
			return StreamSupport.stream(mOperand.getInitialStates().spliterator(), false)
					.map(initial -> mOperand.getSuccessors(initial, letter, renamedFactory).dual())
					.collect(bddFactory.toConjunction());
		}
		return mOperand.getSuccessors(mStateFactory.getOriginal(state), letter, renamedFactory).dual();
	}

	public interface IAfaComplementationStateFactory<S, C> {
		C makeInitial();

		C makeComplementationState(S state);

		S getOriginal(C state);
	}
}
