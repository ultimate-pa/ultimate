/*
 * Copyright (C) 2026 Marcel Ebbinghaus
 * Copyright (C) 2026 University of Freiburg
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

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.afa.AFAReductionAutomaton.AfaState;
import de.uni_freiburg.informatik.ultimate.automata.afa.AFAReductionAutomaton.AfaState.StateType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;

public class AFAReductionAutomaton<L, S1, S2> implements IAlternatingFiniteAutomaton<L, AfaState<L, S1, S2>> {

	private final IDfsOrder<L, S2> mOrder;
	private final Set<L> mAlphabet;
	private Set<AfaState<L, S1, S2>> mStates;
	private Set<AfaState<L, S1, S2>> mInitialStates;
	private Set<AfaState<L, S1, S2>> mFinalStates;
	final BddManager<AfaState<L, S1, S2>> mBddManager = new BddManager<>();
	private final IIndependencyAutomaton<L, S1> mIndependencyAutomaton;
	// TODO: implement order automaton
	// I assume the order automaton to be total and deterministic!
	private final INwaOutgoingLetterAndTransitionProvider<L, S2> mOrderAutomaton;
	private final Map<StateKey<L, S1, S2>, AfaState<L, S1, S2>> mStateCache = new HashMap<>();

	// before the search, do an intersection of the current abstraction (transformed to an AFA) with the reduction AFA
	public AFAReductionAutomaton(final IDfsOrder<L, S2> order, final Set<L> alphabet,
			final IIndependencyAutomaton<L, S1> independencyAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<L, S2> orderAutomaton) {
		mOrder = order;
		mAlphabet = alphabet;
		mIndependencyAutomaton = independencyAutomaton;
		mOrderAutomaton = orderAutomaton;
		constructInitialStates();
	}

	private void constructInitialStates() {
		final Iterable<S1> independencyInitialStates = mIndependencyAutomaton.getInitialStates();
		final Iterable<S2> orderInitialStates = mOrderAutomaton.getInitialStates();
		for (final S1 independencyState : independencyInitialStates) {
			for (final S2 orderState : orderInitialStates) {
				mInitialStates.add(new AfaState<>(StateType.TRACK, null, independencyState, orderState));
			}
		}
	}

	@Override
	public Set<L> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public int size() {
		return mStates.size();
	}

	@Override
	public Iterable<AfaState<L, S1, S2>> getInitialStates() {
		return mInitialStates;
	}

	@Override
	public boolean isInitial(final AfaState<L, S1, S2> state) {
		return mInitialStates.contains(state);
	}

	@Override
	public boolean isFinal(final AfaState<L, S1, S2> state) {
		return mFinalStates.contains(state);
	}

	@Override
	public Bdd<AfaState<L, S1, S2>> getSuccessors(final AfaState<L, S1, S2> state, final L letter) {

		final L sleepLetter = state.mSleepletter;
		final S1 independencyState = state.mIndependencyState;
		final S2 orderState = state.mOrderState;
		final Iterable<OutgoingInternalTransition<L, S1>> independencyTransitions =
				mIndependencyAutomaton.internalSuccessors(independencyState, letter);
		final S2 orderSucc = getUniqueOrderSuccessor(orderState, letter);
		Bdd<AfaState<L, S1, S2>> bddResult = mBddManager.getTrue();
		AfaState<L, S1, S2> succ;

		switch (state.mType) {
		case TRACK:
			for (final OutgoingInternalTransition<L, S1> t : independencyTransitions) {
				succ = getOrConstructState(StateType.TRACK, null, t.getSucc(), orderSucc);
				bddResult = bddResult.and(mBddManager.variable(succ));
			}
			Bdd<AfaState<L, S1, S2>> bddConjunction = mBddManager.getTrue();
			for (final L letter2 : mAlphabet) {
				Bdd<AfaState<L, S1, S2>> bddDisjunct1 = mBddManager.getTrue();
				Bdd<AfaState<L, S1, S2>> bddDisjunct2;
				// TODO: use the Order from the orderState instead
				if (mOrder.getOrder(orderState).compare(letter2, letter) < 0) {
					for (final OutgoingInternalTransition<L, S1> t : independencyTransitions) {
						succ = getOrConstructState(StateType.SLEEP, letter2, t.getSucc(), orderSucc);
						bddDisjunct1 = bddDisjunct1.and(mBddManager.variable(succ));

					}
					final Optional<L> specialSymbol = mIndependencyAutomaton.getSpecialSymbol(letter, letter2);
					if (specialSymbol.isPresent()) {
						final L symbol = specialSymbol.get();
						bddDisjunct2 = mBddManager.getTrue();
						for (final OutgoingInternalTransition<L, S1> t : mIndependencyAutomaton
								.internalSuccessors(independencyState, symbol)) {
							succ = getOrConstructState(StateType.WAIT, letter2, t.getSucc(), orderSucc);
							bddDisjunct2 = bddDisjunct2.and(mBddManager.variable(succ));

						}
					} else {
						bddDisjunct2 = mBddManager.getFalse();
					}
					bddConjunction = bddConjunction.and(bddDisjunct1.or(bddDisjunct2));
				}
			}
			bddResult = bddResult.and(bddConjunction);
			break;
		case SLEEP:
			if (Objects.equals(sleepLetter, letter)) {
				bddResult = mBddManager.getFalse();
			} else {
				Bdd<AfaState<L, S1, S2>> bddDisjunct1 = mBddManager.getTrue();
				Bdd<AfaState<L, S1, S2>> bddDisjunct2;
				for (final OutgoingInternalTransition<L, S1> t : independencyTransitions) {
					succ = getOrConstructState(StateType.SLEEP, sleepLetter, t.getSucc(), orderSucc);
					bddDisjunct1 = bddDisjunct1.and(mBddManager.variable(succ));

				}
				final Optional<L> specialSymbol = mIndependencyAutomaton.getSpecialSymbol(letter, sleepLetter);
				if (specialSymbol.isPresent()) {
					final L symbol = specialSymbol.get();
					bddDisjunct2 = mBddManager.getTrue();
					for (final OutgoingInternalTransition<L, S1> t : mIndependencyAutomaton
							.internalSuccessors(independencyState, symbol)) {
						succ = getOrConstructState(StateType.WAIT, sleepLetter, t.getSucc(), orderSucc);
						bddDisjunct2 = bddDisjunct2.and(mBddManager.variable(succ));

					}
				} else {
					bddDisjunct2 = mBddManager.getFalse();
				}
				bddResult = bddResult.and(bddDisjunct1.or(bddDisjunct2));
			}
			break;
		case WAIT:
			if (Objects.equals(sleepLetter, letter)) {
				succ = getOrConstructState(StateType.CHECK, null, independencyState, orderSucc);
				bddResult = mBddManager.variable(succ);

			} else {
				for (final OutgoingInternalTransition<L, S1> t : independencyTransitions) {
					succ = getOrConstructState(StateType.WAIT, sleepLetter, t.getSucc(), orderSucc);
					bddResult = bddResult.and(mBddManager.variable(succ));

				}
			}
			break;
		case CHECK:
			for (final OutgoingInternalTransition<L, S1> t1 : independencyTransitions) {
				succ = getOrConstructState(StateType.CHECK, null, t1.getSucc(), orderSucc);
				bddResult = bddResult.and(mBddManager.variable(succ));

			}
			break;
		}
		return bddResult;

	}

	public AfaState<L, S1, S2> getOrConstructState(final StateType type, final L sleepletter,
			final S1 independencyState, final S2 orderState) {

		final StateKey<L, S1, S2> key = new StateKey<>(type, sleepletter, independencyState, orderState);

		return mStateCache.computeIfAbsent(key, k -> {
			final AfaState<L, S1, S2> state =
					new AfaState<>(k.type(), k.sleepletter(), k.independencyState(), k.orderState());

			switch (k.type()) {
			case TRACK, SLEEP:
				mFinalStates.add(state);
				break;
			case WAIT:
				break;
			case CHECK:
				if (!mIndependencyAutomaton.isFinal(k.independencyState())) {
					mFinalStates.add(state);
				}
				break;
			default:
				throw new IllegalArgumentException("Unknown state type: " + k.type());
			}

			return state;
		});
	}

	record StateKey<L, S1, S2>(StateType type, L sleepletter, S1 independencyState, S2 orderState) {
	}

	static class AfaState<L, S1, S2> {
		StateType mType;
		L mSleepletter;
		S1 mIndependencyState;
		S2 mOrderState;

		enum StateType {
			TRACK, SLEEP, WAIT, CHECK
		}

		AfaState(final StateType type, final L sleepletter, final S1 indenepdencyState, final S2 orderState) {
			mType = type;
			mSleepletter = sleepletter;
			mIndependencyState = indenepdencyState;
			mOrderState = orderState;
		}

	}

	private S2 getUniqueOrderSuccessor(final S2 state, final L letter) {
		final Iterator<OutgoingInternalTransition<L, S2>> iterator =
				mOrderAutomaton.internalSuccessors(state, letter).iterator();

		if (!iterator.hasNext()) {
			throw new IllegalArgumentException(
					"Order automaton is not total for state " + state + " and letter " + letter);
		}

		final S2 successor = iterator.next().getSucc();

		if (iterator.hasNext()) {
			throw new IllegalArgumentException(
					"Order automaton is not deterministic for state " + state + " and letter " + letter);
		}

		return successor;
	}

	// maybe not needed anymore
	class AfaTransition<L2> {
		L2 mLetter;
		AfaState<L, S1, S2> mState;

		public AfaTransition(final L2 letter, final AfaState<L, S1, S2> state) {
			mLetter = letter;
			mState = state;
		}

		public L2 getLetter() {
			return mLetter;
		}

		public AfaState<L, S1, S2> getSucc() {
			return mState;
		}
	}
}
