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

import java.util.HashSet;
import java.util.Iterator;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.afa.AFAReductionAutomaton.AfaState;
import de.uni_freiburg.informatik.ultimate.automata.afa.IIndependenceAutomaton.IndependenceLetter;
import de.uni_freiburg.informatik.ultimate.automata.afa.IIndependenceAutomaton.WrappedLetter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

public class AFAReductionAutomaton<L, S1, S2> implements IAlternatingFiniteAutomaton<L, AfaState<L, S1, S2>> {

	private final IDfsOrder<L, S2> mOrder;
	private final Set<L> mAlphabet;
	private final Set<AfaState<L, S1, S2>> mStates = new HashSet<>();
	private final Set<AfaState<L, S1, S2>> mInitialStates = new HashSet<>();
	private final BddManager<AfaState<L, S1, S2>> mBddManager = new BddManager<>();

	private final UnifyHash<AfaState<L, S1, S2>> mStateUnifier = new UnifyHash<>();

	// The independence automaton accepts words of the form "rho <ab> sigma" s.t. (rho,a,b,sigma) in I
	private final IIndependenceAutomaton<L, S1> mIndependenceAutomaton;

	// TODO: implement order automaton
	// I assume the order automaton to be total and deterministic!
	private final INwaOutgoingLetterAndTransitionProvider<L, S2> mOrderAutomaton;

	// before the search, do an intersection of the current abstraction (transformed to an AFA) with the reduction AFA
	public AFAReductionAutomaton(final IDfsOrder<L, S2> order, final Set<L> alphabet,
			final IIndependenceAutomaton<L, S1> independenceAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<L, S2> orderAutomaton) {
		mOrder = order;
		mAlphabet = alphabet;
		mIndependenceAutomaton = independenceAutomaton;
		mOrderAutomaton = orderAutomaton;
		constructInitialStates();
	}

	private void constructInitialStates() {
		final Iterable<S1> independenceInitialStates = mIndependenceAutomaton.getInitialStates();
		final Iterable<S2> orderInitialStates = mOrderAutomaton.getInitialStates();
		for (final S1 independenceState : independenceInitialStates) {
			for (final S2 orderState : orderInitialStates) {
				mInitialStates.add(unify(new AfaState.Track<>(independenceState, orderState)));
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
		return switch (state) {
		case AfaState.Track(final S1 independenceState, final S2 orderState) -> true;
		case AfaState.Sleep(final S1 independenceState, final S2 orderState, final L sleepLetter) -> true;
		case AfaState.Wait(final S1 independenceState, final L waitLetter) -> false;
		case AfaState.Check(final S1 independenceState) -> !mIndependenceAutomaton.isFinal(independenceState);
		};
	}

	private <X> Stream<X> stream(final Iterable<X> items) {
		return StreamSupport.stream(items.spliterator(), false);
	}

	// this implementation follows the definition of the prefix-suffix AFA's transition function in our paper
	@Override
	public Bdd<AfaState<L, S1, S2>> getSuccessors(final AfaState<L, S1, S2> state, final L letter) {
		final Iterable<OutgoingInternalTransition<IndependenceLetter<L>, S1>> independenceTransitions =
				mIndependenceAutomaton.internalSuccessors(state.independenceState(), new WrappedLetter<>(letter));
		final S2 orderSucc;

		switch (state) {
		case AfaState.Track(final S1 independenceState, final S2 orderState):
			orderSucc = getUniqueOrderSuccessor(orderState, letter);

			// /\ { track(q', orderSucc) | independenceState --(letter)--> q' }
			final var trackConjunction =
					stream(independenceTransitions).map(t -> unify(new AfaState.Track<>(t.getSucc(), orderSucc)))
							.map(mBddManager::variable).collect(mBddManager.toConjunction());

			Bdd<AfaState<L, S1, S2>> smallerLetterConjunction = mBddManager.getTrue();
			for (final L letter2 : mAlphabet) {
				// TODO: use the Order from the orderState instead
				if (mOrder.getOrder(orderState).compare(letter2, letter) < 0) {
					// /\ { sleep(q', orderSucc, letter2) | independenceState --(letter)--> q' }
					final Bdd<AfaState<L, S1, S2>> bddDisjunct1 = stream(independenceTransitions)
							.map(t -> unify(new AfaState.Sleep<>(t.getSucc(), orderSucc, letter2)))
							.map(mBddManager::variable).collect(mBddManager.toConjunction());

					// TODO remove Optional from return type
					final IndependenceLetter<L> specialSymbol =
							mIndependenceAutomaton.getSpecialSymbol(letter, letter2).get();

					// /\ { wait(q', letter2) | independenceState --(letter/letter2)--> q' }
					final Bdd<AfaState<L, S1, S2>> bddDisjunct2 =
							stream(mIndependenceAutomaton.internalSuccessors(independenceState, specialSymbol))
									.map(t -> unify(new AfaState.Wait<>(t.getSucc(), letter2)))
									.map(mBddManager::variable).collect(mBddManager.toConjunction());

					smallerLetterConjunction = smallerLetterConjunction.and(bddDisjunct1.or(bddDisjunct2));
				}
			}
			return trackConjunction.and(smallerLetterConjunction);

		case AfaState.Sleep(final S1 independenceState, final S2 orderState, final L sleepLetter):
			if (Objects.equals(sleepLetter, letter)) {
				return mBddManager.getFalse();
			}

			orderSucc = getUniqueOrderSuccessor(orderState, letter);

			// /\ { sleep(q', orderSucc, sleepLetter) | independenceState --(letter)--> q' }
			final Bdd<AfaState<L, S1, S2>> stayAsleepDisjunct = stream(independenceTransitions)
					.map(t -> unify(new AfaState.Sleep<>(t.getSucc(), orderSucc, sleepLetter)))
					.map(mBddManager::variable).collect(mBddManager.toConjunction());

			// TODO remove Optional from return type
			final IndependenceLetter<L> specialSymbol =
					mIndependenceAutomaton.getSpecialSymbol(letter, sleepLetter).get();

			// /\ { wait(q', sleepLetter) | independenceState --(letter)--> q' }
			final Bdd<AfaState<L, S1, S2>> nonCommutativityDisjunct =
					stream(mIndependenceAutomaton.internalSuccessors(independenceState, specialSymbol))
							.map(t -> unify(new AfaState.Wait<>(t.getSucc(), sleepLetter))).map(mBddManager::variable)
							.collect(mBddManager.toConjunction());

			return stayAsleepDisjunct.or(nonCommutativityDisjunct);

		case AfaState.Wait(final S1 independenceState, final L waitLetter):
			if (Objects.equals(waitLetter, letter)) {
				return mBddManager.variable(unify(new AfaState.Check<>(independenceState)));
			}
			// /\ { wait(q', waitLetter) | independenceState --(letter)--> q' }
			return stream(independenceTransitions).map(t -> unify(new AfaState.Wait<>(t.getSucc(), waitLetter)))
					.map(mBddManager::variable).collect(mBddManager.toConjunction());

		case AfaState.Check(final S1 independenceState):
			// /\ { check(q') | independenceState --(letter)--> q' }
			return stream(independenceTransitions).map(t -> unify(new AfaState.Check<>(t.getSucc())))
					.map(mBddManager::variable).collect(mBddManager.toConjunction());
		}
	}

	private AfaState<L, S1, S2> unify(final AfaState<L, S1, S2> state) {
		return mStateUnifier.unify(state);
	}

	sealed interface AfaState<L, S1, S2> {
		S1 independenceState();

		record Track<L, S1, S2>(S1 independenceState, S2 orderState) implements AfaState<L, S1, S2> {
			// simple record
		}

		record Sleep<L, S1, S2>(S1 independenceState, S2 orderState, L sleepLetter) implements AfaState<L, S1, S2> {
			// simple record
		}

		record Wait<L, S1, S2>(S1 independenceState, L waitLetter) implements AfaState<L, S1, S2> {
			// simple record
		}

		record Check<L, S1, S2>(S1 independenceState) implements AfaState<L, S1, S2> {
			// simple record
		}
	}

	// method to ensure that the order automaton is total and deterministic
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
}
