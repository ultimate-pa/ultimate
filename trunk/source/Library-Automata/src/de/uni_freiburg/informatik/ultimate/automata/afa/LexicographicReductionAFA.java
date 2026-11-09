/*
 * Copyright (C) 2026 Marcel Ebbinghaus
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 University of Freiburg
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
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.SequencedSet;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.afa.IIndependenceAutomaton.IndependenceLetter;
import de.uni_freiburg.informatik.ultimate.automata.afa.IIndependenceAutomaton.IndependentPair;
import de.uni_freiburg.informatik.ultimate.automata.afa.IIndependenceAutomaton.WrappedLetter;
import de.uni_freiburg.informatik.ultimate.automata.afa.LexicographicReductionAFA.ReductionState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

// This implementation follows the definition of the (original) prefix-suffix AFA's transition function in our paper.
// We extend it by allowing clients to pass an order automaton (for a monitor-based preference order).
// This requires ReductionState.Track(...) states to also track the current state of this order automaton.
public class LexicographicReductionAFA<L, S1, S2> implements IAlternatingFiniteAutomaton<L, ReductionState<L, S1, S2>> {
	// TODO: implement order automaton
	// The order automaton must be total and deterministic.
	private final INwaOutgoingLetterAndTransitionProvider<L, S2> mOrderAutomaton;
	private final IDfsOrder<L, S2> mOrder;

	private final Set<L> mAlphabet;

	// The independence automaton accepts words of the form "rho <ab> sigma" s.t. (rho,a,b,sigma) in I
	private final INwaOutgoingLetterAndTransitionProvider<IndependenceLetter<L>, S1> mIndependenceAutomaton;

	private final SequencedSet<ReductionState<L, S1, S2>> mInitialStates;

	private final BddManager<ReductionState<L, S1, S2>> mBddManager = new BddManager<>();
	private final UnifyHash<ReductionState<L, S1, S2>> mStateUnifier = new UnifyHash<>();

	// before the search, do an intersection of the current abstraction (transformed to an AFA) with the reduction AFA
	public LexicographicReductionAFA(final IDfsOrder<L, S2> order, final Set<L> alphabet,
			final INwaOutgoingLetterAndTransitionProvider<IndependenceLetter<L>, S1> independenceAutomaton,
			final INwaOutgoingLetterAndTransitionProvider<L, S2> orderAutomaton) {
		mOrder = order;
		mAlphabet = alphabet;
		mIndependenceAutomaton = independenceAutomaton;
		mOrderAutomaton = orderAutomaton;
		mInitialStates = constructInitialStates();
	}

	private SequencedSet<ReductionState<L, S1, S2>> constructInitialStates() {
		final Iterable<S1> independenceInitialStates = mIndependenceAutomaton.getInitialStates();
		final S2 orderInitialState =
				DataStructureUtils.getOneAndOnly(mOrderAutomaton.getInitialStates(), "initial state");
		final LinkedHashSet<ReductionState<L, S1, S2>> initialStates = stream(independenceInitialStates)
				.map(independenceState -> unify(new ReductionState.Track<>(independenceState, orderInitialState)))
				.collect(Collectors.toCollection(LinkedHashSet::new));

		return Collections.unmodifiableSequencedSet(initialStates);
	}

	@Override
	public Set<L> getAlphabet() {
		return mAlphabet;
	}

	@Override
	public int size() {
		// automaton is constructed on-demand
		return -1;
	}

	@Override
	public Iterable<ReductionState<L, S1, S2>> getInitialStates() {
		return mInitialStates;
	}

	@Override
	public boolean isInitial(final ReductionState<L, S1, S2> state) {
		return mInitialStates.contains(state);
	}

	@Override
	public boolean isFinal(final ReductionState<L, S1, S2> state) {
		return switch (state) {
		case ReductionState.Track(final S1 independenceState, final S2 orderState) -> true;
		case ReductionState.Sleep(final S1 independenceState, final L sleepLetter) -> true;
		case ReductionState.Wait(final S1 independenceState, final L waitLetter) -> false;
		case ReductionState.Check(final S1 independenceState) -> !mIndependenceAutomaton.isFinal(independenceState);
		};
	}

	@Override
	public Bdd<ReductionState<L, S1, S2>> getSuccessors(final ReductionState<L, S1, S2> state, final L letter) {
		final Iterable<OutgoingInternalTransition<IndependenceLetter<L>, S1>> independenceTransitions =
				mIndependenceAutomaton.internalSuccessors(state.independenceState(), new WrappedLetter<>(letter));

		switch (state) {
		case ReductionState.Track(final S1 independenceState, final S2 orderState):
			// /\ { track(q', q'') | independenceState --(letter)--> q' /\ orderState --(letter)--> q'' }
			final S2 orderSucc = getUniqueOrderSuccessor(orderState, letter);
			final var trackConjunction = conjunction(
					stream(independenceTransitions).map(t -> new ReductionState.Track<>(t.getSucc(), orderSucc)));

			Bdd<ReductionState<L, S1, S2>> smallerLetterConjunction = mBddManager.getTrue();
			for (final L letter2 : mAlphabet) {
				// TODO: use the Order from the orderState instead
				if (mOrder.getOrder(orderState).compare(letter2, letter) < 0) {
					// /\ { sleep(q', letter2) | independenceState --(letter)--> q' }
					final Bdd<ReductionState<L, S1, S2>> putToSleepDisjunct = conjunction(
							stream(independenceTransitions).map(t -> new ReductionState.Sleep<>(t.getSucc(), letter2)));

					// TODO: Discuss if this change is sufficient
					final IndependenceLetter<L> specialSymbol = new IndependentPair<>(letter, letter2);

					// /\ { wait(q', letter2) | independenceState --(letter/letter2)--> q' }
					final var specialSuccessors =
							mIndependenceAutomaton.internalSuccessors(independenceState, specialSymbol);
					final Bdd<ReductionState<L, S1, S2>> dependenceDisjunct = conjunction(
							stream(specialSuccessors).map(t -> new ReductionState.Wait<>(t.getSucc(), letter2)));

					smallerLetterConjunction = smallerLetterConjunction.and(putToSleepDisjunct.or(dependenceDisjunct));
				}
			}
			return trackConjunction.and(smallerLetterConjunction);

		case ReductionState.Sleep(final S1 independenceState, final L sleepLetter):
			if (Objects.equals(sleepLetter, letter)) {
				return mBddManager.getFalse();
			}

			// /\ { sleep(q', sleepLetter) | independenceState --(letter)--> q' }
			final Bdd<ReductionState<L, S1, S2>> stayAsleepDisjunct = conjunction(
					stream(independenceTransitions).map(t -> new ReductionState.Sleep<>(t.getSucc(), sleepLetter)));

			// /\ { wait(q', sleepLetter) | independenceState --(letter/sleepLetter)--> q' }
			final IndependenceLetter<L> specialSymbol = new IndependentPair<>(letter, sleepLetter);
			final var specialSuccessors = mIndependenceAutomaton.internalSuccessors(independenceState, specialSymbol);
			final Bdd<ReductionState<L, S1, S2>> dependenceDisjunct = conjunction(
					stream(specialSuccessors).map(t -> new ReductionState.Wait<>(t.getSucc(), sleepLetter)));

			return stayAsleepDisjunct.or(dependenceDisjunct);

		case ReductionState.Wait(final S1 independenceState, final L waitLetter):
			if (Objects.equals(waitLetter, letter)) {
				return mBddManager.variable(unify(new ReductionState.Check<>(independenceState)));
			}
			// /\ { wait(q', waitLetter) | independenceState --(letter)--> q' }
			return conjunction(
					stream(independenceTransitions).map(t -> new ReductionState.Wait<>(t.getSucc(), waitLetter)));

		case ReductionState.Check(final S1 independenceState):
			// /\ { check(q') | independenceState --(letter)--> q' }
			return conjunction(stream(independenceTransitions).map(t -> new ReductionState.Check<>(t.getSucc())));
		}
	}

	private ReductionState<L, S1, S2> unify(final ReductionState<L, S1, S2> state) {
		return mStateUnifier.unify(state);
	}

	private static <X> Stream<X> stream(final Iterable<X> items) {
		return StreamSupport.stream(items.spliterator(), false);
	}

	private Bdd<ReductionState<L, S1, S2>> conjunction(final Stream<? extends ReductionState<L, S1, S2>> conjuncts) {
		return conjuncts.map(this::unify).map(mBddManager::variable).collect(mBddManager.toConjunction());
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

	// Note: The records below override hashCode such that different types of states with similar contents -- e.g. the
	// states Sleep(q, a) and Wait(q, a) -- have (likely) different hash codes.
	sealed interface ReductionState<L, S1, S2> {
		S1 independenceState();

		record Track<L, S1, S2>(S1 independenceState, S2 orderState) implements ReductionState<L, S1, S2> {
			// simple record

			@Override
			public final int hashCode() {
				return Objects.hash(457, independenceState, orderState);
			}
		}

		record Sleep<L, S1, S2>(S1 independenceState, L sleepLetter) implements ReductionState<L, S1, S2> {
			// simple record

			@Override
			public final int hashCode() {
				return Objects.hash(659, independenceState, sleepLetter);
			}
		}

		record Wait<L, S1, S2>(S1 independenceState, L waitLetter) implements ReductionState<L, S1, S2> {
			// simple record

			@Override
			public final int hashCode() {
				return Objects.hash(839, independenceState, waitLetter);
			}
		}

		record Check<L, S1, S2>(S1 independenceState) implements ReductionState<L, S1, S2> {
			// simple record

			@Override
			public final int hashCode() {
				return Objects.hash(211, independenceState);
			}
		}
	}
}
