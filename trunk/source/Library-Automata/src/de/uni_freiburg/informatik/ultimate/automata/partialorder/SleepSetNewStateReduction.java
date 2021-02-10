/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Implementation of the Sleep Set Reduction with new states.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            letter
 * @param <S>
 *            state
 * @param <S2>
 *            sleep set state
 */
public class SleepSetNewStateReduction<L, S, S2> { // TODO rename S2

	private final ISleepSetStateFactory<L, S, S2> mStateFactory;
	private final ISleepSetOrder<S, L> mOrder;
	private final IIndependenceRelation<S, L> mIndependenceRelation;
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final IPartialOrderVisitor<L, S> mVisitor; // TODO should use S2

	private final Set<S2> mVisitedSet = new HashSet<>();
	private final ArrayDeque<S2> mStateStack = new ArrayDeque<>();
	private final HashMap<S2, Pair<S, Set<L>>> mStateMap = new HashMap<>(); // TODO split into 2 maps

	/**
	 * Constructor of the Sleep Set Reduction with new states.
	 *
	 * @param operand
	 *            deterministic finite automaton
	 * @param independenceRelation
	 *            the independence relation used for reduction purposes
	 * @param sleepSetOrder
	 *            order for transition handling
	 * @param stateFactory
	 *            state factory
	 * @param visitor
	 *            the visitor class used for the reduction
	 */
	public SleepSetNewStateReduction(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IIndependenceRelation<S, L> independenceRelation, final ISleepSetOrder<S, L> sleepSetOrder,
			final ISleepSetStateFactory<L, S, S2> stateFactory, final IPartialOrderVisitor<L, S> visitor) {
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Sleep sets support only finite automata";

		mStateFactory = stateFactory;
		mOrder = sleepSetOrder;
		mIndependenceRelation = independenceRelation;
		mOperand = operand;
		mVisitor = visitor;

		final S startState = getOneAndOnly(operand.getInitialStates(), "initial state");
		final S2 newStartState = getSleepSetState(startState, Collections.emptySet());
		mVisitor.addStartState(startState);
		mStateStack.push(newStartState);
		search();
	}

	// TODO eliminate duplication
	private static <E> E getOneAndOnly(final Iterable<E> elements, final String thing) {
		final Iterator<E> iterator = elements.iterator();
		assert iterator.hasNext() : "Must have at least one " + thing;
		final E elem = iterator.next();
		assert !iterator.hasNext() : "Only one " + thing + " allowed";
		return elem;
	}

	// TODO eliminate duplication
	private static <E> E getOnly(final Iterable<E> elements, final String errMsg) {
		final Iterator<E> iterator = elements.iterator();
		if (!iterator.hasNext()) {
			return null;
		}
		final E elem = iterator.next();
		assert !iterator.hasNext() : errMsg;
		return elem;
	}

	private void search() {
		while (!mVisitor.isFinished() && !mStateStack.isEmpty()) {

			final S2 currentSleepSetState = mStateStack.peek();
			final ArrayList<L> successorTransitionList = new ArrayList<>();
			final S currentState = mStateMap.get(currentSleepSetState).getFirst();
			final Set<L> currentSleepSet = mStateMap.get(currentSleepSetState).getSecond();

			// If state not visited with this sleep set, determine transitions to explore.
			if (!mVisitedSet.contains(currentSleepSetState)) {
				mVisitedSet.add(currentSleepSetState);
				final boolean prune = mVisitor.discoverState(currentState);
				if (mVisitor.isFinished()) {
					return;
				}
				if (!prune) {
					successorTransitionList.addAll(
							DataStructureUtils.difference(mOperand.lettersInternal(currentState), currentSleepSet));
				}
			}

			// If all transitions have been explored or pruned (or there were none), backtrack.
			if (successorTransitionList.isEmpty()) {
				mVisitor.backtrackState(currentState);
				mStateStack.pop();
				continue;
			}

			// sort successorTransitionList according to the given order
			successorTransitionList.sort(mOrder.getOrder(currentState));
			final Set<L> explored = new HashSet<>();
			final ArrayList<S2> successorStateList = new ArrayList<>();

			// TODO (Dominik 2021-01-24) Consider pre-computing independence between different outgoing transitions,
			// and between outgoing transitions and sleep set members, at an earlier point. The background is that
			// in the usage of this class in SleepSetCegar, there is competition for a ManagedScript between the
			// (interpolant) automaton and the independence checks. The fewer batches of independence checks, the
			// fewer times the ManagedScript need change lock ownership.

			for (final L currentLetter : successorTransitionList) {
				final var currentTransition = getOnly(mOperand.internalSuccessors(currentState, currentLetter),
						"Automaton must be deterministic");
				if (currentTransition == null) {
					continue;
				}

				final S succState = currentTransition.getSucc();
				final Set<L> succSleepSet = DataStructureUtils.union(currentSleepSet, explored).stream()
						.filter(l -> mIndependenceRelation.contains(currentState, currentLetter, l))
						.collect(Collectors.toCollection(HashSet::new));
				final S2 succSleepSetState = getSleepSetState(succState, succSleepSet);

				final boolean prune = mVisitor.discoverTransition(currentState, currentLetter, succState);
				if (mVisitor.isFinished()) {
					return;
				}
				if (!prune) {
					successorStateList.add(succSleepSetState);
				}
				explored.add(currentLetter);
			}
			Collections.reverse(successorStateList);
			for (final S2 succSleepSetState : successorStateList) {
				mStateStack.push(succSleepSetState);
			}
		}
	}

	private S2 getSleepSetState(final S state, final Set<L> sleepset) {
		final S2 newState = mStateFactory.createSleepSetState(state, sleepset);
		mStateMap.put(newState, new Pair<>(state, sleepset));
		return newState;
	}
}
