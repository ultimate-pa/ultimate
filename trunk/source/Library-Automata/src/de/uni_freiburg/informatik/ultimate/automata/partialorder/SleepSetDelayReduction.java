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
import java.util.Comparator;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Implementation of Partial Order Reduction for Deterministic Finite Automata using Sleep Sets for reduction and a
 * Delay Set for handling loops. This version can either construct a new automaton or search for an error trace.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            letter
 * @param <S>
 *            state
 */
public class SleepSetDelayReduction<L, S> {

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final ISleepSetOrder<S, L> mOrder;
	private final IIndependenceRelation<S, L> mIndependenceRelation;
	private final IPartialOrderVisitor<L, S> mVisitor;

	private final HashMap<S, Set<L>> mPrunedMap = new HashMap<>();
	private final HashMap<S, Set<L>> mSleepSetMap = new HashMap<>();
	private final ArrayDeque<S> mStateStack = new ArrayDeque<>();
	private final HashMap<S, Deque<Set<L>>> mDelaySetMap = new HashMap<>();

	/**
	 * Constructor for POR with Sleep Sets and Delay Set
	 *
	 * @param services
	 *            automata library services used e.g. for timeout
	 * @param operand
	 *            deterministic finite automaton
	 * @param independenceRelation
	 *            the independence relation used for reduction purposes
	 * @param sleepSetOrder
	 *            order for transition handling
	 * @param services
	 *            ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param visitor
	 *            the visitor class used for the reduction
	 * @throws AutomataOperationCanceledException
	 *             thrown if the reduction times out
	 */
	public SleepSetDelayReduction(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IIndependenceRelation<S, L> independenceRelation, final ISleepSetOrder<S, L> sleepSetOrder,
			final IPartialOrderVisitor<L, S> visitor) throws AutomataOperationCanceledException {
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Sleep sets support only finite automata";

		mOrder = sleepSetOrder;
		mIndependenceRelation = independenceRelation;
		mVisitor = visitor;
		mOperand = operand;

		final S startState = getOneAndOnly(operand.getInitialStates(), "initial state");
		mSleepSetMap.put(startState, new HashSet<>());
		mStateStack.push(startState);
		mVisitor.addStartState(startState);
		search(services);
	}

	private static <E> E getOneAndOnly(final Iterable<E> elements, final String thing) {
		final Iterator<E> iterator = elements.iterator();
		assert iterator.hasNext() : "Must have at least one " + thing;
		final E elem = iterator.next();
		assert !iterator.hasNext() : "Only one " + thing + " allowed";
		return elem;
	}

	private static <E> E getOnly(final Iterable<E> elements, final String errMsg) {
		final Iterator<E> iterator = elements.iterator();
		if (!iterator.hasNext()) {
			return null;
		}
		final E elem = iterator.next();
		assert !iterator.hasNext() : errMsg;
		return elem;
	}

	private void search(final AutomataLibraryServices services) throws AutomataOperationCanceledException {
		while (!mVisitor.isFinished() && !mStateStack.isEmpty()) {
			if (!services.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}

			final S currentState = mStateStack.peek();
			Set<L> currentSleepSet = mSleepSetMap.get(currentState);
			final ArrayList<L> successorTransitionList = new ArrayList<>();
			final Set<L> pruned = mPrunedMap.get(currentState);

			if (pruned == null) {
				// state not visited yet
				mPrunedMap.put(currentState, currentSleepSet);
				final boolean prune = mVisitor.discoverState(currentState);
				if (mVisitor.isFinished()) {
					return;
				}
				if (!prune) {
					successorTransitionList.addAll(
							DataStructureUtils.difference(mOperand.lettersInternal(currentState), currentSleepSet));
				} else {
					mVisitor.backtrackState(currentState);
					mStateStack.pop();
				}

			} else if (hasDelaySet(currentState)) {
				currentSleepSet = popDelaySet(currentState);
				successorTransitionList.addAll(DataStructureUtils.difference(pruned, currentSleepSet));
				currentSleepSet = DataStructureUtils.intersection(currentSleepSet, pruned);
				mSleepSetMap.put(currentState, currentSleepSet);
				mPrunedMap.put(currentState, currentSleepSet);
			} else {
				final boolean prune = mVisitor.discoverState(currentState);
				if (mVisitor.isFinished()) {
					return;
				}
				if (!prune) {
					successorTransitionList.addAll(DataStructureUtils.difference(pruned, currentSleepSet));
					currentSleepSet = DataStructureUtils.intersection(currentSleepSet, pruned);
					mSleepSetMap.put(currentState, currentSleepSet);
					mPrunedMap.put(currentState, currentSleepSet);
				}
				if (successorTransitionList.isEmpty()) {
					mVisitor.backtrackState(currentState);
					mStateStack.pop();
				}
			}

			// sort successorTransitionList according to the given order
			final Comparator<L> order = mOrder.getOrder(currentState);
			successorTransitionList.sort(order);
			final Set<L> explored = new HashSet<>();
			final Deque<S> successorStateList = new ArrayDeque<>(successorTransitionList.size());

			for (final L currentLetter : successorTransitionList) {
				final var currentTransition = getOnly(mOperand.internalSuccessors(currentState, currentLetter),
						"Automaton must be deterministic");
				if (currentTransition == null) {
					continue;
				}

				final S succState = currentTransition.getSucc();
				final boolean prune = mVisitor.discoverTransition(currentState, currentLetter, succState);
				if (mVisitor.isFinished()) {
					return;
				}
				if (prune) {
					explored.add(currentLetter);
					continue;
				}

				final Set<L> succSleepSet = Stream.concat(currentSleepSet.stream(), explored.stream())
						.filter(l -> mIndependenceRelation.contains(currentState, currentLetter, l))
						.collect(Collectors.toSet()); // TODO factor out
				if (mStateStack.contains(succState)) {
					enterDelaySet(currentState, succSleepSet);
					mVisitor.delayState(currentState);
					if (mVisitor.isFinished()) {
						return;
					}
				} else {
					mSleepSetMap.put(succState, succSleepSet);
					successorStateList.addFirst(succState);
				}
				explored.add(currentLetter);
			}
			for (final S succState : successorStateList) {
				mStateStack.push(succState);
			}
		}

	}

	private void enterDelaySet(final S state, final Set<L> delay) {
		final Deque<Set<L>> delaySets = mDelaySetMap.computeIfAbsent(state, x -> new ArrayDeque<>());
		delaySets.add(delay);
	}

	private boolean hasDelaySet(final S state) {
		final Deque<Set<L>> delaySets = mDelaySetMap.get(state);
		return delaySets != null && !delaySets.isEmpty();
	}

	private Set<L> popDelaySet(final S state) {
		return mDelaySetMap.get(state).poll();
	}
}
