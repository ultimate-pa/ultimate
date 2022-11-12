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
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Implementation of Partial Order Reduction for Deterministic Finite Automata using Sleep Sets for reduction and a
 * Delay Set for handling loops.
 *
 * @author Marcel Ebbinghaus
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the input (and reduced) automaton
 * @param <S>
 *            The type of states in the input automaton
 * @param <R>
 *            The type of states in the reduced automaton
 */
public class SleepSetDelayReduction<L, S, R> {
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final ISleepSetStateFactory<L, S, R> mFactory;
	private final IDfsOrder<L, R> mOrder;
	private final IIndependenceRelation<R, L> mIndependenceRelation;
	private final IDfsVisitor<L, R> mVisitor;

	private final Deque<R> mStateStack = new ArrayDeque<>();
	private final Map<R, Set<L>> mSleepSetMap = new HashMap<>();
	private final Map<R, S> mStateMap = new HashMap<>();
	private final Map<R, Set<L>> mPrunedMap = new HashMap<>();
	private final Map<R, Deque<Set<L>>> mDelaySetMap = new HashMap<>();

	/**
	 * Constructor for POR with Sleep Sets and Delay Set
	 *
	 * @param services
	 *            automata library services used e.g. for timeout
	 * @param operand
	 *            input deterministic finite automaton that will be reduced
	 * @param factory
	 *            used to create states for the reduced automaton
	 * @param independenceRelation
	 *            the independence relation used for reduction purposes
	 * @param sleepSetOrder
	 *            order for transition handling
	 * @param visitor
	 *            the visitor class used for the reduction
	 *
	 * @throws AutomataOperationCanceledException
	 *             thrown if the reduction times out
	 */
	public SleepSetDelayReduction(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand, final ISleepSetStateFactory<L, S, R> factory,
			final IIndependenceRelation<R, L> independenceRelation, final IDfsOrder<L, R> sleepSetOrder,
			final IDfsVisitor<L, R> visitor) throws AutomataOperationCanceledException {
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Sleep sets support only finite automata";

		mOperand = operand;
		mFactory = factory;
		mIndependenceRelation = independenceRelation;
		mOrder = sleepSetOrder;
		mVisitor = visitor;

		final S startState = DataStructureUtils.getOneAndOnly(operand.getInitialStates(), "initial state");
		final R redStartState = getReductionState(startState, ImmutableSet.empty());
		mStateStack.push(redStartState);
		final boolean prune = mVisitor.addStartState(redStartState);
		if (!prune) {
			search(services);
		}
	}

	private R getReductionState(final S state, final ImmutableSet<L> sleepSet) {
		final R result = mFactory.createSleepSetState(state, sleepSet);
		mStateMap.put(result, state);
		mSleepSetMap.put(result, sleepSet);
		return result;
	}

	private void search(final AutomataLibraryServices services) throws AutomataOperationCanceledException {
		// mStateStack does not contain only the states truly "on the stack", but also their siblings.
		// This makes it unsuitable for detecting loops.
		final ArrayDeque<R> loopDetectionStack = new ArrayDeque<>();

		while (!mVisitor.isFinished() && !mStateStack.isEmpty()) {
			if (!services.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}

			final R currentRedState = mStateStack.peek();
			final S currentState = mStateMap.get(currentRedState);
			Set<L> currentSleepSet = mSleepSetMap.get(currentRedState);

			final ArrayList<L> successorTransitionList = new ArrayList<>();
			final Set<L> pruned = mPrunedMap.get(currentRedState);
			if (pruned == null) {
				// State not visited yet. Explore all enabled actions not in current sleep set.
				mPrunedMap.put(currentRedState, currentSleepSet);
				final boolean prune = mVisitor.discoverState(currentRedState);
				if (mVisitor.isFinished()) {
					return;
				}

				if (prune) {
					mVisitor.backtrackState(currentRedState, false);
					mStateStack.pop();
					continue;
				}

				// State is added to stack for first time.
				assert !loopDetectionStack.contains(currentRedState);
				loopDetectionStack.push(currentRedState);

				successorTransitionList
						.addAll(DataStructureUtils.difference(mOperand.lettersInternal(currentState), currentSleepSet));
			} else if (hasDelaySet(currentRedState)) {
				// State currently being visited is a loop head.
				// Explore actions not in sleep set when state is reached through loop body.
				currentSleepSet = popDelaySet(currentRedState);
				successorTransitionList.addAll(DataStructureUtils.difference(pruned, currentSleepSet));
				currentSleepSet = DataStructureUtils.intersection(currentSleepSet, pruned);
				mSleepSetMap.put(currentRedState, currentSleepSet);
				mPrunedMap.put(currentRedState, currentSleepSet);

				// If we are processing delay sets, then the state must be at the top of the stack.
				assert loopDetectionStack.peek() == currentRedState;
			} else {
				// Case 1: State has been visited before through a different path.
				// Explore actions that were previously pruned but are not in current sleep set.
				//
				// Case 2: After DFS has searched subtree rooted at this state (including handling all delay sets),
				// state is again at top of stack. Then it follows that no success will be in old sleep set
				// but not in current (they are equal). Hence backtrack the state.
				final boolean prune = mVisitor.discoverState(currentRedState);
				if (mVisitor.isFinished()) {
					return;
				}
				if (!prune) {
					successorTransitionList.addAll(DataStructureUtils.difference(pruned, currentSleepSet));
					currentSleepSet = DataStructureUtils.intersection(currentSleepSet, pruned);
					mSleepSetMap.put(currentRedState, currentSleepSet);
					mPrunedMap.put(currentRedState, currentSleepSet);
				}

				if (loopDetectionStack.peek() != currentRedState) {
					// Case 1: State not currently on stack, so put it there.
					loopDetectionStack.push(currentRedState);
				} else {
					// Case 2: We are currently backtracking. There should be nothing to explore.
					assert successorTransitionList.isEmpty() : "I was backtracking, but found new transitions: "
							+ successorTransitionList;
				}

				if (successorTransitionList.isEmpty()) {
					mVisitor.backtrackState(currentRedState, false);
					mStateStack.pop();
					final R popped = loopDetectionStack.pop();
					assert popped == currentRedState;
				}
			}

			// sort successorTransitionList according to the given order
			final Comparator<L> order = mOrder.getOrder(currentRedState);
			successorTransitionList.sort(order);
			final Set<L> explored = new HashSet<>();
			final Deque<R> successorStateList = new ArrayDeque<>(successorTransitionList.size());

			for (final L currentLetter : successorTransitionList) {
				final var currentTransitionOpt = DataStructureUtils.getOnly(
						mOperand.internalSuccessors(currentState, currentLetter), "Automaton must be deterministic");
				if (currentTransitionOpt.isEmpty()) {
					continue;
				}
				final var currentTransition = currentTransitionOpt.get();

				final S succState = currentTransition.getSucc();
				// TODO factor out sleep set successor computation
				final ImmutableSet<L> succSleepSet = Stream
						.concat(currentSleepSet.stream(), explored.stream()).filter(l -> mIndependenceRelation
								.isIndependent(currentRedState, currentLetter, l) == Dependence.INDEPENDENT)
						.collect(ImmutableSet.collector());
				final R successor = getReductionState(succState, succSleepSet);

				final boolean prune = mVisitor.discoverTransition(currentRedState, currentLetter, successor);
				if (mVisitor.isFinished()) {
					return;
				}
				if (prune) {
					explored.add(currentLetter);
					continue;
				}

				if (loopDetectionStack.contains(successor)) {
					enterDelaySet(successor, succSleepSet);
					mVisitor.delayState(successor);
					if (mVisitor.isFinished()) {
						return;
					}
				} else {
					successorStateList.addFirst(successor);
				}
				explored.add(currentLetter);
			}
			for (final R succState : successorStateList) {
				mStateStack.push(succState);
			}
		}

	}

	private void enterDelaySet(final R state, final Set<L> delay) {
		final Deque<Set<L>> delaySets = mDelaySetMap.computeIfAbsent(state, x -> new ArrayDeque<>());
		delaySets.add(delay);
	}

	private boolean hasDelaySet(final R state) {
		final Deque<Set<L>> delaySets = mDelaySetMap.get(state);
		return delaySets != null && !delaySets.isEmpty();
	}

	private Set<L> popDelaySet(final R state) {
		return mDelaySetMap.get(state).poll();
	}
}
