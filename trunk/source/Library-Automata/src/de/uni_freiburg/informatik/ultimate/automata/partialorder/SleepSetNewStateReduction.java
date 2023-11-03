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
 * Implementation of the Sleep Set Reduction with new states. This variant explores a reduction automaton that partially
 * unfolds and unrolls the input automaton, in order to guarantee a reduction that is minimal (in terms of the accepted
 * language).
 *
 * @deprecated Superseded by {@link MinimalSleepSetReduction}
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters of the input automaton.
 * @param <S>
 *            The type of states of the input automaton.
 * @param <R>
 *            The type of states of the reduced automaton that is built on-the-fly.
 */
@Deprecated(since = "2021-03-22")
public class SleepSetNewStateReduction<L, S, R> {
	private final ISleepSetStateFactory<L, S, R> mStateFactory;
	private final IDfsOrder<L, R> mOrder;
	private final IIndependenceRelation<S, L> mIndependenceRelation;
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final IDfsVisitor<L, R> mVisitor;

	private final Set<R> mVisitedSet = new HashSet<>();
	private final ArrayDeque<R> mStateStack = new ArrayDeque<>();
	private final Map<R, Set<L>> mSleepMap = new HashMap<>();
	private final Map<R, S> mStateMap = new HashMap<>();

	/**
	 * Constructor of the Sleep Set Reduction with new states.
	 *
	 * @param services
	 *            automata library services used e.g. for timeout
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
	 * @throws AutomataOperationCanceledException
	 *             thrown if the reduction times out
	 */
	public SleepSetNewStateReduction(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final ISleepSetStateFactory<L, S, R> stateFactory, final IIndependenceRelation<S, L> independenceRelation,
			final IDfsOrder<L, R> sleepSetOrder, final IDfsVisitor<L, R> visitor)
			throws AutomataOperationCanceledException {
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Sleep sets support only finite automata";

		mStateFactory = stateFactory;
		mOrder = sleepSetOrder;
		mIndependenceRelation = independenceRelation;
		mOperand = operand;
		mVisitor = visitor;

		final S startState = DataStructureUtils.getOneAndOnly(operand.getInitialStates(), "initial state");
		final R newStartState = getSleepSetState(startState, ImmutableSet.empty());
		mStateStack.push(newStartState);
		final boolean prune = mVisitor.addStartState(newStartState);
		if (!prune) {
			search(services);
		}
	}

	private void search(final AutomataLibraryServices services) throws AutomataOperationCanceledException {
		while (!mVisitor.isFinished() && !mStateStack.isEmpty()) {
			if (!services.getProgressAwareTimer().continueProcessing()) {
				throw new AutomataOperationCanceledException(this.getClass());
			}

			final R currentSleepSetState = mStateStack.peek();
			final ArrayList<L> successorTransitionList = new ArrayList<>();
			final S currentState = mStateMap.get(currentSleepSetState);
			final Set<L> currentSleepSet = mSleepMap.get(currentSleepSetState);

			// If state not visited with this sleep set, determine transitions to explore.
			if (!mVisitedSet.contains(currentSleepSetState)) {
				mVisitedSet.add(currentSleepSetState);
				final boolean prune = mVisitor.discoverState(currentSleepSetState);
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
				mVisitor.backtrackState(currentSleepSetState, false);
				mStateStack.pop();
				continue;
			}

			// sort successorTransitionList according to the given order
			successorTransitionList.sort(mOrder.getOrder(currentSleepSetState));
			final Set<L> explored = new HashSet<>();
			final ArrayDeque<R> successorStateList = new ArrayDeque<>(successorTransitionList.size());

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
								.isIndependent(currentState, currentLetter, l) == Dependence.INDEPENDENT)
						.collect(ImmutableSet.collector());
				final R succSleepSetState = getSleepSetState(succState, succSleepSet);

				final boolean prune =
						mVisitor.discoverTransition(currentSleepSetState, currentLetter, succSleepSetState);
				if (mVisitor.isFinished()) {
					return;
				}
				if (!prune) {
					successorStateList.addFirst(succSleepSetState);
				}
				explored.add(currentLetter);
			}
			for (final R succState : successorStateList) {
				mStateStack.push(succState);
			}
		}
	}

	private R getSleepSetState(final S state, final ImmutableSet<L> sleepset) {
		final R newState = mStateFactory.createSleepSetState(state, sleepset);
		mStateMap.put(newState, state);
		mSleepMap.put(newState, sleepset);
		return newState;
	}
}
