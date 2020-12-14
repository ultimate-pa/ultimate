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
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SleepSetNewStateReduction<L, S, S2> {

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final Set<S> mStartStateSet;
	private final Set<S2> mVisitedSet;
	private final ArrayDeque<S2> mStateStack;
	private final HashMap<S2, Pair<S, Set<L>>> mStateMap;
	private final ISleepSetOrder<S, L> mOrder;
	private final IIndependenceRelation<S, L> mIndependenceRelation;
	private final ISleepSetStateFactory<L, S, S2> mStateFactory;
	// private final NestedWordAutomaton<L, S2> mReductionAutomaton;
	// private NestedRun<L, S> mAcceptingRun;
	private final IPartialOrderVisitor<L, S> mVisitor;
	private boolean mExit;
	private boolean mBacktrack;

	public SleepSetNewStateReduction(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IIndependenceRelation<S, L> independenceRelation, final ISleepSetOrder<S, L> sleepSetOrder,
			final ISleepSetStateFactory<L, S, S2> stateFactory, final IPartialOrderVisitor<L, S> visitor) {
		mStateFactory = stateFactory;
		mOperand = operand;
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Sleep sets support only finite automata";

		mStartStateSet = CoreUtil.constructHashSet(operand.getInitialStates());
		assert (mStartStateSet.size() == 1) : "Only one initial state allowed";

		mVisitedSet = new HashSet<>();
		mStateStack = new ArrayDeque<>();
		mStateMap = new HashMap<>();
		mVisitor = visitor;
		mExit = false;
		// mReductionAutomaton = new NestedWordAutomaton<L, S2>(services, mOperand.getVpAlphabet(), stateFactory);
		for (final S startState : mStartStateSet) {
			final Set<L> emptySet = new HashSet<>();
			final Pair<S, Set<L>> startStatePair = new Pair<>(startState, emptySet);
			final S2 newStartState = stateFactory.createSleepSetState(startState, emptySet);
			mExit = mVisitor.addStartState(startState);
			// mReductionAutomaton.addState(true, mOperand.isFinal(startState), newStartState);
			mStateStack.push(newStartState);
			mStateMap.put(newStartState, startStatePair);

		}
		mOrder = sleepSetOrder;
		mIndependenceRelation = independenceRelation;
		mBacktrack = false;
		search();
	}

	private void search() {

		while (!mExit && !mStateStack.isEmpty()) {

			final S2 currentSleepSetState = mStateStack.peek();
			final ArrayList<L> successorTransitionList = new ArrayList<>();
			final S currentState = mStateMap.get(currentSleepSetState).getFirst();
			final Set<L> currentSleepSet = mStateMap.get(currentSleepSetState).getSecond();
			/*
			if (!mBacktrack) {
				mVisitor.discoverState(currentState);
			}
			mBacktrack = false;*/

			if (!mVisitedSet.contains(currentSleepSetState)) {
				// state not visited with this sleep set
				mVisitor.discoverState(currentState);
				mVisitedSet.add(currentSleepSetState);
				for (final OutgoingInternalTransition<L, S> transition : mOperand.internalSuccessors(currentState)) {
					if (!currentSleepSet.contains(transition.getLetter())) {
						successorTransitionList.add(transition.getLetter());
					}
				}
			}
			
			else /*(successorTransitionList.isEmpty())*/ {
				mVisitor.backtrackState(currentState);
				mStateStack.pop();
				//mBacktrack = true;
			}

			// sort successorTransitionList according to the given order
			final Comparator<L> order = mOrder.getOrder(currentState);
			successorTransitionList.sort(order);
			final Set<L> explored = new HashSet<>();
			final ArrayList<S2> successorStateList = new ArrayList<>();

			for (final L letterTransition : successorTransitionList) {
				final var successors = mOperand.internalSuccessors(currentState, letterTransition).iterator();
				if (!successors.hasNext()) {
					continue;
				}
				final var currentTransition = successors.next();
				assert !successors.hasNext() : "Automaton must be deterministic";

				final S succState = currentTransition.getSucc();
				final Set<L> succSleepSet = DataStructureUtils.union(currentSleepSet, explored).stream()
						.filter(l -> mIndependenceRelation.contains(currentState, letterTransition, l))
						.collect(Collectors.toCollection(HashSet::new));
				final S2 succSleepSetState = mStateFactory.createSleepSetState(succState, succSleepSet);
				mStateMap.put(succSleepSetState, new Pair<>(succState, succSleepSet));
				mExit = mVisitor.discoverTransition(currentState, letterTransition, succState);
				successorStateList.add(succSleepSetState);
				// mStateStack.push(succSleepSetState);
				explored.add(letterTransition);
				if (mExit) {
					break;
				}
			}
			Collections.reverse(successorStateList);
			for (final S2 succSleepSetState : successorStateList) {
				mStateStack.push(succSleepSetState);
			}
		}
	}
}
