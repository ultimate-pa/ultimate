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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class tempDelaySet<L, S> {
	
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final Set<S> mStartStateSet;
	private final HashMap<S, Set<L>> mPrunedMap;
	private final HashMap<S, Set<L>> mSleepSetMap;
	private final HashMap<S, Set<Set<L>>> mDelaySetMap;
	private final ArrayDeque<S> mStateStack;
	private final ISleepSetOrder<S, L> mOrder;
	private final IIndependenceRelation<S, L> mIndependenceRelation;
	private final IPartialOrderVisitor<L, S> mVisitor;
	private boolean mExit;
	private final Set<S> mCompletedSet;
	private final HashMap<S, Set<L>> mExploredMap;

	public tempDelaySet(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IIndependenceRelation<S, L> independenceRelation, final ISleepSetOrder<S, L> sleepSetOrder,
			final IPartialOrderVisitor<L, S> visitor) {
		mOperand = operand;
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Sleep sets support only finite automata";

		mStartStateSet = CoreUtil.constructHashSet(operand.getInitialStates());
		assert (mStartStateSet.size() == 1) : "Only one initial state allowed";

		mPrunedMap = new HashMap<>();
		mSleepSetMap = new HashMap<>();
		mDelaySetMap = new HashMap<>();
		mStateStack = new ArrayDeque<>();
		mVisitor = visitor;
		mExit = false;
		mCompletedSet = new HashSet<>();
		mExploredMap = new HashMap<>();
		for (final S startState : mStartStateSet) {
			mSleepSetMap.put(startState, new HashSet<L>());
			mDelaySetMap.put(startState, new HashSet<Set<L>>());
			mExit = mVisitor.addStartState(startState);
			mStateStack.push(startState);
		}
		mOrder = sleepSetOrder;
		mIndependenceRelation = independenceRelation;
		search();
	}

	private void search() {

		while (!mExit && !mStateStack.isEmpty()) {

			final S currentState = mStateStack.pop();
			final ArrayList<L> successorTransitionList = new ArrayList<>();
			Set<L> currentSleepSet = mSleepSetMap.get(currentState);
			final Set<Set<L>> currentDelaySet = mDelaySetMap.get(currentState);
			
			if (mPrunedMap.get(currentState) == null) {
				mPrunedMap.put(currentState, mSleepSetMap.get(currentState));
				mExploredMap.put(currentState, new HashSet<L>());
				for (final OutgoingInternalTransition<L, S> transition : mOperand.internalSuccessors(currentState)) {
					if (!currentSleepSet.contains(transition.getLetter())) {
						successorTransitionList.add(transition.getLetter());
					}
				}
			} else if (!mCompletedSet.contains(currentState)) {
				for (final OutgoingInternalTransition<L, S> transition : mOperand.internalSuccessors(currentState)) {
					if (!currentSleepSet.contains(transition.getLetter())
							&& !mExploredMap.get(currentState).contains(transition.getLetter())) {
						successorTransitionList.add(transition.getLetter());
					}
				}
			} else if (!currentDelaySet.isEmpty()) {
				currentSleepSet = currentDelaySet.iterator().next();
				mSleepSetMap.put(currentState, currentSleepSet);
				currentDelaySet.remove(currentSleepSet);
				final Set<L> pruned = mPrunedMap.get(currentState);
				successorTransitionList.addAll(DataStructureUtils.difference(pruned, currentSleepSet));
				currentSleepSet = DataStructureUtils.intersection(currentSleepSet, pruned);
				//mSleepSetMap.put(currentState, currentSleepSet);
				mPrunedMap.put(currentState, currentSleepSet);
				mCompletedSet.remove(currentState);
			} else {
				final Set<L> pruned = mPrunedMap.get(currentState);
				successorTransitionList.addAll(DataStructureUtils.difference(pruned, currentSleepSet));
				currentSleepSet = DataStructureUtils.intersection(currentSleepSet, pruned);
				//mSleepSetMap.put(currentState, currentSleepSet);
				mPrunedMap.put(currentState, currentSleepSet);
				mCompletedSet.remove(currentState);
			}

			if (!successorTransitionList.isEmpty()) {
				final Comparator<L> order = mOrder.getOrder(currentState);
				successorTransitionList.sort(order);
				L transition = successorTransitionList.get(0);
				
				final var successors = mOperand.internalSuccessors(currentState, transition).iterator();
				if (!successors.hasNext()) {
					continue;
				}
				final var currentTransition = successors.next();
				assert !successors.hasNext() : "Automaton must be deterministic";
				final S succState = currentTransition.getSucc();
				Set<L> explored = mExploredMap.get(currentState);
				final Set<L> succSleepSet = DataStructureUtils.union(currentSleepSet, explored).stream()
						.filter(l -> mIndependenceRelation.contains(currentState, transition, l))
						.collect(Collectors.toCollection(HashSet::new));
				final Set<Set<L>> succDelaySet = new HashSet<>();
				mExit = mVisitor.discoverTransition(currentState, transition, succState);
				
				mStateStack.push(currentState);
				if (!mExit && mStateStack.contains(succState)) {
					succDelaySet.addAll(mDelaySetMap.get(succState));
					succDelaySet.add(succSleepSet);
					mDelaySetMap.put(succState, succDelaySet);
					mVisitor.delayState(currentState);
				} else {
					mSleepSetMap.put(succState, succSleepSet);
					mDelaySetMap.put(succState, succDelaySet);
					//mStateStack.push(currentState);
					mStateStack.push(succState);
					//mExit = mVisitor.discoverTransition(currentState, letterTransition, succState);
				}
				explored.add(transition);
				mExploredMap.put(currentState, explored);			
			} else {
				mVisitor.backtrackState(currentState);
				mSleepSetMap.put(currentState, currentSleepSet);
				//Set<L> explored = mExploredMap.get(currentState);
				//mPrunedMap.put(currentState, );
				mCompletedSet.add(currentState);
			}		
		}
	}

}
