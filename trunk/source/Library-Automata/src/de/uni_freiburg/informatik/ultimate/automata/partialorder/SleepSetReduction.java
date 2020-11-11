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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SleepSetReduction<L, S, S2> extends UnaryNwaOperation<L, S, IStateFactory<S>> {

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final Set<S> mStartStateSet;
	private final Set<S2> mVisitedSet;
	private final ArrayDeque<S2> mStateStack;
	private final HashMap<S2, Pair<S, Set<L>>> mStateMap;
	private final ISleepSetOrder<S, L> mOrder;
	private final IIndependenceRelation<S, L> mIndependenceRelation;
	private final NestedWordAutomaton<L, S2> mReductionAutomaton;
	private final ISleepSetStateFactory<L, S, S2> mStateFactory;
	private final HashMap<S, Set<L>> mPrunedMap;
	private final HashMap<S, Set<Set<L>>> mDelaySetMap;
	private final Boolean mMode;
	//private BasicCegarLoop.SleepSetMode mMode;
	
	public SleepSetReduction(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IIndependenceRelation<S, L> independenceRelation, final ISleepSetOrder<S, L> sleepSetOrder,
			final AutomataLibraryServices services, final ISleepSetStateFactory<L, S, S2> stateFactory,
			//final BasicCegarLoop.SleepSetMode mode
			final Boolean mode) {
		super(services);
		mStateFactory = stateFactory;
		mOperand = operand;
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Sleep sets support only finite automata";

		mStartStateSet = CoreUtil.constructHashSet(operand.getInitialStates());
		assert (mStartStateSet.size() == 1) : "Only one initial state allowed";
		
		mPrunedMap = new HashMap<>();
		mDelaySetMap = new HashMap<>();
		mVisitedSet = new HashSet<>();
		mStateStack = new ArrayDeque<>();
		mStateMap = new HashMap<>();
		mReductionAutomaton = new NestedWordAutomaton<L, S2>(services, mOperand.getVpAlphabet(), stateFactory);
		for (final S startState : mStartStateSet) {
			Set<L> emptySet = new HashSet<>();
			Pair<S, Set<L>> startStatePair = new Pair<>(startState, emptySet);
			S2 newStartState = stateFactory.createSleepSetState(startState, emptySet);
			mReductionAutomaton.addState(true, mOperand.isFinal(startState), newStartState);
			mStateStack.push(newStartState);
			mStateMap.put(newStartState, startStatePair);
			mDelaySetMap.put(startState, new HashSet<Set<L>>());
		}
		mOrder = sleepSetOrder;
		mIndependenceRelation = independenceRelation;
		mMode = mode;

		constructReductionAutomaton();
	}

	private void constructReductionAutomaton() {

		while (!mStateStack.isEmpty()) {
			
			final S2 currentSleepSetState = mStateStack.peek();
			final ArrayList<L> successorTransitionList = new ArrayList<>();
			S currentState = mStateMap.get(currentSleepSetState).getFirst();
			Set<L> currentSleepSet = mStateMap.get(currentSleepSetState).getSecond();
			final Set<Set<L>> currentDelaySet = mDelaySetMap.get(currentState);
			
			
			if ((!mMode && !mVisitedSet.contains(currentSleepSetState)) || 
					(mMode && mPrunedMap.get(currentState) == null)){
				// state not visited with this sleep set
				mVisitedSet.add(currentSleepSetState);
				mPrunedMap.put(currentState, currentSleepSet);
				for (final OutgoingInternalTransition<L, S> transition : mOperand.internalSuccessors(currentState)) {
					if (!currentSleepSet.contains(transition.getLetter())) {
						successorTransitionList.add(transition.getLetter());
					}
				}
			} else if (!currentDelaySet.isEmpty()){
				currentSleepSet = currentDelaySet.iterator().next();
				currentDelaySet.remove(currentSleepSet);
				final Set<L> pruned = mPrunedMap.get(currentState);
				successorTransitionList.addAll(DataStructureUtils.difference(pruned, currentSleepSet));
				currentSleepSet = DataStructureUtils.intersection(currentSleepSet, pruned);
				//mSleepSetMap.put(currentState, currentSleepSet);
				Pair<S, Set<L>> currentStatePair = new Pair<S, Set<L>>(currentState, currentSleepSet);
				mStateMap.put(currentSleepSetState, currentStatePair);
				mPrunedMap.put(currentState, currentSleepSet);
			} else if (mMode){
				final Set<L> pruned = mPrunedMap.get(currentState);
				successorTransitionList.addAll(DataStructureUtils.difference(pruned, currentSleepSet));
				currentSleepSet = DataStructureUtils.intersection(currentSleepSet, pruned);
				//mSleepSetMap.put(currentState, currentSleepSet);
				Pair<S, Set<L>> currentStatePair = new Pair<S, Set<L>>(currentState, currentSleepSet);
				mStateMap.put(currentSleepSetState, currentStatePair);
				mPrunedMap.put(currentState, currentSleepSet);
			}
			
			if (successorTransitionList.isEmpty()) {
				mStateStack.pop();
			}
			
			// sort successorTransitionList according to the given order
			final Comparator<L> order = mOrder.getOrder(currentState);
			successorTransitionList.sort(order);
			Set<L> explored = new HashSet<>();
			
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
				final Set<Set<L>> succDelaySet = new HashSet<>();
				
				S2 succSleepSetState = null;
				if (mMode) {
					succSleepSetState = mStateFactory.createSleepSetState(succState, new HashSet<L>());
				} else {
					succSleepSetState = mStateFactory.createSleepSetState(succState, succSleepSet);
				}
				mStateMap.put(succSleepSetState, new Pair<>(succState, succSleepSet));
				

				if (!mReductionAutomaton.contains(succSleepSetState)) {
					mReductionAutomaton.addState(false, mOperand.isFinal(succState), succSleepSetState);
				}
				mReductionAutomaton.addInternalTransition(currentSleepSetState, letterTransition, succSleepSetState);

				
				if (mMode && mStateStack.contains(succSleepSetState)) {
					succDelaySet.addAll(mDelaySetMap.get(succState));
					succDelaySet.add(succSleepSet);
					mDelaySetMap.put(succState, succDelaySet);
				} else {
					mStateMap.put(succSleepSetState, new Pair<>(succState, succSleepSet));
					//mSleepSetMap.put(succState, succSleepSet);
					mDelaySetMap.put(succState, succDelaySet);
					mStateStack.push(succSleepSetState);
				}
				explored.add(letterTransition);
			}
		}
		
	}

	@Override
	public NestedWordAutomaton<L, S2> getResult() {
		return mReductionAutomaton;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<L, S> getOperand() {
		return null;
	}
}
