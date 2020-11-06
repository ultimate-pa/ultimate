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
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Implementation of Partial Order Reduction for Deterministic Finite Automata using Sleep Sets for reduction and a
 * Delay Set for handling loops. This version constructs a reduced automaton.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            letter type
 * @param <S>
 *            state type
 */
public class SleepSetDelayReductionAutomatonIterative<L, S> extends UnaryNwaOperation<L, S, IStateFactory<S>> {

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final Set<S> mStartStateSet;
	private final HashMap<S, Set<L>> mHashMap;
	private final HashMap<S, Set<L>> mSleepSetMap;
	private final HashMap<S, Set<Set<L>>> mDelaySetMap;
	private final ArrayDeque<S> mStateStack;
	private final HashMap<S, ArrayDeque<S>> mStateStackMap;
	private final ISleepSetOrder<S, L> mOrder;
	private final IIndependenceRelation<S, L> mIndependenceRelation;
	private final NestedWordAutomaton<L, S> mReductionAutomaton;

	/**
	 * Constructor for POR with Sleep Sets and Delay Set
	 *
	 * @param operand
	 *            deterministic finite automaton
	 * @param independenceRelation
	 *            the underlying independence relation
	 * @param sleepSetOrder
	 *            order of transitions for further branchings
	 * @param services
	 *            ultimate services
	 * @param stateFactory
	 *            state factory
	 *
	 */
	public SleepSetDelayReductionAutomatonIterative(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IIndependenceRelation<S, L> independenceRelation, final ISleepSetOrder<S, L> sleepSetOrder,
			final AutomataLibraryServices services, final IEmptyStackStateFactory<S> stateFactory) {
		super(services);
		mOperand = operand;
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Sleep sets support only finite automata";

		mStartStateSet = CoreUtil.constructHashSet(operand.getInitialStates());
		assert (mStartStateSet.size() == 1) : "Only one initial state allowed";
		mHashMap = new HashMap<>();
		mSleepSetMap = new HashMap<>();
		mDelaySetMap = new HashMap<>();
		mStateStack = new ArrayDeque<>();
		mStateStackMap = new HashMap<>();
		mReductionAutomaton = new NestedWordAutomaton<>(services, mOperand.getVpAlphabet(), stateFactory);
		for (final S startState : mStartStateSet) {
			mSleepSetMap.put(startState, new HashSet<L>());
			mDelaySetMap.put(startState, new HashSet<Set<L>>());
			mStateStack.push(startState);
			mStateStackMap.put(startState, new ArrayDeque<S>());
			mReductionAutomaton.addState(true, mOperand.isFinal(startState), startState);

		}
		mOrder = sleepSetOrder;
		mIndependenceRelation = independenceRelation;

		constructReductionAutomaton();

	}

	private void constructReductionAutomaton() {
		
		while (!mStateStack.isEmpty()) {
			
			final S currentState = mStateStack.peek();
			final ArrayList<L> successorTransitionList = new ArrayList<>();
			Set<L> currentSleepSet = mSleepSetMap.get(currentState);
			final Set<Set<L>> currentDelaySet = mDelaySetMap.get(currentState);
			
			if (mHashMap.get(currentState) == null) {
				// state not visited yet
				mHashMap.put(currentState, mSleepSetMap.get(currentState));
				for (final OutgoingInternalTransition<L, S> transition : mOperand.internalSuccessors(currentState)) {
					if (!currentSleepSet.contains(transition.getLetter())) {
						successorTransitionList.add(transition.getLetter());
					}
				}
			} else if (!currentDelaySet.isEmpty()) {
				// state already visited but loops are not explored yet
				currentSleepSet = currentDelaySet.iterator().next();
				currentDelaySet.remove(currentSleepSet);
				mSleepSetMap.put(currentState, currentSleepSet);
				mDelaySetMap.put(currentState, currentDelaySet);
				mStateStack.push(currentState);
				final Set<L> currentHash = mHashMap.get(currentState);
				successorTransitionList.addAll(DataStructureUtils.difference(currentHash, currentSleepSet));
				currentSleepSet = DataStructureUtils.intersection(currentSleepSet, currentHash);
				mSleepSetMap.put(currentState, currentSleepSet);
				mHashMap.put(currentState, currentSleepSet);
			} else {
				// state already visited and loops are explored
				mStateStack.pop();
			}
			
			// sort successorTransitionList according to the given order
			final Comparator<L> order = mOrder.getOrder(currentState);
			successorTransitionList.sort(order);
			
			for (final L letterTransition : successorTransitionList) {
				final var successors = mOperand.internalSuccessors(currentState, letterTransition).iterator();
				if (!successors.hasNext()) {
					continue;
				}
				final var currentTransition = successors.next();
				assert !successors.hasNext() : "Automaton must be deterministic";

				final S succState = currentTransition.getSucc();
				final Set<L> succSleepSet = currentSleepSet.stream()
						.filter(l -> mIndependenceRelation.contains(currentState, letterTransition, l))
						.collect(Collectors.toCollection(HashSet::new));
				final Set<Set<L>> succDelaySet = new HashSet<>();

				// add succState to the automaton
				if (!mReductionAutomaton.contains(succState) && mOperand.isFinal(succState)) {
					mReductionAutomaton.addState(false, true, succState);
				} else if (!mReductionAutomaton.contains(succState)) {
					mReductionAutomaton.addState(false, false, succState);
				}
				// add transition from currentState to succState to the automaton
				mReductionAutomaton.addInternalTransition(currentState, letterTransition, succState);

				ArrayDeque<S> stateStack = new ArrayDeque<S>();
				stateStack.addAll(mStateStackMap.get(currentState));
				if (stateStack.contains(succState)) {
					if (mDelaySetMap.get(succState) != null) {
						succDelaySet.addAll(mDelaySetMap.get(succState));
					}
					succDelaySet.add(succSleepSet);
					mDelaySetMap.put(succState, succDelaySet);
				} else {
					mSleepSetMap.put(succState, succSleepSet);
					mDelaySetMap.put(succState, succDelaySet);
					mStateStack.push(succState);
					stateStack.push(succState);
					mStateStackMap.put(succState, stateStack);
				}
				currentSleepSet.add(letterTransition);
				mSleepSetMap.put(currentState, currentSleepSet);
			}	
		}	
	}

	@Override
	public NestedWordAutomaton<L, S> getResult() {
		// TODO Auto-generated method stub
		return mReductionAutomaton;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<L, S> getOperand() {
		// TODO Auto-generated method stub
		return null;
	}

}
