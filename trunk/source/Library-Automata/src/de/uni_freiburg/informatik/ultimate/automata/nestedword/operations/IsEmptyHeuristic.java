/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashedPriorityQueue;

/**
 * Check emptiness and obtain an accepting run of a nested word automaton using a modified version of A*.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class IsEmptyHeuristic<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final Predicate<STATE> mIsGoalState;
	private final Predicate<STATE> mIsForbiddenState;
	private final NestedRun<LETTER, STATE> mAcceptingRun;
	private final STATE mDummyEmptyStackState;

	/**
	 * Default constructor. Here we search a run from the initial states of the automaton to the final states of the
	 * automaton.
	 *
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            input NWA
	 * @see #IsEmpty(AutomataLibraryServices, INwaOutgoingLetterAndTransitionProvider)
	 */
	public IsEmptyHeuristic(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		this(services, operand, CoreUtil.constructHashSet(operand.getInitialStates()), a -> false, a -> operand.isFinal(a),
				IHeuristic.getZeroHeuristic());
	}

	/**
	 * Constructor that is not restricted to emptiness checks. The set of startStates defines where the run that we
	 * search has to start. The set of forbiddenStates defines states that the run must not visit. The set of goalStates
	 * defines where the run that we search has to end.
	 */
	public IsEmptyHeuristic(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand,
			final Set<STATE> startStates, final Predicate<STATE> funIsForbiddenState,
			final Predicate<STATE> funIsGoalState, final IHeuristic<STATE, LETTER> heuristic)
			throws AutomataOperationCanceledException {
		this(services, (INwaOutgoingLetterAndTransitionProvider<LETTER, STATE>) operand, startStates,
				funIsForbiddenState, funIsGoalState, heuristic);
		assert operand.getStates().containsAll(startStates) : "unknown states";
	}

	private IsEmptyHeuristic(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand, final Set<STATE> startStates,
			final Predicate<STATE> funIsForbiddenState, final Predicate<STATE> funIsGoalState,
			final IHeuristic<STATE, LETTER> heuristic) throws AutomataOperationCanceledException {
		super(services);
		mOperand = operand;
		mIsGoalState = funIsGoalState;
		mIsForbiddenState = funIsForbiddenState;
		assert startStates != null;
		assert mIsGoalState != null;
		assert mIsForbiddenState != null;
		assert mOperand != null;

		mDummyEmptyStackState = mOperand.getEmptyStackState();

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		mAcceptingRun = getAcceptingRun(startStates, heuristic);

		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	/**
	 * Get an accepting run of the automaton passed to the constructor. Return null if the automaton does not accept any
	 * nested word.
	 *
	 * @param heuristic
	 */
	private NestedRun<LETTER, STATE> getAcceptingRun(final Collection<STATE> startStates,
			final IHeuristic<STATE, LETTER> heuristic) throws AutomataOperationCanceledException {

		final HashedPriorityQueue<Item> worklist =
				new HashedPriorityQueue<>((a, b) -> Integer.compare(a.mExpectedCostToTarget, b.mExpectedCostToTarget));
		final Set<Item> closed = new HashSet<>();

		for (final STATE state : startStates) {
			worklist.add(new Item(state));
		}

		while (!worklist.isEmpty()) {
			if (!mServices.getProgressAwareTimer().continueProcessing()) {
				final String taskDescription = "searching accepting run (input had " + mOperand.size() + " states)";
				final RunningTaskInfo rti = new RunningTaskInfo(getClass(), taskDescription);
				throw new AutomataOperationCanceledException(rti);
			}
			mLogger.info("----");
			final Item current = worklist.poll();
			mLogger.info("Cur " + current);
			if (mIsGoalState.test(current.mTargetState)) {
				return current.constructRun();
			}

			final List<Item> unvaluatedSuccessors = getUnvaluatedSuccessors(current);

			for (final Item succ : unvaluatedSuccessors) {
				final int costSoFar = current.mCostSoFar + heuristic.getConcreteCost(succ.mTransition);
				if (worklist.contains(succ)) {
					final Item oldSucc = worklist.find(succ);
					if (costSoFar >= oldSucc.mCostSoFar) {
						// we already know the successor and our current way is not
						// better than the new one
						continue;
					}
				}

				final int expectedCost = costSoFar
						+ heuristic.getHeuristicValue(succ.mTargetState, succ.getHierPreState(), succ.mTransition);
				final boolean rem = worklist.remove(succ);
				if (!rem && !closed.add(succ)) {
					// if
					mLogger.info("REM " + rem);
					continue;
				}
				succ.setExpectedCostToTarget(expectedCost);
				if (!succ.isLowest()) {
					continue;
				}
				succ.setCostSoFar(costSoFar);
				worklist.add(succ);
				mLogger.info("Add " + succ);
			}
		}
		return null;
	}

	private List<Item> getUnvaluatedSuccessors(final Item current) {
		final List<Item> rtr = new ArrayList<>();

		// process internal transitions
		for (final OutgoingInternalTransition<LETTER, STATE> transition : mOperand
				.internalSuccessors(current.mTargetState)) {
			final LETTER symbol = transition.getLetter();
			final STATE succ = transition.getSucc();
			if (mIsForbiddenState.test(succ)) {
				continue;
			}
			rtr.add(new Item(succ, current.getHierPreState(), symbol, current, ItemType.INTERNAL));
		}

		// process call transitions
		for (final OutgoingCallTransition<LETTER, STATE> transition : mOperand.callSuccessors(current.mTargetState)) {
			final LETTER symbol = transition.getLetter();
			final STATE succ = transition.getSucc();
			if (mIsForbiddenState.test(succ)) {
				continue;
			}
			rtr.add(new Item(succ, current.mTargetState, symbol, current, ItemType.CALL));
		}

		if (current.getHierPreState() == null) {
			// there is no return transition
			return rtr;
		}

		// process return transitions
		for (final OutgoingReturnTransition<LETTER, STATE> transition : mOperand
				.returnSuccessorsGivenHier(current.mTargetState, current.getHierPreState())) {
			final LETTER symbol = transition.getLetter();
			final STATE succ = transition.getSucc();
			if (mIsForbiddenState.test(succ)) {
				continue;
			}

			final STATE stateKk = current.findHierPredecessor();
			if (stateKk == null) {
				continue;
			}
			rtr.add(new Item(succ, stateKk, symbol, current, ItemType.RETURN));
		}

		return rtr;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Boolean getResult() {
		return mAcceptingRun == null;
	}

	public NestedRun<LETTER, STATE> getNestedRun() {
		return mAcceptingRun;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		boolean correct = true;
		if (mAcceptingRun == null) {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("Emptiness not double checked ");
			}
		} else {
			if (mLogger.isWarnEnabled()) {
				mLogger.warn("Correctness of emptinessCheck not tested.");
			}
			correct = (new Accepts<>(mServices, mOperand, mAcceptingRun.getWord())).getResult();
			if (mLogger.isInfoEnabled()) {
				mLogger.info("Finished testing correctness of emptinessCheck");
			}
		}
		return correct;
	}

	@Override
	public String exitMessage() {
		if (mAcceptingRun == null) {
			return "Finished " + getOperationName() + ". No accepting run.";
		}
		return "Finished " + getOperationName() + ". Found accepting run of length " + mAcceptingRun.getLength();
	}

	private enum ItemType {
		CALL, RETURN, INTERNAL, INITIAL
	}

	/**
	 * Internal datastructure that represents worklist item.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private class Item implements Comparable<Item> {

		private final STATE mTargetState;
		private final Deque<STATE> mHierPreStates;
		private final LETTER mTransition;
		private final Item mBackPointer;
		private final ItemType mItemType;

		// g-value, how much have we already payed?
		private int mCostSoFar;
		// h-value
		private int mLowestExpectedCost;
		// f-value, i.e. how expensive from start to target if we use this node, i.e. g+h
		private int mExpectedCostToTarget;

		/**
		 * Create initial worklist item.
		 *
		 * @param initialState
		 */
		Item(final STATE initialState) {
			this(initialState, mDummyEmptyStackState, null, null, ItemType.INITIAL);
		}

		/**
		 * Create new worklist item.
		 *
		 * @param targetState
		 * @param hierPreState
		 * @param letter
		 * @param predecessor
		 * @param symbolType
		 */
		Item(final STATE targetState, final STATE hierPreState, final LETTER letter, final Item predecessor,
				final ItemType symbolType) {
			mTargetState = targetState;
			if (symbolType == ItemType.INTERNAL) {
				mHierPreStates = predecessor.mHierPreStates;
			} else if (symbolType == ItemType.RETURN) {
				mHierPreStates = new ArrayDeque<>(predecessor.mHierPreStates);
				mHierPreStates.pop();
			} else if (symbolType == ItemType.CALL) {
				mHierPreStates = new ArrayDeque<>(predecessor.mHierPreStates);
				mHierPreStates.push(hierPreState);
			} else {
				mHierPreStates = new ArrayDeque<>();
				mHierPreStates.push(hierPreState);
			}

			mTransition = letter;
			mBackPointer = predecessor;
			mItemType = symbolType;
			setExpectedCostToTarget(Integer.MAX_VALUE);
			mLowestExpectedCost = Integer.MAX_VALUE;
		}

		void setExpectedCostToTarget(final int value) {
			mExpectedCostToTarget = value;
			if (value < mLowestExpectedCost) {
				mLowestExpectedCost = value;
			}
		}

		void setCostSoFar(final int costSoFar) {
			mCostSoFar = costSoFar;
		}

		boolean isLowest() {
			return mLowestExpectedCost == mExpectedCostToTarget;
		}

		@Override
		public int compareTo(final Item o) {
			return Integer.compare(mExpectedCostToTarget, o.mExpectedCostToTarget);
		}

		public STATE getHierPreState() {
			return mHierPreStates.peek();
		}

		public STATE findHierPredecessor() {
			if (mHierPreStates.size() < 2) {
				return null;
			}
			final Iterator<STATE> iter = mHierPreStates.iterator();
			iter.next();
			return iter.next();
		}

		public NestedRun<LETTER, STATE> constructRun() {
			final List<Item> runInItems = new ArrayList<>();
			Item current = this;
			while (true) {
				runInItems.add(current);
				current = current.mBackPointer;
				if (current == null) {
					break;
				}
			}
			Collections.reverse(runInItems);

			// construct nesting relation
			final ArrayList<STATE> stateSequence = new ArrayList<>();
			@SuppressWarnings("unchecked")
			final LETTER[] word = (LETTER[]) new Object[runInItems.size() - 1];

			final Deque<Integer> callIndices = new ArrayDeque<>();
			final int[] nestingRelation = new int[word.length];
			int i = 0;
			for (final Item item : runInItems) {
				if (item.mTransition == null) {
					stateSequence.add(item.mTargetState);
					continue;
				}
				word[i] = item.mTransition;
				stateSequence.add(item.mTargetState);
				switch (item.mItemType) {
				case CALL:
					callIndices.push(i);
					nestingRelation[i] = NestedWord.PLUS_INFINITY;
					break;
				case INTERNAL:
					nestingRelation[i] = NestedWord.INTERNAL_POSITION;
					break;
				case RETURN:
					final int lastCall = callIndices.pop();
					nestingRelation[i] = lastCall;
					nestingRelation[lastCall] = i;
					break;
				case INITIAL:
				default:
					throw new UnsupportedOperationException();
				}
				++i;
			}

			final NestedWord<LETTER> nestedWord = new NestedWord<>(word, nestingRelation);

			return new NestedRun<>(nestedWord, stateSequence);
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((mTargetState == null) ? 0 : mTargetState.hashCode());
			result = prime * result + ((mHierPreStates == null) ? 0 : mHierPreStates.hashCode());
			result = prime * result + ((mTransition == null) ? 0 : mTransition.hashCode());
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			@SuppressWarnings("unchecked")
			final Item other = (Item) obj;
			if (mTargetState == null) {
				if (other.mTargetState != null) {
					return false;
				}
			} else if (!mTargetState.equals(other.mTargetState)) {
				return false;
			}
			if (mHierPreStates == null) {
				if (other.mHierPreStates != null) {
					return false;
				}
			} else if (!mHierPreStates.equals(other.mHierPreStates)) {
				return false;
			}
			if (mTransition == null) {
				if (other.mTransition != null) {
					return false;
				}
			} else if (!mTransition.equals(other.mTransition)) {
				return false;
			}
			return true;
		}

		@Override
		public String toString() {
			return String.format("{?} {%s} %s (%s) {%s} (g=%d, h=%d, f=%d, s=%d)", mHierPreStates.peek().hashCode(),
					mTransition == null ? 0 : mTransition.hashCode(), mItemType, mTargetState.hashCode(), mCostSoFar,
					mLowestExpectedCost, mExpectedCostToTarget, mHierPreStates.size());
		}
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 * @param <STATE>
	 *            Type of states
	 * @param <LETTER>
	 *            Type of transitions
	 */
	public interface IHeuristic<STATE, LETTER> {

		int getHeuristicValue(STATE state, STATE stateK, LETTER trans);

		int getConcreteCost(LETTER trans);

		public static <STATE, LETTER> IHeuristic<STATE, LETTER> getZeroHeuristic() {
			return new IHeuristic<STATE, LETTER>() {
				@Override
				public final int getHeuristicValue(final STATE state, final STATE stateK, final LETTER trans) {
					return 0;
				}

				@Override
				public final int getConcreteCost(final LETTER e) {
					return 1;
				}
			};
		}
	}
}
