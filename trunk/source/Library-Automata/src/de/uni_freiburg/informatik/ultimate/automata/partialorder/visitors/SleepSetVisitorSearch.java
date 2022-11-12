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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;

/**
 * Visitor Class for the Sleep Set Reduction, which searches for an error state while reducing.
 *
 * @author Marcel Ebbinghaus
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @deprecated will be replaced by {@link AcceptingRunSearchVisitor}
 *
 * @param <L>
 *            letter
 * @param <S>
 *            state
 */
@Deprecated(since = "2021-04-08")
public class SleepSetVisitorSearch<L, S> implements IDfsVisitor<L, S> {
	private final Predicate<S> mIsGoalState;
	private final Predicate<S> mIsHopelessState;

	private final ArrayDeque<ArrayList<L>> mLetterStack = new ArrayDeque<>();
	private final ArrayDeque<ArrayList<S>> mStateStack = new ArrayDeque<>();

	private S mStartState;
	private boolean mFound;

	/**
	 * Constructor for the Sleep Set Reduction Visitor searching for an error trace.
	 *
	 * @param isGoalState
	 *            function to determine whether a state is a goal state
	 * @param isHopelessState
	 *            function to identify "hopeless" states, i.e., states from which a goal state can not be reached
	 */
	public SleepSetVisitorSearch(final Predicate<S> isGoalState, final Predicate<S> isHopelessState) {
		mIsGoalState = isGoalState;
		mIsHopelessState = isHopelessState;
	}

	@Override
	public boolean discoverState(final S state) {
		if (!state.equals(mStartState) && !mStateStack.peek().isEmpty()) {
			mLetterStack.push(new ArrayList<>());
			mStateStack.push(new ArrayList<>());
		}
		// prune successors of hopeless states
		return isHopelessState(state);
	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		assert !mFound : "Search must not continue after target state found";
		assert mStateStack.size() > 1 || source == mStartState : "Initial transition must begin in start state";
		assert mStateStack.size() < 2
				|| mStateStack.toArray(ArrayList[]::new)[1].contains(source) : "Transition source should be on stack";

		// push letter onto Stack
		mLetterStack.peek().add(letter);
		mStateStack.peek().add(target);
		mFound = mIsGoalState.test(target);

		// no pruning of transitions
		return false;
	}

	@Override
	public void backtrackState(final S state, final boolean isComplete) {
		// pop state's list and remove letter leading to state from predecessor's list
		if (mStateStack.peek().isEmpty()) {
			mLetterStack.pop();
			mStateStack.pop();
		}
		if (!mLetterStack.isEmpty()) {
			mLetterStack.peek().remove(0);
			mStateStack.peek().remove(0);
		}
	}

	@Override
	public void delayState(final S state) {
		// Delay is called immediately after discoverTransition.
		// Hence the delayed state will be the last (just added) in the topmost stack frame.
		assert state == mStateStack.peek().get(mStateStack.peek().size() - 1) : "Delaying the wrong state";
		mLetterStack.peek().remove(mLetterStack.peek().size() - 1);
		mStateStack.peek().remove(mStateStack.peek().size() - 1);
	}

	// TODO (Dominik 2021-02-10) Refactor so run constructed once; can be called multiple times to retrieve run
	public NestedRun<L, S> constructRun() {
		Word<L> acceptingWord = new Word<>();
		final ArrayList<S> acceptingStateSequence = new ArrayList<>();

		// problem: initial == final
		if (mIsGoalState.test(mStartState)) {
			acceptingStateSequence.add(mStartState);
			final NestedWord<L> acceptingNestedWord = NestedWord.nestedWord(acceptingWord);
			return new NestedRun<>(acceptingNestedWord, acceptingStateSequence);
		}
		if (mStateStack.isEmpty()) {
			return null;
		}

		final ArrayList<L> acceptingTransitionSequence = new ArrayList<>();

		// mFound is set in discoverTransition.
		// Hence the transition leading to the goal state will be the last in the topmost stack frame.
		ArrayList<L> currentTransitionList = mLetterStack.pop();
		L currentTransition = currentTransitionList.get(currentTransitionList.size() - 1);
		acceptingTransitionSequence.add(0, currentTransition);
		ArrayList<S> currentStateList = mStateStack.pop();
		S currentState = currentStateList.get(currentStateList.size() - 1);
		acceptingStateSequence.add(0, currentState);

		while (!mStateStack.isEmpty()) {
			// In other stack frames, the first transition in the stack frame is the one that is currently being
			// explored and leads to the goal state.
			currentTransitionList = mLetterStack.pop();
			currentTransition = currentTransitionList.get(0);
			acceptingTransitionSequence.add(0, currentTransition);
			currentStateList = mStateStack.pop();
			currentState = currentStateList.get(0);
			acceptingStateSequence.add(0, currentState);
		}
		acceptingStateSequence.add(0, mStartState);

		for (final L letter : acceptingTransitionSequence) {
			final Word<L> tempWord = new Word<>(letter);
			acceptingWord = acceptingWord.concatenate(tempWord);
		}
		final NestedWord<L> acceptingNestedWord = NestedWord.nestedWord(acceptingWord);
		return new NestedRun<>(acceptingNestedWord, acceptingStateSequence);
	}

	@Override
	public boolean addStartState(final S state) {
		mStartState = state;
		mLetterStack.push(new ArrayList<>());
		mStateStack.push(new ArrayList<>());
		mFound = mIsGoalState.test(state);
		return isHopelessState(state);
	}

	@Override
	public boolean isFinished() {
		return mFound;
	}

	private boolean isHopelessState(final S state) {
		if (mIsHopelessState != null) {
			return mIsHopelessState.test(state);
		}
		return false;
	}
}
