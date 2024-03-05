/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
import java.util.Deque;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;

/**
 * A visitor implementation that searches for an accepting run.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the traversed automaton
 * @param <S>
 *            The type of states in the traversed automaton
 */
public class AcceptingRunSearchVisitor<L, S> implements IDfsVisitor<L, S> {

	private final Predicate<S> mIsGoalState;

	// The current stack, as n+1 states and n letters
	private final Deque<S> mStateStack = new ArrayDeque<>();
	private final Deque<L> mLetterStack = new ArrayDeque<>();

	// An outgoing transition from the last state on the stack, that may become the next element on the stack.
	private L mPendingLetter;
	private S mPendingState;

	private boolean mFound;
	private NestedRun<L, S> mRun;

	/**
	 * Create a fresh visitor instance. Each instance can only be used for one traversal.
	 *
	 * @param isGoalState
	 *            A predicate identifying a goal state. We consider a run accepting if it reaches such a state.
	 */
	public AcceptingRunSearchVisitor(final Predicate<S> isGoalState) {
		mIsGoalState = isGoalState;
	}

	@Override
	public boolean addStartState(final S state) {
		assert mStateStack.isEmpty() : "start state must be first";
		mStateStack.addLast(state);
		mFound = mIsGoalState.test(state);
		return false;
	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		assert !mFound : "Unexpected transition discovery after abort";
		assert mStateStack.getLast() == source : "Unexpected transition from state " + source;
		mPendingLetter = letter;
		mPendingState = target;
		return false;
	}

	@Override
	public boolean discoverState(final S state) {
		assert !mFound : "Unexpected state discovery after abort";

		if (mPendingLetter == null) {
			// Must be initial state
			assert mStateStack.size() == 1 && mStateStack.getLast() == state : "Unexpected discovery of state " + state;
		} else {
			// Pending transition must lead to given state
			assert mPendingState == state : "Unexpected discovery of state " + state;
			mLetterStack.addLast(mPendingLetter);
			mStateStack.addLast(mPendingState);
			mPendingLetter = null;
			mPendingState = null;
		}

		mFound = mIsGoalState.test(state);
		return false;
	}

	@Override
	public void backtrackState(final S state, final boolean isComplete) {
		assert !mFound : "Unexpected backtrack after abort";
		assert mStateStack.getLast() == state : "Unexpected backtrack of state " + state;

		mPendingLetter = null;
		mPendingState = null;

		mStateStack.removeLast();
		mLetterStack.pollLast();
	}

	@Override
	public boolean isFinished() {
		return mFound;
	}

	/**
	 * Retrieves an accepting run, if one was found.
	 *
	 * @return A run from an initial to a goal state, if found. <code>null</code> otherwise.
	 */
	public NestedRun<L, S> getAcceptingRun() {
		if (mRun != null) {
			return mRun;
		}
		if (!mFound) {
			return null;
		}

		final ArrayList<S> stateSequence = new ArrayList<>(mStateStack);
		final Word<L> acceptedWord = new Word<>((L[]) mLetterStack.toArray());
		mRun = new NestedRun<>(NestedWord.nestedWord(acceptedWord), stateSequence);
		return mRun;
	}
}
