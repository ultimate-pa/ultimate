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
import java.util.Deque;
import java.util.Set;

/**
 * A visitor that checks reachability of a given set of states, and aborts the search as soon as such a state is
 * reached. At this point, it also adds all states on the stack to the given set of states.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of states
 * @param <V>
 *            The type of the underlying visitor
 */
// This duplicates in part code / functionality of AcceptingRunSearchVisitor and DeadEndOptimizingVisitor.
// TODO See if we can avoid such duplication.
public class ReachabilityCheckVisitor<L, S, V extends IDfsVisitor<L, S>> extends WrapperVisitor<L, S, V> {

	private final Set<S> mCanReach;
	private final Set<S> mCanNotReach;
	private boolean mFound;

	// The current stack of states
	private final Deque<S> mStateStack = new ArrayDeque<>();

	// A possible successor of the last state on the stack, which may become the next element on the stack.
	private S mPendingState;

	/**
	 * Create a new instance of the visitor.
	 *
	 * @param underlying
	 *            An underlying visitor to which calls are proxied
	 * @param canReach
	 *            A set of states for which reachability is checked
	 * @param canNotReach
	 *            A set of states for which it is known that they can not reach a state in the previous set. The visitor
	 *            prunes the exploration of such states.
	 */
	public ReachabilityCheckVisitor(final V underlying, final Set<S> canReach, final Set<S> canNotReach) {
		super(underlying);
		mCanReach = canReach;
		mCanNotReach = canNotReach;
	}

	@Override
	public boolean addStartState(final S state) {
		assert mStateStack.isEmpty() : "start state must be first";
		mStateStack.addLast(state);
		checkState(state);
		return mCanNotReach.contains(state) || mUnderlying.addStartState(state);
	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		assert !mFound : "Unexpected transition discovery after abort";
		assert mStateStack.getLast() == source : "Unexpected transition from state " + source;
		mPendingState = target;
		return mCanNotReach.contains(target) || mUnderlying.discoverTransition(source, letter, target);
	}

	@Override
	public boolean discoverState(final S state) {
		assert !mFound : "Unexpected state discovery after abort";
		assert !mCanNotReach.contains(state) : "should have pruned transition to this state";

		if (mPendingState == null) {
			// Must be initial state
			assert mStateStack.size() == 1 && mStateStack.getLast() == state : "Unexpected discovery of state " + state;
		} else {
			// Pending transition must lead to given state
			assert mPendingState == state : "Unexpected discovery of state " + state;
			mStateStack.addLast(mPendingState);
			mPendingState = null;
		}

		checkState(state);
		return mUnderlying.discoverState(state);
	}

	@Override
	public void backtrackState(final S state, final boolean isComplete) {
		assert !mFound : "Unexpected backtrack after abort";
		assert mStateStack.getLast() == state : "Unexpected backtrack of state " + state;

		mPendingState = null;
		mStateStack.removeLast();

		if (isComplete) {
			mCanNotReach.add(state);
		}

		mUnderlying.backtrackState(state, isComplete);
	}

	@Override
	public boolean isFinished() {
		return mFound || mUnderlying.isFinished();
	}

	/**
	 * @return true if a state in the given set was found (and the visitor aborted the search), false otherwise
	 */
	public boolean reachabilityConfirmed() {
		return mFound;
	}

	private void checkState(final S state) {
		assert !mFound : "Unexpected call after abort";
		assert mStateStack.getLast() == state : "Checked state is expected to be on top of stack";

		mFound = mCanReach.contains(state);
		if (mFound) {
			mCanReach.addAll(mStateStack);
		}
	}
}
