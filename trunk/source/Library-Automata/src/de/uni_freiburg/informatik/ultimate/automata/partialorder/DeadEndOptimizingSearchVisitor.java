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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * A visitor that implements a dead-end removal optimization. Each instance can be used in multiple traversals, if it is
 * reset in between traversals. From each traversal, it remembers backtracked states and marks them as dead ends. In
 * future traversals, the successors of such dead ends are not explored. Additionally, states can be explicitly marked
 * as dead ends.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the traversed automaton
 * @param <R>
 *            The type of states in the traversed automaton
 * @param <S>
 *            States of type R can (optionally) be split into a state of type S and extra information (type Object).
 *            This is useful if automata transformation (like e.g. sleep set reduction, or combination with a stateful
 *            order) are used, but dead end information is to be transferred based on the underlying state of type S.
 * @param <V>
 *            The type of the underlying visitor
 */
public class DeadEndOptimizingSearchVisitor<L, R, S, V extends IDfsVisitor<L, R>> implements IDfsVisitor<L, R> {
	private V mUnderlying;
	private final Supplier<V> mCreateUnderlying;
	private final Function<R, S> mState2Original;
	private final Function<R, Object> mState2ExtraInfo;

	private final Set<R> mDeadEndSet;
	private final HashRelation<S, Object> mDeadEndRelation;

	private int mPruneCounter;

	/**
	 * Creates a new instance, which can be used in multiple traversals. In each traversal, a new underlying visitor is
	 * created; and calls are proxied to this underlying instance.
	 *
	 * @param createUnderlying
	 *            A function that constructs a new underlying instance
	 */
	public DeadEndOptimizingSearchVisitor(final Supplier<V> createUnderlying) {
		this(createUnderlying, null, null);
	}

	public DeadEndOptimizingSearchVisitor(final Supplier<V> createUnderlying, final Function<R, S> state2Original,
			final Function<R, Object> state2ExtraInfo) {
		mCreateUnderlying = createUnderlying;
		mState2Original = state2Original;
		mState2ExtraInfo = state2ExtraInfo;

		if (mState2Original == null) {
			assert mState2ExtraInfo == null : "support for extra info (sleep sets etc.) requires both functions";
			mDeadEndSet = new HashSet<>();
			mDeadEndRelation = null;
		} else {
			assert mState2ExtraInfo != null : "support for extra info (sleep sets etc.) requires both functions";
			mDeadEndSet = null;
			mDeadEndRelation = new HashRelation<>();
		}
	}

	@Override
	public boolean addStartState(final R state) {
		final boolean result = getUnderlying().addStartState(state);
		return result || isDeadEndState(state);
	}

	@Override
	public boolean discoverTransition(final R source, final L letter, final R target) {
		return getUnderlying().discoverTransition(source, letter, target);
	}

	@Override
	public boolean discoverState(final R state) {
		final boolean result = getUnderlying().discoverState(state);
		return result || isDeadEndState(state);
	}

	@Override
	public void backtrackState(final R state, final boolean isComplete) {
		getUnderlying().backtrackState(state, isComplete);
		if (isComplete) {
			addDeadEndState(state);
		}
	}

	@Override
	public void delayState(final R state) {
		getUnderlying().delayState(state);
	}

	@Override
	public boolean isFinished() {
		return getUnderlying().isFinished();
	}

	/**
	 * Retrieves the underlying visitor instance.
	 */
	public V getUnderlying() {
		if (mUnderlying == null) {
			mUnderlying = mCreateUnderlying.get();
		}
		return mUnderlying;
	}

	/**
	 * Resets the instance, replacing the underlying visitor with a new instance. Call this before using this visitor
	 * for traversals.
	 */
	public void reset() {
		mUnderlying = null;
	}

	/**
	 * Determines if a state has been marked as dead end, either because it was backtracked or because it was marked
	 * explicitly as dead end (see {@link #addDeadEndState(R)}).
	 *
	 * @param state
	 *            the state which might be a dead end
	 * @return true if the state has already been marked as dead end, false otherwise
	 */
	public boolean isDeadEndState(final R state) {
		final boolean result;
		if (mDeadEndSet == null) {
			result = mDeadEndRelation.containsPair(mState2Original.apply(state), mState2ExtraInfo.apply(state));
		} else {
			result = mDeadEndSet.contains(state);
		}
		if (result) {
			mPruneCounter++;
		}
		return result;
	}

	private void addDeadEndState(final R state) {
		if (mDeadEndSet == null) {
			mDeadEndRelation.addPair(mState2Original.apply(state), mState2ExtraInfo.apply(state));
		} else {
			mDeadEndSet.add(state);
		}
	}

	/**
	 * Copies dead end information from a given state to another.
	 *
	 * If extra information is not used, this simply means that if the first state is known to be a dead end, we also
	 * mark the new state as dead end.
	 *
	 * If extra information is used, this means that for any combination of the first state with extra information X
	 * that is known to be a dead end, we also mark the combination of the new state and the same extra information X as
	 * dead end.
	 *
	 * @param originalState
	 *            The state whose dead end information should be copied.
	 * @param newState
	 *            The state for which dead end information is added
	 */
	public void copyDeadEndInformation(final S originalState, final S newState) {
		if (mDeadEndSet == null) {
			mDeadEndRelation.addAllPairs(newState, mDeadEndRelation.getImage(originalState));
		} else if (mDeadEndSet.contains(originalState)) {
			mDeadEndSet.add((R) newState);
		}
	}
}
