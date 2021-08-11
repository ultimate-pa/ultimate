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
import java.util.function.Supplier;

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
 * @param <S>
 *            The type of states in the traversed automaton
 * @param <V>
 *            The type of the underlying visitor
 */
public class DeadEndOptimizingSearchVisitor<L, S, V extends IDfsVisitor<L, S>> implements IDfsVisitor<L, S> {
	private V mUnderlying;
	private final Supplier<V> mCreateUnderlying;
	private final Set<S> mDeadEndSet = new HashSet<>();

	/**
	 * Creates a new instance, which can be used in multiple traversals. In each traversal, a new underlying visitor is
	 * created; and calls are proxied to this underlying instance.
	 *
	 * @param createUnderlying
	 *            A function that constructs a new underlying instance
	 */
	public DeadEndOptimizingSearchVisitor(final Supplier<V> createUnderlying) {
		mCreateUnderlying = createUnderlying;
	}

	@Override
	public boolean addStartState(final S state) {
		final boolean result = getUnderlying().addStartState(state);
		return result || isDeadEndState(state);
	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		return getUnderlying().discoverTransition(source, letter, target);
	}

	@Override
	public boolean discoverState(final S state) {
		final boolean result = getUnderlying().discoverState(state);
		return result || isDeadEndState(state);
	}

	@Override
	public void backtrackState(final S state, final boolean isComplete) {
		getUnderlying().backtrackState(state, isComplete);
		if (isComplete) {
			addDeadEndState(state);
		}
	}

	@Override
	public void delayState(final S state) {
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
	 * explicitly as dead end (see {@link #addDeadEndState(S)}).
	 *
	 * @param state
	 *            the state which might be a dead end
	 * @return true if the state has already been marked as dead end, false otherwise
	 */
	public boolean isDeadEndState(final S state) {
		return mDeadEndSet.contains(state);
	}

	/**
	 * Explicitly marks a given state as dead end. In future traversals, outgoing transitions of this state will not be
	 * explored.
	 *
	 * @param state
	 *            the new dead end state
	 */
	public void addDeadEndState(final S state) {
		mDeadEndSet.add(state);
	}
}
