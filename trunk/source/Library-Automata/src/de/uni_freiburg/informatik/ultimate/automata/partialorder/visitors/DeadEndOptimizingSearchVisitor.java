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

/**
 * A visitor that implements a dead-end removal optimization.
 *
 * The visitor collects backtracked states in a given {@link IDeadEndStore}. When it encounters a state marked as dead
 * end, the successors of this state are not explored.
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
public class DeadEndOptimizingSearchVisitor<L, S, V extends IDfsVisitor<L, S>> extends WrapperVisitor<L, S, V> {
	private final IDeadEndStore<?, S> mDeadEndStore;
	private final boolean mIsReadOnly;

	/**
	 * Wraps a given visitor with dead-end detection and pruning.
	 *
	 * @param underlying
	 *            The underlying visitor
	 * @param store
	 *            A dead end store which is used to store and query dead end information
	 * @param isReadOnly
	 *            Whether the dead end store should be treated as read-only (backtracked states should not be added)
	 */
	public DeadEndOptimizingSearchVisitor(final V underlying, final IDeadEndStore<?, S> store,
			final boolean isReadOnly) {
		super(underlying);
		mDeadEndStore = store;
		mIsReadOnly = isReadOnly;
	}

	@Override
	public boolean addStartState(final S state) {
		final boolean result = mUnderlying.addStartState(state);
		return result || mDeadEndStore.isDeadEndState(state);
	}

	@Override
	public boolean discoverState(final S state) {
		final boolean result = mUnderlying.discoverState(state);
		return result || mDeadEndStore.isDeadEndState(state);
	}

	@Override
	public void backtrackState(final S state, final boolean isComplete) {
		mUnderlying.backtrackState(state, isComplete);
		if (!mIsReadOnly && isComplete) {
			mDeadEndStore.addDeadEndState(state);
		}
	}
}
