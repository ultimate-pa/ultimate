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
 * A simple base class for visitors that delegate to an underlying instance and overwrite only some methods.
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
public abstract class WrapperVisitor<L, S, V extends IDfsVisitor<L, S>> implements IDfsVisitor<L, S> {
	protected final V mUnderlying;

	/**
	 * Create a new instance
	 *
	 * @param underlying
	 *            The underlying visitor to which calls are delegated.
	 */
	public WrapperVisitor(final V underlying) {
		mUnderlying = underlying;
	}

	public V getUnderlying() {
		return mUnderlying;
	}

	public IDfsVisitor<L, S> getBaseVisitor() {
		if (mUnderlying instanceof WrapperVisitor<?, ?, ?>) {
			return ((WrapperVisitor<L, S, IDfsVisitor<L, S>>) mUnderlying).getBaseVisitor();
		}
		return mUnderlying;
	}

	@Override
	public boolean addStartState(final S state) {
		return mUnderlying.addStartState(state);
	}

	@Override
	public boolean discoverTransition(final S source, final L letter, final S target) {
		return mUnderlying.discoverTransition(source, letter, target);
	}

	@Override
	public boolean discoverState(final S state) {
		return mUnderlying.discoverState(state);
	}

	@Override
	public void backtrackState(final S state, final boolean isComplete) {
		mUnderlying.backtrackState(state, isComplete);
	}

	@Override
	public boolean isFinished() {
		return mUnderlying.isFinished();
	}

}
