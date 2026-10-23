/*
 * Copyright (C) 2026 Marcel Ebbinghaus
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.afa;

import java.util.Objects;

/**
 * A Boolean formula represented by a reduced ordered binary decision diagram.
 *
 * @param <V>
 *            The type used to identify Boolean variables, e.g. AfaState.
 */
public final class Bdd<V> {

	final BddManager<V> mManager;
	final BddManager.Node mRoot;

	Bdd(final BddManager<V> manager, final BddManager.Node root) {
		mManager = Objects.requireNonNull(manager);
		mRoot = Objects.requireNonNull(root);
	}

	public Bdd<V> and(final Bdd<V> other) {
		return mManager.and(this, other);
	}

	public Bdd<V> or(final Bdd<V> other) {
		return mManager.or(this, other);
	}

	public Bdd<V> not() {
		return mManager.not(this);
	}

	public boolean isTrue() {
		return mRoot == mManager.mTrueNode;
	}

	public boolean isFalse() {
		return mRoot == mManager.mFalseNode;
	}

	public boolean isTerminal() {
		return isTrue() || isFalse();
	}

	/**
	 * Returns the variable at this node.
	 *
	 * @throws IllegalStateException
	 *             if this BDD is a terminal.
	 */
	public V getVariable() {
		if (isTerminal()) {
			throw new IllegalStateException("A terminal has no variable");
		}
		return mManager.getVariableForIndex(mRoot.mVariable);
	}

	/**
	 * Returns the left child, corresponding to variable = false.
	 *
	 * @throws IllegalStateException
	 *             if this BDD is a terminal.
	 */
	public Bdd<V> getLeft() {
		ensureNonTerminal();
		return new Bdd<>(mManager, mRoot.mLeft);
	}

	/**
	 * Returns the right child, corresponding to variable = true.
	 *
	 * @throws IllegalStateException
	 *             if this BDD is a terminal.
	 */
	public Bdd<V> getRight() {
		ensureNonTerminal();
		return new Bdd<>(mManager, mRoot.mRight);
	}

	private void ensureNonTerminal() {
		if (isTerminal()) {
			throw new IllegalStateException("A terminal has no children");
		}
	}

	/**
	 * Checks whether two BDDs represent the same canonical function. Both must belong to the same manager.
	 */
	public boolean equivalentTo(final Bdd<V> other) {
		checkSameManager(other);
		return mRoot == other.mRoot;
	}

	private void checkSameManager(final Bdd<V> other) {
		Objects.requireNonNull(other);
		if (mManager != other.mManager) {
			throw new IllegalArgumentException("Cannot combine BDDs from different managers");
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof final Bdd<?> other)) {
			return false;
		}
		return mManager == other.mManager && mRoot == other.mRoot;
	}

	@Override
	public int hashCode() {
		return 31 * System.identityHashCode(mManager) + System.identityHashCode(mRoot);
	}

	@Override
	public String toString() {
		return mManager.toString(this);
	}
}