/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 Ecole Polytechnique
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

/**
 * A BDD signature defines how variables (that are meaningful at the level of client code) are mapped to the integer
 * indices representing these variables in BDDs.
 *
 * @param <V>
 *            The type of variables
 */
public interface IBddSignature<V> {
	/**
	 * Maps a variable to a non-negative integer index.
	 *
	 * Multiple invocations with equal objects (in the sense of {@link Object#equals(Object)}) must return the same
	 * index. For new objects (not previously passed to the method) the indices must increase (strictly) monotonically.
	 *
	 * @param variable
	 *            the variable
	 * @return the index used in BDD representation
	 */
	int getVariableIndex(V variable);

	/**
	 * Indicates whether the signature supports the method {@link #getVariableName(int)}.
	 */
	default boolean isReversible() {
		return false;
	}

	/**
	 * If supported (see {@link #isReversible()}), calling this method with an index previously returned from
	 * {@link #getVariableIndex(Object)} yields the variable object associated with the index.
	 *
	 * @throws IllegalArgumentException
	 *             if the index is not known (not previously returned from {@link #getVariableIndex(Object)})
	 * @throws UnsupportedOperationException
	 *             if the operation is generally unsupported (see {@link #isReversible()})
	 */
	default V getVariableName(final int variableIndex) throws IllegalArgumentException, UnsupportedOperationException {
		throw new UnsupportedOperationException("BDD signature is not reversible");
	}

	/**
	 * Registers variables in the supplied order. Call before constructing formulas if a deliberate ordering is desired.
	 */
	default void registerVariables(final Iterable<? extends V> variables) {
		for (final V variable : variables) {
			getVariableIndex(variable);
		}
	}
}
