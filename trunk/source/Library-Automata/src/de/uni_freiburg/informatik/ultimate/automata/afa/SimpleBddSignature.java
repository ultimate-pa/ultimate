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

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;

/**
 * A straightforward implementation of a (reversible) {@link IBddSignature}.
 *
 * @param <V>
 *            the type of variables
 */
public class SimpleBddSignature<V> implements IBddSignature<V> {
	private final BidirectionalMap<V, Integer> mVariableIndices = new BidirectionalMap<>();
	private final BddManager mManager;

	public SimpleBddSignature(final BddManager manager) {
		mManager = manager;
	}

	@Override
	public int getVariableIndex(final V variable) {
		Objects.requireNonNull(variable, "Variable must not be null");
		return mVariableIndices.computeIfAbsent(variable, v -> mManager.getFreshVariable());
	}

	@Override
	public boolean isReversible() {
		return true;
	}

	@Override
	public V getVariableName(final int variableIndex) throws IllegalArgumentException, UnsupportedOperationException {
		if (mVariableIndices.containsValue(variableIndex)) {
			return mVariableIndices.inverse().get(variableIndex);
		}
		throw new IllegalArgumentException("Unknown variable index: " + variableIndex);
	}
}
