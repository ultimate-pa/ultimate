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

import java.util.function.Function;

/**
 * Implements an {@link IBddSignature} by applying a renaming function and then delegating to an underlying signature.
 *
 * This can be useful to implement tagged versions of variables (e.g. primed variables) or to embed variables of
 * different types in a common signature.
 *
 * In most cases, the renaming function should be injective to avoid unexpected behaviour (i.e. variable aliasing).
 *
 * @param <V>
 *            The type of variables in this signature
 * @param <W>
 *            The type of variables in the underlying signature
 */
public class RenamingBddSignature<V, W> implements IBddSignature<V> {
	private final IBddSignature<W> mUnderlying;
	private final Function<V, W> mRenamer;

	public RenamingBddSignature(final IBddSignature<W> underlying, final Function<V, W> renamer) {
		mUnderlying = underlying;
		mRenamer = renamer;
	}

	@Override
	public int getVariableIndex(final V variable) {
		return mUnderlying.getVariableIndex(mRenamer.apply(variable));
	}
}
