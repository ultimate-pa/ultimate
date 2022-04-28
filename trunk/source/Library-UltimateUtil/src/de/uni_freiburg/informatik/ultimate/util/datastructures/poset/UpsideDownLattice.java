/*
 * Copyright (C) 2022 Marcel Rogg
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.util.datastructures.poset;

/**
 * Reverses a given lattice.
 *
 * @author Marcel Rogg
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <T>
 *            The type of elements in the lattice
 */
public class UpsideDownLattice<T> implements ILattice<T> {
	private final ILattice<T> mLattice;

	public UpsideDownLattice(final ILattice<T> lattice) {
		mLattice = lattice;
	}

	@Override
	public T getBottom() {
		return mLattice.getTop();
	}

	@Override
	public T getTop() {
		return mLattice.getBottom();
	}

	@Override
	public ComparisonResult compare(final T o1, final T o2) {
		return mLattice.compare(o2, o1);
	}

	@Override
	public T supremum(final T h1, final T h2) {
		return mLattice.infimum(h1, h2);
	}

	@Override
	public T infimum(final T h1, final T h2) {
		return mLattice.supremum(h1, h2);
	}
}
