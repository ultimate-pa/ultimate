/*
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

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Implements the (finite) powerset lattice structure (ordered by subset inclusion).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <T>
 *            The type of elements in the set
 */
public class PowersetLattice<T> implements ILattice<Set<T>> {

	private final Set<T> mTop;

	/**
	 * Creates the subset lattice for the given finite set.
	 *
	 * @param fullSet
	 *            The set of all elements that may occur in compared sets.
	 */
	public PowersetLattice(final Set<T> fullSet) {
		assert fullSet != null : "full set must not be null";
		mTop = fullSet;
	}

	/**
	 * Creates the lattice of all sets over the given element type. This lattice has no top element.
	 */
	public PowersetLattice() {
		mTop = null;
	}

	@Override
	public ComparisonResult compare(final Set<T> o1, final Set<T> o2) {
		assert mTop == null || (mTop.containsAll(o1) && mTop.containsAll(o2)) : "set with unexpected elements";
		if (o1.equals(o2)) {
			return ComparisonResult.EQUAL;
		}
		if (o2.containsAll(o1)) {
			return ComparisonResult.STRICTLY_SMALLER;
		}
		if (o1.containsAll(o2)) {
			return ComparisonResult.STRICTLY_GREATER;
		}
		return ComparisonResult.INCOMPARABLE;
	}

	@Override
	public Set<T> getBottom() {
		return Collections.emptySet();
	}

	@Override
	public Set<T> getTop() {
		if (mTop == null) {
			throw new UnsupportedOperationException("set lattice has no top element unless domain is finite");
		}
		return mTop;
	}

	@Override
	public Set<T> supremum(final Set<T> h1, final Set<T> h2) {
		assert mTop == null || (mTop.containsAll(h1) && mTop.containsAll(h2)) : "set with unexpected elements";
		return DataStructureUtils.union(h1, h2);
	}

	@Override
	public Set<T> infimum(final Set<T> h1, final Set<T> h2) {
		assert mTop == null || (mTop.containsAll(h1) && mTop.containsAll(h2)) : "set with unexpected elements";
		return DataStructureUtils.intersection(h1, h2);
	}
}
