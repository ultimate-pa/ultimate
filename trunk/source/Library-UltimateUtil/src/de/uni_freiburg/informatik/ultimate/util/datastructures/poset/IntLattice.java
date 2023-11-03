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

/**
 * Implements the canonical lattice for integers.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class IntLattice implements ILattice<Integer> {
	@Override
	public ComparisonResult compare(final Integer o1, final Integer o2) {
		if (o1 < o2) {
			return ComparisonResult.STRICTLY_SMALLER;
		}
		if (o1 > o2) {
			return ComparisonResult.STRICTLY_GREATER;
		}
		return ComparisonResult.EQUAL;
	}

	@Override
	public Integer getBottom() {
		return Integer.MIN_VALUE;
	}

	@Override
	public Integer getTop() {
		return Integer.MAX_VALUE;
	}

	@Override
	public Integer supremum(final Integer h1, final Integer h2) {
		return Integer.max(h1, h2);
	}

	@Override
	public Integer infimum(final Integer h1, final Integer h2) {
		return Integer.min(h1, h2);
	}
}