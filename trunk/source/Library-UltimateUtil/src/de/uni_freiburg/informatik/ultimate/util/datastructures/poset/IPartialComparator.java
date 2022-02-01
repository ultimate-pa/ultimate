/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
 * Comparator for partially ordered sets.
 *
 * @author Matthias Heizmann
 *
 * @param <T>
 */
@FunctionalInterface
public interface IPartialComparator<T> {

	public enum ComparisonResult {
		STRICTLY_SMALLER, EQUAL, STRICTLY_GREATER, INCOMPARABLE;

		public ComparisonResult invert() {
			switch (this) {
			case STRICTLY_SMALLER:
				return STRICTLY_GREATER;
			case EQUAL:
				return EQUAL;
			case STRICTLY_GREATER:
				return STRICTLY_SMALLER;
			case INCOMPARABLE:
				return INCOMPARABLE;
			default:
				throw new AssertionError("unknown value");
			}
		}

		public static ComparisonResult fromNonPartialComparison(final int nonPartialComparisonResult) {
			if (nonPartialComparisonResult == 0) {
				return ComparisonResult.EQUAL;
			} else if (nonPartialComparisonResult > 0) {
				return ComparisonResult.STRICTLY_GREATER;
			} else {
				return ComparisonResult.STRICTLY_SMALLER;
			}
		}

		public static ComparisonResult aggregate(final ComparisonResult cr1, final ComparisonResult cr2) {
			switch (cr1) {
			case EQUAL:
				return cr2;
			case INCOMPARABLE:
				return INCOMPARABLE;
			case STRICTLY_GREATER:
				if (cr2 == INCOMPARABLE || cr2 == STRICTLY_SMALLER) {
					return INCOMPARABLE;
				}
				return cr2;
			case STRICTLY_SMALLER:
				if (cr2 == INCOMPARABLE || cr2 == STRICTLY_GREATER) {
					return INCOMPARABLE;
				}
				return cr2;
			default:
				throw new AssertionError("unknown value");
			}
		}
	}

	/**
	 * Returns e.g., STRICTLY_SMALLER if o1 is strictly smaller than o2.
	 */
	ComparisonResult compare(T o1, T o2);

}
