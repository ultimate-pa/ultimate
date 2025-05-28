/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import de.uni_freiburg.informatik.ultimate.util.LazyInt;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Represents a <em>region</em>, which is a set of places of a Petri net.
 *
 * A region typically (though it is not strictly necessary) represents a block of places connected by transitions.
 * Intuitively, we think of a region as a (connected) segment of the control flow of a single thread.
 *
 * Therefore, regions should satisfy the invariant that any two places in the region cannot occur together in a
 * reachable marking of the Petri net.
 *
 * This class is immutable.
 *
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 */
public class Region<PLACE> {
	private final ImmutableSet<PLACE> mRegion;
	private final LazyInt mHash;

	/**
	 * Creates a new region.
	 *
	 * NOTE: The constructor does not check the invariants that should be satisfied by regions (see above). Checking
	 * these would be prohibitively expensive. Thus, it is the caller's responsibility to only call this constructor
	 * with places satisfying these invariants.
	 *
	 * @param region
	 *            the set of places constituting the region
	 */
	public Region(final ImmutableSet<PLACE> region) {
		assert !region.isEmpty() : "Region is empty";
		mRegion = region;
		mHash = new LazyInt(region::hashCode);
	}

	/**
	 * Creates a region containing only a single place.
	 *
	 * @param <P>
	 *            the type of places
	 * @param place
	 *            the only place in the region
	 * @return the singleton region
	 */
	public static <P> Region<P> singleton(final P place) {
		return new Region<>(ImmutableSet.singleton(place));
	}

	/**
	 * Checks if a given place is in this region.
	 *
	 * @param place
	 *            the place to check
	 * @return {@code true} if the given place is in this region, {@code false} otherwise
	 */
	public boolean contains(final PLACE place) {
		return mRegion.contains(place);
	}

	/**
	 * @return the set of all places in region
	 */
	public ImmutableSet<PLACE> getPlaces() {
		return mRegion;
	}

	/**
	 * Determines the size of this region.
	 *
	 * @return the number of places
	 */
	public int size() {
		return mRegion.size();
	}

	@Override
	public boolean equals(final Object obj) {
		return obj == this || obj instanceof final Region<?> other && mRegion.equals(other.getPlaces());
	}

	@Override
	public int hashCode() {
		// Hash code is cached for performance reasons. Regions are almost always used in sets (typically, HashSets)
		// such as territories, and each hash code computation requires an iteration over the set of places.
		return mHash.get();
	}

	@Override
	public String toString() {
		return mRegion.toString();
	}
}
