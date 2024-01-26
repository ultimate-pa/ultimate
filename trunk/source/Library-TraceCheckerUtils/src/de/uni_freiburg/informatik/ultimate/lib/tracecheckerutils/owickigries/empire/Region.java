/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Class represents a Region which is a sets of places. Region is an Immutable class.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 */
public final class Region<PLACE> {

	/**
	 * The set of places in Region.
	 */

	private final ImmutableSet<PLACE> mRegion;

	public Region(final ImmutableSet<PLACE> region) {
		assert !region.isEmpty() : "Region is empty";
		mRegion = region;
	}

	public boolean contains(final PLACE place) {
		return mRegion.contains(place);
	}

	/**
	 * @return set of all places in region.
	 */
	public ImmutableSet<PLACE> getPlaces() {
		return mRegion;
	}

	public int size() {
		return mRegion.size();
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final Region<PLACE> other = (Region<PLACE>) obj;
		return mRegion.equals(other.getPlaces());
	}

	@Override
	public int hashCode() {
		return mRegion.hashCode();
	}

	@Override
	public String toString() {
		return mRegion.toString();
	}
}
