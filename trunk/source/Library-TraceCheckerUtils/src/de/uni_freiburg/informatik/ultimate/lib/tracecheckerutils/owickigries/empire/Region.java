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

import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.Condition;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.Realm;

public class Region<PLACE, LETTER> {

	/**
	 * The set of places in Region.
	 */

	private final Set<PLACE> mRegion;

	public Region(final Set<PLACE> region) {
		mRegion = region;
	}

	public Region(final Realm<PLACE, LETTER> realm) {
		mRegion = getRealmPlaces(realm);
	}

	private Set<PLACE> getRealmPlaces(final Realm<PLACE, LETTER> realm) {
		final Set<PLACE> realmPlaces =
				realm.getConditions().stream().map(Condition::getPlace).collect(Collectors.toSet());
		return realmPlaces;
	}

	/**
	 * @return set of all places in region.
	 */
	public Set<PLACE> getPlaces() {
		return mRegion;
	}

	/**
	 * * Adds the specified place in to the set of places in the region.
	 *
	 * @param place
	 */
	public void addPlace(final PLACE place) {
		mRegion.add(place);
	}

	/**
	 * Add the specified set of places to the region.
	 *
	 * @param places
	 */
	public void addPlace(final Set<PLACE> places) {
		mRegion.addAll(places);
	}

	/**
	 * Removes the specified place from the region.
	 *
	 * @param place
	 */
	public void removePlace(final PLACE place) {
		if (mRegion.contains(place)) {
			mRegion.remove(place);
		}
	}

	/**
	 * @param petriNet
	 *            over which place corelation is checked.
	 * @return true if place is NOT corelated to all places in the region. TODO: place corelation!!!!
	 */
	public boolean checkCorelation(final IPetriNet<LETTER, PLACE> petriNet) {
		return true;
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
		final Region<PLACE, LETTER> other = (Region<PLACE, LETTER>) obj;
		return mRegion.equals(other.getPlaces());
	}

	@Override
	public int hashCode() {
		return mRegion.hashCode();
	}
}
