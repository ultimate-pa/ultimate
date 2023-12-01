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

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.Kingdom;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */

public final class Territory<PLACE, LETTER> {

	/**
	 * Set of regions in Territory.
	 */
	private final Set<Region<PLACE, LETTER>> mTerritory;

	/**
	 * Data structure which contains the different Regions of a Territory.
	 *
	 * @param regions
	 *            Set of regions for which a Territory should be created.
	 */
	public Territory(final Set<Region<PLACE, LETTER>> regions) {
		mTerritory = regions;
	}

	/**
	 * Create a Kingdoms territory.
	 *
	 * @param kingdom
	 *            Kingdom for which a corresponding Territory should be created.
	 */
	public Territory(final Kingdom<PLACE, LETTER> kingdom) {
		mTerritory = getKingdomRegions(kingdom);
	}

	private Set<Region<PLACE, LETTER>> getKingdomRegions(final Kingdom<PLACE, LETTER> kingdom) {
		final Set<Region<PLACE, LETTER>> kingdomRegions =
				kingdom.getRealms().stream().map(realm -> new Region<PLACE, LETTER>(realm)).collect(Collectors.toSet());
		return kingdomRegions;
	}

	private void getAllMarkings(final Set<Region<PLACE, LETTER>> remainingTerritory, final Set<PLACE> currentMarking,
			final Set<Marking<PLACE>> treaty) {
		if (remainingTerritory.isEmpty()) {
			treaty.add(new Marking<>(ImmutableSet.of(currentMarking)));
			return;
		}
		final Region<PLACE, LETTER> currentRegion = remainingTerritory.iterator().next();
		remainingTerritory.remove(currentRegion);

		for (final PLACE place : currentRegion.getPlaces()) {
			currentMarking.add(place);
			getAllMarkings(new HashSet<>(remainingTerritory), new HashSet<>(currentMarking), treaty);
			currentMarking.remove(place);
		}
	}

	/**
	 * @return Set of regions in Territory.
	 */
	public Set<Region<PLACE, LETTER>> getRegions() {
		return mTerritory;
	}

	/**
	 * Calculate the treaty by creating a set of markings picking one place per region.
	 *
	 * @return Treaty of the Territory.
	 */
	public Set<Marking<PLACE>> getTreaty() {
		final Set<Marking<PLACE>> treatySet = new HashSet<>();
		final Set<Region<PLACE, LETTER>> territoryRegions = new HashSet<>(mTerritory);
		getAllMarkings(territoryRegions, new HashSet<>(), treatySet);
		return treatySet;
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
		final Territory<PLACE, LETTER> other = (Territory<PLACE, LETTER>) obj;
		return mTerritory.equals(other.getRegions());
	}

	@Override
	public int hashCode() {
		return mTerritory.hashCode();
	}

}
