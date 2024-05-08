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
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Class represents a Territory which is a set of Regions. Territory is Immutable.
 *
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 */

public final class Territory<PLACE> {

	/**
	 * Set of regions in Territory.
	 */
	private final ImmutableSet<Region<PLACE>> mTerritory;

	/**
	 * Data structure which contains the different Regions of a Territory.
	 *
	 * @param regions
	 *            Set of regions for which a Territory should be created.
	 */
	public Territory(final ImmutableSet<Region<PLACE>> regions) {
		mTerritory = regions;
	}

	private void getAllMarkings(final Set<Region<PLACE>> remainingTerritory, final Set<PLACE> currentMarking,
			final Set<Marking<PLACE>> treaty) {
		if (remainingTerritory.isEmpty()) {
			treaty.add(new Marking<>(ImmutableSet.of(currentMarking)));
			return;
		}
		final Region<PLACE> currentRegion = remainingTerritory.iterator().next();
		remainingTerritory.remove(currentRegion);

		for (final PLACE place : currentRegion.getPlaces()) {
			currentMarking.add(place);
			getAllMarkings(new HashSet<>(remainingTerritory), new HashSet<>(currentMarking), treaty);
			currentMarking.remove(place);
		}
	}

	/**
	 * Get the union of all places in the Territory's Regions.
	 *
	 * @return Set of all places in Territory.
	 */
	public Set<PLACE> getPlaces() {
		final Set<PLACE> places = mTerritory.stream().flatMap(r -> r.getPlaces().stream()).collect(Collectors.toSet());
		return places;
	}

	/**
	 * @return Set of regions in Territory.
	 */
	public ImmutableSet<Region<PLACE>> getRegions() {
		return mTerritory;
	}

	/**
	 * Calculate the treaty by creating a set of markings picking one place per region.
	 *
	 * @return Treaty of the Territory.
	 */
	public Set<Marking<PLACE>> getTreaty() {
		final Set<Marking<PLACE>> treatySet = new HashSet<>();
		final Set<Region<PLACE>> territoryRegions = new HashSet<>(mTerritory);
		getAllMarkings(territoryRegions, new HashSet<>(), treatySet);
		return treatySet;
	}

	public int size() {
		return mTerritory.size();
	}

	public boolean subsumes(final Territory<PLACE> subsumee) {
		final var bigRegions = new HashSet<>(getRegions());
		for (final var smallRegion : subsumee.getRegions()) {
			final var it = bigRegions.iterator();
			boolean found = false;
			while (it.hasNext()) {
				final var bigRegion = it.next();
				if (bigRegion.getPlaces().containsAll(smallRegion.getPlaces())) {
					it.remove();
					found = true;
					break;
				}
			}
			if (!found) {
				return false;
			}
		}
		return true;
	}

	public boolean containsMarking(final Marking<PLACE> marking) {
		final Set<Region<PLACE>> regions = new HashSet<>(getRegions());
		if (marking.size() != regions.size()) {
			return false;
		}
		for (final PLACE place : marking.getPlaces()) {
			var found = false;
			final var it = regions.iterator();
			while (!found && it.hasNext()) {
				final var region = it.next();
				if (region.contains(place)) {
					found = true;
					regions.remove(region);
				}
			}
			if (!found) {
				return false;
			}
		}
		return regions.isEmpty();
	}

	public <L> boolean enables(final PLACE lawPlace, final Transition<L, PLACE> transition,
			final Set<PLACE> assertionPlaces) {
		final var regions = new HashSet<>(getRegions());
		for (final var place : transition.getPredecessors()) {
			if (place.equals(lawPlace) || (assertionPlaces.contains(place))) {
				continue;
			}

			final var it = regions.iterator();
			boolean found = false;
			while (!found && it.hasNext()) {
				final var region = it.next();
				if (region.contains(place)) {
					found = true;
					it.remove();
				}
			}
			if (!found) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Get all transitions of a PetriNet that are enabled by the territory.
	 *
	 * @param <L>
	 * @param successorProvider
	 *            Petri Net successor Provider
	 * @param lawPlace
	 *            Law place corresponding to the Territory
	 * @param assertionPlaces
	 *            Assertion places of the proof automata
	 * @return
	 */
	public <L> Stream<Transition<L, PLACE>> getEnabledTransitions(
			final IPetriNetSuccessorProvider<L, PLACE> successorProvider, final PLACE lawPlace,
			final Set<PLACE> assertionPlaces) {

		final var mayPlaces = DataStructureUtils.union(getPlaces(), Set.of(lawPlace), assertionPlaces);
		return successorProvider.getSuccessorTransitionProviders(getPlaces(), mayPlaces).stream()
				.flatMap(provider -> provider.getTransitions().stream())
				.filter(t -> enables(lawPlace, t, assertionPlaces));
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
		final Territory<PLACE> other = (Territory<PLACE>) obj;
		return mTerritory.equals(other.getRegions());
	}

	@Override
	public int hashCode() {
		return mTerritory.hashCode();
	}

	@Override
	public String toString() {
		return mTerritory.toString();
	}
}
