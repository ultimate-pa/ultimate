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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * A <em>territory</em> consists of several {@link Region}s, and represents a collection of reachable markings of a
 * Petri net.
 *
 * Territories should satisfy the invariants that any two places in different regions of the territory are co-related,
 * and that any marking in the territory's treaty (see {@link #getTreaty()}) is a reachable marking.
 *
 * This class is immutable.
 *
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri net
 */
public final class Territory<P, R extends Region<P>> {
	private final ImmutableSet<R> mRegions;

	// Cached map of places in the territory to the respective region in the territory that contains the place.
	// This is computed on-demand in #ensurePlaceMap().
	private Map<P, R> mPlaceMap;

	/**
	 * Creates a new territory.
	 *
	 * NOTE: The constructor does not check the invariants that should be satisfied by territories (see above). Checking
	 * these would be prohibitively expensive. Thus, it is the caller's responsibility to only call this constructor
	 * with regions satisfying these invariants.
	 *
	 * @param regions
	 *            the set of regions constituting the territory
	 */
	public Territory(final ImmutableSet<R> regions) {
		assert !regions.isEmpty() : "cannot create an empty territory";
		mRegions = regions;
	}

	/**
	 * @return the regions constituting this territory
	 */
	public ImmutableSet<R> getRegions() {
		return mRegions;
	}

	/**
	 * @return the set of all places in this territory, which corresponds to the union of its regions.
	 */
	public ImmutableSet<P> getPlaces() {
		ensurePlaceMap();
		return ImmutableSet.of(mPlaceMap.keySet());
	}

	/**
	 * Determines if this territory contains a given place.
	 *
	 * @param place
	 *            the place to check
	 * @return {@code true} if one of the regions in this territory contains the place, {@code false} otherwise
	 */
	public boolean containsPlace(final P place) {
		ensurePlaceMap();
		return mPlaceMap.containsKey(place);
	}

	/**
	 * Retrieves the size of the territory.
	 *
	 * @return the number of regions in the territory
	 */
	public int size() {
		return mRegions.size();
	}

	/**
	 * Determines whether this territory <em>subsumes</em> a given territory.
	 *
	 * One territory subsumes another if the subsuming territory's treaty (see {@link #getTreaty()}) is a superset of
	 * the subsumed territory's treaty.
	 *
	 * NOTE: The implementation of this method does not actually compute the treaty, and should be reasonably efficient.
	 *
	 * @param subsumee
	 *            the territory for which subsumption should be checked
	 * @return {@code true} if this territory subsumes the given territory, {@code false} otherwise
	 */
	public boolean subsumes(final Territory<P, R> subsumee) {
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

	/**
	 * Determines whether a given marking is represented by this territory, i.e., whether it is contained in the treaty,
	 * see {@link #getTreaty()}.
	 *
	 * NOTE: The implementation of this method does not actually compute the treaty, and should be reasonably efficient.
	 *
	 * @param marking
	 *            the marking for which membership in the treaty should be checked
	 * @return {@code true} if this territory's treaty contains the given marking, {@code false} otherwise
	 */
	public boolean containsMarking(final Marking<P> marking) {
		final Set<R> regions = new HashSet<>(getRegions());
		if (marking.size() != regions.size()) {
			return false;
		}
		for (final P place : marking.getPlaces()) {
			var found = false;
			final var it = regions.iterator();
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
		return regions.isEmpty();
	}

	/**
	 * Determines if this territory <em>enables</em> a given transition of a Petri net.
	 *
	 * A territory enables a transition if the territory's treating contains any marking that enables the transition.
	 *
	 * @param transition
	 *            the transition for which enabledness is checked
	 * @return {@code true} if this territory enables the given transition, {@code false} otherwise
	 */
	public boolean enables(final Transition<?, P> transition) {
		final var regions = new HashSet<>(getRegions());
		final var predecessors = transition.getPredecessors();
		for (final var place : predecessors) {
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
	 * Get all transitions of a Petri net that are enabled by this territory.
	 *
	 * @see #enables(Transition)
	 *
	 * @param <L>
	 *            The type of labels on the transitions
	 * @param net
	 *            A Petri net (containing all places of this territory) whose enabled transitions shall be collected
	 * @return a stream of all transitions enabled in some marking represented by this territory
	 */
	public <L> Stream<Transition<L, P>> getEnabledTransitions(final IPetriNet<L, P> net) {
		final var places = getPlaces();
		return net.getSuccessorTransitionProviders(places, places).stream()
				.flatMap(provider -> provider.getTransitions().stream()).filter(this::enables);
	}

	/**
	 * Checks if some other territory is a successor of this territory for a given transition.
	 *
	 * A given territory is the successor of this territory, if this territory enables the transition (see
	 * {@link #enables(Transition)}), and for every region of this territory containing some predecessor place of the
	 * transition, there exists a region in the given territory containing a successor place of the transition. These
	 * successor regions must be pairwise distinct (no two successor places may belong to the same region), but they may
	 * be the same region that (in this territory) contains the predecessor place. In fact, a territory may be its own
	 * successor (not only for self-loop transitions). All bystander regions of the transition in this territory (see
	 * {@link #getBystanders(Transition)}) must also be present in the given territory.
	 *
	 * The above conditions imply that (but are stronger than) for every marking in this territory's treaty that enables
	 * the transition, the marking resulting from firing the transition is in the successor territory's treaty.
	 *
	 * @param otherTerritory
	 *            the potential successor territory
	 * @param transition
	 *            a transition that is enabled by this territory
	 * @return {@code true} if {@code otherTerritory} is a successor of this territory for {@code transition},
	 *         {@code false} otherwise
	 */
	public boolean isSuccessor(final Territory<P, R> otherTerritory, final Transition<?, P> transition) {
		final var bystanders = getBystanders(transition);
		final var successorPlaces = transition.getSuccessors();
		if (!otherTerritory.getRegions().containsAll(bystanders)
				|| !otherTerritory.getPlaces().containsAll(successorPlaces)) {
			return false;
		}
		final var potentialSuccessors = DataStructureUtils.difference(otherTerritory.getRegions(), bystanders).stream()
				.collect(Collectors.toSet());
		if (potentialSuccessors.size() != successorPlaces.size()) {
			return false;
		}
		for (final P succPlace : successorPlaces) {
			final var succRegions =
					potentialSuccessors.stream().filter(r -> r.contains(succPlace)).collect(Collectors.toSet());
			if (succRegions.size() != 1) {
				return false;
			}
			potentialSuccessors.removeAll(succRegions);
		}
		return true;
	}

	/**
	 * Get bystander regions in the territory for a given transition (which is enabled by this territory).
	 *
	 * A bystander region is a region of the territory that does not contain any of the transition's predecessor places.
	 *
	 * @param transition
	 *            A transition enabled by this territory
	 * @return the set of bystander regions
	 */
	public Set<R> getBystanders(final Transition<?, P> transition) {
		assert enables(transition) : "Territory does not enable the given transition";

		ensurePlaceMap();
		final var bystanders = new HashSet<>(mRegions);
		for (final var predecessor : transition.getPredecessors()) {
			bystanders.remove(mPlaceMap.get(predecessor));
		}
		return bystanders;
	}

	/**
	 * Retrieves all regions that contain at least one place in a given set of places.
	 *
	 * @param places
	 *            a set of places
	 * @return the set of corresponding regions
	 */
	public Set<R> getPlacesRegions(final Set<P> places) {
		ensurePlaceMap();
		return places.stream().map(mPlaceMap::get).collect(Collectors.toSet());
	}

	public R getPlaceRegion(final P place) {
		ensurePlaceMap();
		assert containsPlace(place) : "No region contains the place";
		return mPlaceMap.get(place);
	}

	private void ensurePlaceMap() {
		if (mPlaceMap != null) {
			return;
		}

		mPlaceMap = new HashMap<>();
		for (final var region : mRegions) {
			for (final var place : region.getPlaces()) {
				mPlaceMap.put(place, region);
			}
		}
	}

	@Override
	public boolean equals(final Object obj) {
		return this == obj || (obj instanceof final Territory<?, ?> other && mRegions.equals(other.getRegions()));
	}

	@Override
	public int hashCode() {
		return mRegions.hashCode();
	}

	@Override
	public String toString() {
		return mRegions.toString();
	}
}
