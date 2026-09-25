/*
 * Copyright (C) 2025 Matthias Zumkeller
 * Copyright (C) 2025 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.directed;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.Region;
import de.uni_freiburg.informatik.ultimate.util.LazyInt;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class ConnectedRegion<L, P> extends Region<P> {

	private final ImmutableSet<Transition<L, P>> mTransitions;
	private final LazyInt mHash;

	public ConnectedRegion(final ImmutableSet<P> region, final ImmutableSet<Transition<L, P>> transitions) {
		super(region);
		mTransitions = transitions;
		mHash = new LazyInt(region::hashCode);
	}

	/**
	 * Creates a connected region containing only a single place and an empty set of transitions.
	 *
	 * @param <L>
	 *            the type of transitions
	 * @param <P>
	 *            the type of places
	 * @param place
	 *            the only place in the region
	 * @return the singleton connected region
	 */
	public static <L, P> ConnectedRegion<L, P> connectedSingleton(final P place) {
		return new ConnectedRegion<>(ImmutableSet.singleton(place), ImmutableSet.empty());
	}

	public static <L, P> Region<P> intersectConnectedRegions(final Set<ConnectedRegion<L, P>> connectedRegions,
			final P startingPlace) {
		final var transitionIntersection = connectedRegions.stream().map(r -> new HashSet<>(r.getTransitions()))
				.reduce((t1, t2) -> new HashSet<>(DataStructureUtils.intersection(t1, t2)));
		final var transitions = transitionIntersection.orElse(new HashSet<>());
		final var intersection = connectedRegions.stream().map(r -> new HashSet<>(r.getPlaces()))
				.reduce((r1, r2) -> new HashSet<>(DataStructureUtils.intersection(r1, r2)));
		final var jointPlaces = intersection.orElse(new HashSet<>());
		assert !jointPlaces.isEmpty() : "No common place";
		final var regionPlaces = new HashSet<P>();
		regionPlaces.add(startingPlace);
		final var queue = new ArrayDeque<P>();
		queue.offer(startingPlace);
		final var visited = new HashSet<P>();
		while (!queue.isEmpty()) {
			final var currentPlace = queue.poll();
			if (!visited.add(currentPlace)) {
				continue;
			}
			final var possibleSuccessors = transitions.stream()
					.filter(t -> t.getPredecessors().contains(currentPlace) && t.getPredecessors().size() == 1
							&& t.getSuccessors().size() == 1)
					.flatMap(t -> t.getSuccessors().stream()).collect(Collectors.toSet());
			final var jointSuccessors = DataStructureUtils.intersection(jointPlaces, possibleSuccessors);
			regionPlaces.addAll(jointSuccessors);
			for (final P p : jointSuccessors) {
				if (visited.contains(p)) {
					continue;
				}
				queue.offer(p);
			}
		}
		return new Region<>(ImmutableSet.of(regionPlaces));
	}

	public ImmutableSet<Transition<L, P>> getTransitions() {
		return mTransitions;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj == this || obj instanceof final ConnectedRegion<?, ?> other && getPlaces().equals(other.getPlaces())
				&& mTransitions.equals(other.getTransitions());
	}

	@Override
	public int hashCode() {
		// Hash code is cached for performance reasons. Regions are almost always used in sets (typically, HashSets)
		// such as territories, and each hash code computation requires an iteration over the set of places.
		return mHash.get();
	}
}
