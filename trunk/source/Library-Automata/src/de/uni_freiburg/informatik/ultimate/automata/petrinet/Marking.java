/*
 * Copyright (C) 2011-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.io.Serializable;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * A marking of a Petri Net which is a set of places.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            place content type
 */
public class Marking<PLACE> implements Iterable<PLACE>, Serializable {
	private static final long serialVersionUID = -357669345268897194L;

	private final ImmutableSet<PLACE> mPlaces;

	/**
	 * Constructor.
	 *
	 * @param places
	 *            places
	 */
	public Marking(final ImmutableSet<PLACE> places) {
		mPlaces = Objects.requireNonNull(places);
	}

	/**
	 * @param place
	 *            The place.
	 * @return {@code true} iff the place is contained
	 * @see java.util.Set#contains(Object)
	 */
	public boolean contains(final PLACE place) {
		return mPlaces.contains(place);
	}

	/**
	 * @param places
	 *            The places.
	 * @return {@code true} iff all places are contained
	 * @see java.util.Set#containsAll(java.util.Collection)
	 */
	public boolean containsAll(final Collection<PLACE> places) {
		return mPlaces.containsAll(places);
	}

	/**
	 * @param places
	 *            The places.
	 * @return {@code true} if the marking contains any of the specified places.
	 */
	public boolean containsAny(final Collection<PLACE> places) {
		for (final PLACE place : places) {
			if (mPlaces.contains(place)) {
				return true;
			}
		}
		return false;
	}

	public boolean isEmpty() {
		return mPlaces.isEmpty();
	}

	/**
	 * @see java.util.Set#iterator()
	 */
	@Override
	public Iterator<PLACE> iterator() {
		return mPlaces.iterator();
	}

	/**
	 * @return The number of places.
	 * @see java.util.Set#size()
	 */
	public int size() {
		return mPlaces.size();
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
		final Marking<PLACE> other = (Marking<PLACE>) obj;
		if (mPlaces == null) {
			if (other.mPlaces != null) {
				return false;
			}
		} else if (!mPlaces.equals(other.mPlaces)) {
			return false;
		}
		return true;
	}

	@Override
	public int hashCode() {
		return mPlaces.hashCode();
	}

	/**
	 * @param transition
	 *            The transition.
	 * @return true, if the marking enables the specified transition.
	 */
	public <LETTER> boolean isTransitionEnabled(final Transition<LETTER, PLACE> transition) {
		return mPlaces.containsAll(transition.getPredecessors());
	}

	/**
	 * @param transition
	 *            The transition.
	 * @return The marking to which the occurrence of the specified transition leads.
	 * @throws PetriNetNot1SafeException
	 */
	public <LETTER> Marking<PLACE> fireTransition(final Transition<LETTER, PLACE> transition)
			throws PetriNetNot1SafeException {
		final Set<PLACE> predecessors = transition.getPredecessors();
		final Set<PLACE> successors = transition.getSuccessors();
		final Stream<PLACE> places =
				Stream.concat(mPlaces.stream().filter(x -> !predecessors.contains(x)), successors.stream());

		final Set<PLACE> resultSet;
		try {
			// Using DataStructureUtils is more memory-efficient than HashSet,
			// and avoiding HashSet copies should be faster.
			resultSet = DataStructureUtils.asSet(places);
		} catch (final IllegalArgumentException e) {
			// thrown if the "places" stream contains duplicate elements
			// see https://docs.oracle.com/en/java/javase/11/docs/api/java.base/java/util/Set.html#unmodifiable
			final List<PLACE> unsafePlaces = mPlaces.stream().filter(x -> !predecessors.contains(x))
					.filter(successors::contains).collect(Collectors.toList());
			throw new PetriNetNot1SafeException(getClass(), unsafePlaces);
		}

		return new Marking<>(ImmutableSet.of(resultSet));
	}

	@Override
	public String toString() {
		return this.mPlaces.toString();
	}

	public Stream<PLACE> stream() {
		return mPlaces.stream();
	}

	public ImmutableSet<PLACE> getPlaces() {
		return mPlaces;
	}
}
