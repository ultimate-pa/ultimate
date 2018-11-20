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
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;


/**
 * A marking of a Petri Net which is a set of places.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbols type
 * @param <PLACE>
 *            place content type
 */
public class Marking<LETTER, PLACE> implements Iterable<PLACE>, Serializable {
	private static final long serialVersionUID = -357669345268897194L;

	private final Set<PLACE> mPlaces;

	/**
	 * Constructor.
	 *
	 * @param places
	 *            places
	 */
	public Marking(final Set<PLACE> places) {
		mPlaces = places;
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
		final Marking<LETTER, PLACE> other = (Marking<LETTER, PLACE>) obj;
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
		final int prime = 31;
		return prime + ((mPlaces == null) ? 0 : mPlaces.hashCode());
	}

	/**
	 * @param transition
	 *            The transition.
	 * @return true, if the marking enables the specified transition.
	 */
	public boolean isTransitionEnabled(final ITransition<LETTER, PLACE> transition, final IPetriNet<LETTER, PLACE> net) {
//		if (transition instanceof InhibitorTransition<?, ?>) {
//			final InhibitorTransition<LETTER, PLACE> it = (InhibitorTransition<LETTER, PLACE>) transition;
//			if (containsAny(it.getInhibitors())) {
//				return false;
//			}
//		}
		return mPlaces.containsAll(net.getPredecessors(transition));
	}

	/*
	/**
	 * Adds the places of another marking.
	 *
	 * @param other
	 */
	/*
	public void add(Marking<LETTER, PLACE> other) {
		mPlaces.addAll(other.mPlaces);
	}
	*/

	/**
	 * @param transition
	 *            The transition.
	 * @return The marking to which the occurrence of the specified transition leads.
	 * @throws PetriNetNot1SafeException
	 */
	public Marking<LETTER, PLACE> fireTransition(final ITransition<LETTER, PLACE> transition,
			final IPetriNet<LETTER, PLACE> net) throws PetriNetNot1SafeException {
		final HashSet<PLACE> resultSet = new HashSet<>(mPlaces);
		final Set<PLACE> predecessors = net.getPredecessors(transition);
		resultSet.removeAll(predecessors);
		final Set<PLACE> successors = net.getSuccessors(transition);
		resultSet.addAll(successors);
		if (mPlaces.size() - predecessors.size() + successors.size() != resultSet.size()) {
			final List<PLACE> unsafePlaces = mPlaces.stream().filter(x -> !predecessors.contains(x))
					.filter(successors::contains).collect(Collectors.toList());
			throw new PetriNetNot1SafeException(getClass(), unsafePlaces);
		}
		return new Marking<>(resultSet);
	}

	/**
	 * Revokes the occurrence of the specified transition if valid.
	 *
	 * @param transition
	 *            transition
	 * @return {@code true} iff all successor places are contained.
	 */
	public boolean undoTransition(final ITransition<LETTER, PLACE> transition, final IPetriNet<LETTER, PLACE> net) {
		if (!mPlaces.containsAll(net.getSuccessors(transition))) {
			return false;
		}
		mPlaces.removeAll(net.getSuccessors(transition));
		mPlaces.addAll(net.getPredecessors(transition));
		return true;
	}

	@Override
	public String toString() {
		return this.mPlaces.toString();
	}

	public Stream<PLACE> stream() {
		return mPlaces.stream();
	}


}
