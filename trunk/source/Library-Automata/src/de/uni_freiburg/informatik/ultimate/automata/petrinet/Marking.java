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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.InhibitorTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Place;

/**
 * A marking of a Petri Net which is a set of places.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @param <S>
 *            symbols type
 * @param <C>
 *            place content type
 */
public class Marking<S, C> implements Iterable<Place<C>>, Serializable {
	private static final long serialVersionUID = -357669345268897194L;

	private final Set<Place<C>> mPlaces;

	/**
	 * Constructor.
	 * 
	 * @param places
	 *            places
	 */
	public Marking(final Set<Place<C>> places) {
		mPlaces = places;
	}

	/**
	 * @param place
	 *            The place.
	 * @return {@code true} iff the place is contained
	 * @see java.util.Set#contains(Object)
	 */
	public boolean contains(final Place<C> place) {
		return mPlaces.contains(place);
	}

	/**
	 * @param places
	 *            The places.
	 * @return {@code true} iff all places are contained
	 * @see java.util.Set#containsAll(java.util.Collection)
	 */
	public boolean containsAll(final Collection<Place<C>> places) {
		return mPlaces.containsAll(places);
	}

	/**
	 * @param places
	 *            The places.
	 * @return {@code true} if the marking contains any of the specified places.
	 */
	public boolean containsAny(final Collection<Place<C>> places) {
		for (final Place<C> place : places) {
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
	public Iterator<Place<C>> iterator() {
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
		final Marking<S, C> other = (Marking<S, C>) obj;
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
	public boolean isTransitionEnabled(final ITransition<S, C> transition) {
		if (transition instanceof InhibitorTransition<?, ?>) {
			final InhibitorTransition<S, C> it = (InhibitorTransition<S, C>) transition;
			if (containsAny(it.getInhibitors())) {
				return false;
			}
		}
		return mPlaces.containsAll(transition.getPredecessors());
	}

	/*
	/**
	 * Adds the places of another marking.
	 *
	 * @param other
	 */
	/*
	public void add(Marking<S, C> other) {
		mPlaces.addAll(other.mPlaces);
	}
	*/

	/**
	 * @param transition
	 *            The transition.
	 * @return The marking to which the occurrence of the specified transition leads.
	 */
	public Marking<S, C> fireTransition(final ITransition<S, C> transition) {
		final HashSet<Place<C>> resultSet = new HashSet<>(mPlaces);
		resultSet.removeAll(transition.getPredecessors());
		resultSet.addAll(transition.getSuccessors());
		return new Marking<>(resultSet);
	}

	/**
	 * Revokes the occurrence of the specified transition if valid.
	 * 
	 * @param transition
	 *            transition
	 * @return {@code true} iff all successor places are contained.
	 */
	public boolean undoTransition(final ITransition<S, C> transition) {
		if (!mPlaces.containsAll(transition.getSuccessors())) {
			return false;
		}
		mPlaces.removeAll(transition.getSuccessors());
		mPlaces.addAll(transition.getPredecessors());
		return true;
	}

	@Override
	public String toString() {
		return this.mPlaces.toString();
	}
}
