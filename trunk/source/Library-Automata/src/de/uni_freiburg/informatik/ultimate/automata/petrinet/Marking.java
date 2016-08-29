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

/**
 * A Marking of a PetriNet which is a set of Places.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */

public class Marking<S, C> implements Iterable<Place<S, C>>, Serializable {
	private static final long serialVersionUID = -357669345268897194L;
	
	private final Set<Place<S, C>> mPlaces;

	public Marking(final Set<Place<S, C>> places) {
		mPlaces = places;
	}

	public boolean contains(final Place<S, C> p) {
		return mPlaces.contains(p);
	}

	/**
	 * @see java.util.Set#containsAll(java.util.Collection)
	 */
	public boolean containsAll(final Collection<?> c) {
		return mPlaces.containsAll(c);
	}
	
	/**
	 * returns true, if the marking contains any of the specified places.
	 */
	public boolean containsAny(final Collection<Place<S, C>> places) {
		for (final Place<S, C> place : places) {
			if (mPlaces.contains(place)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @see java.util.Set#isEmpty()
	 */
	public boolean isEmpty() {
		return mPlaces.isEmpty();
	}

	/**
	 * @see java.util.Set#iterator()
	 */
	@Override
	public Iterator<Place<S, C>> iterator() {
		return mPlaces.iterator();
	}

	/**
	 * @see java.util.Set#size()
	 */
	public int size() {
		return mPlaces.size();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
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

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((mPlaces == null) ? 0 : mPlaces.hashCode());
		return result;
	}

	/**
	 * 
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

//	/**
//	 * Adds the places of another marking.
//	 * 
//	 * @param other
//	 */
//	public void add(Marking<S, C> other) {
//		mPlaces.addAll(other.mPlaces);
//	}

	/**
	 * returns the marking to which the occurrence of the specified transition
	 * leads.
	 */
	public Marking<S, C> fireTransition(final ITransition<S, C> transition) {
		final HashSet<Place<S, C>> resultSet = new HashSet<Place<S, C>>(mPlaces);
		resultSet.removeAll(transition.getPredecessors());
		resultSet.addAll(transition.getSuccessors());
		return new Marking<S, C>(resultSet);
	}

	/**
	 * revokes the occurence of the specified transition if valid.
	 */
	public boolean undoTransition(final ITransition<S, C> transition) {
		if (!mPlaces.containsAll(transition.getSuccessors())) {
			return false;
		}
		mPlaces.removeAll(transition.getSuccessors());
		mPlaces.addAll(transition.getPredecessors());
		return true;
	}

	@Deprecated
	public Marking(final Collection<Place<S, C>> places) {
		mPlaces = new HashSet<Place<S, C>>(places);
	}

	@Deprecated
	public Set<Place<S, C>> getPlaces() {
		return mPlaces;
	}
	
	@Override
	public String toString() {
		return this.mPlaces.toString();
	}

}
