/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
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
 * 
 * @param <S>
 * @param <C>
 */

public class Marking<S, C> implements Iterable<Place<S, C>>, Serializable {
	private static final long serialVersionUID = -357669345268897194L;
	
	private final Set<Place<S, C>> m_Places;

	public Marking(Set<Place<S, C>> places) {
		m_Places = places;
	}

	/**
	 * @param o
	 * @return
	 */
	public boolean contains(Place<S, C> p) {
		return m_Places.contains(p);
	}

	/**
	 * @param c
	 * @return
	 * @see java.util.Set#containsAll(java.util.Collection)
	 */
	public boolean containsAll(Collection<?> c) {
		return m_Places.containsAll(c);
	}
	
	/**
	 * returns true, if the marking contains any of the specified places.
	 * @param places
	 * @return
	 */
	public boolean containsAny(Collection<Place<S, C>> places) {
		for (Place<S, C> place : places) {
			if (m_Places.contains(place))
				return true;
		}
		return false;
	}

	/**
	 * @return
	 * @see java.util.Set#isEmpty()
	 */
	public boolean isEmpty() {
		return m_Places.isEmpty();
	}

	/**
	 * @return
	 * @see java.util.Set#iterator()
	 */
	public Iterator<Place<S, C>> iterator() {
		return m_Places.iterator();
	}

	/**
	 * @return
	 * @see java.util.Set#size()
	 */
	public int size() {
		return m_Places.size();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Marking<S, C> other = (Marking<S, C>) obj;
		if (m_Places == null) {
			if (other.m_Places != null)
				return false;
		} else if (!m_Places.equals(other.m_Places))
			return false;
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
				+ ((m_Places == null) ? 0 : m_Places.hashCode());
		return result;
	}

	/**
	 * 
	 * @return true, if the marking enables the specified transition.
	 */
	public boolean isTransitionEnabled(ITransition<S, C> transition) {
		if (transition instanceof InhibitorTransition<?, ?>) {
			InhibitorTransition<S, C> it = (InhibitorTransition<S, C>) transition;
			if (containsAny(it.getInhibitors()))
				return false;
		}
		return m_Places.containsAll(transition.getPredecessors());
	}

//	/**
//	 * Adds the places of another marking.
//	 * 
//	 * @param other
//	 */
//	public void add(Marking<S, C> other) {
//		m_Places.addAll(other.m_Places);
//	}

	/**
	 * returns the marking to which the occurrence of the specified transition
	 * leads.
	 * 
	 * @param transition
	 * @return
	 */
	public Marking<S, C> fireTransition(ITransition<S, C> transition) {
		HashSet<Place<S, C>> resultSet = new HashSet<Place<S, C>>(m_Places);
		resultSet.removeAll(transition.getPredecessors());
		resultSet.addAll(transition.getSuccessors());
		return new Marking<S, C>(resultSet);
	}

	/**
	 * revokes the occurence of the specified transition if valid.
	 * @param transition
	 * @return true if the
	 */
	public boolean undoTransition(ITransition<S, C> transition) {
		if (!m_Places.containsAll(transition.getSuccessors()))
			return false;
		m_Places.removeAll(transition.getSuccessors());
		m_Places.addAll(transition.getPredecessors());
		return true;
	}

	@Deprecated
	public Marking(Collection<Place<S, C>> places) {
		m_Places = new HashSet<Place<S, C>>(places);
	}

	@Deprecated
	public Set<Place<S, C>> getPlaces() {
		return m_Places;
	}
	
	public String toString() {
		return this.m_Places.toString();
	}

}
