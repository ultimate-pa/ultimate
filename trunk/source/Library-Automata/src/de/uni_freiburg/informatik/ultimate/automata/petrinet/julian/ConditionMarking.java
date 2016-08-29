/*
 * Copyright (C) 2011-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.io.Serializable;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

/**
 * A Marking of an occurencenet which is a set of conditions.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */

public class ConditionMarking<S, C> implements Iterable<Condition<S, C>>,
		Serializable {
	private static final long serialVersionUID = -357669345268897194L;

	private final Set<Condition<S, C>> mConditions;

	public ConditionMarking(final Set<Condition<S, C>> conditions) {
		mConditions = conditions;
	}

	public boolean contains(final Condition<S, C> p) {
		return mConditions.contains(p);
	}

	/**
	 * @see java.util.Set#containsAll(java.util.Collection)
	 */
	public boolean containsAll(final Collection<?> c) {
		return mConditions.containsAll(c);
	}

	/**
	 * @see java.util.Set#isEmpty()
	 */
	public boolean isEmpty() {
		return mConditions.isEmpty();
	}

	/**
	 * @see java.util.Set#iterator()
	 */
	@Override
	public Iterator<Condition<S, C>> iterator() {
		return mConditions.iterator();
	}

	/**
	 * @see java.util.Set#size()
	 */
	public int size() {
		return mConditions.size();
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
		final ConditionMarking<S, C> other = (ConditionMarking<S, C>) obj;
		if (mConditions == null) {
			if (other.mConditions != null) {
				return false;
			}
		} else if (!mConditions.equals(other.mConditions)) {
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
				+ ((mConditions == null) ? 0 : mConditions.hashCode());
		return result;
	}

	/**
	 * 
	 * @return true, if the marking enables the specified transition.
	 */
	public boolean isEventEnabled(final Event<S, C> event) {
		return mConditions.containsAll(event.getPredecessorConditions());
	}

	/**
	 * Adds the conditions of another marking.
	 */
	public void add(final ConditionMarking<S, C> other) {
		mConditions.addAll(other.mConditions);
	}
	
	/**
	 * Adds the markings conditions to another set.
	 */
	public void addTo(final Set<Condition<S, C>> other) {
		other.addAll(mConditions);
	}

	/**
	 * returns the marking to which the occurrence of the specified transition
	 * leads.
	 */
	public ConditionMarking<S, C> fireEvent(final Event<S, C> event) {
		assert (isEventEnabled(event));
		final HashSet<Condition<S, C>> resultSet = new HashSet<Condition<S, C>>(
				mConditions);
		resultSet.removeAll(event.getPredecessorConditions());
		resultSet.addAll(event.getSuccessorConditions());
		return new ConditionMarking<S, C>(resultSet);
	}

	/**
	 * revokes the occurence of the specified transition if valid.
	 */
	public boolean undoEvent(final Event<S, C> event) {
		if (!mConditions.containsAll(event.getSuccessorConditions())) {
			return false;
		}
		mConditions.removeAll(event.getSuccessorConditions());
		mConditions.addAll(event.getPredecessorConditions());
		return true;
	}

	@Override
	public String toString() {
		return this.mConditions.toString();
	}

	/**
	 * Creates and returns a new marking containing the places corresponding to
	 * the conditionMarkings Conditions.
	 */
	public Marking<S, C> getMarking() {
		final HashSet<Place<S, C>> mark = new HashSet<Place<S, C>>();
		for (final Condition<S, C> c : mConditions) {
			assert !mark.contains(c.getPlace()) : "Petri Net not one safe!";
			mark.add(c.getPlace());
		}
		return new Marking<S, C>(mark);
	}
}
