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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.io.Serializable;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;

/**
 * A Marking of an occurencenet which is a set of conditions.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public class ConditionMarking<LETTER, PLACE> implements Iterable<Condition<LETTER, PLACE>>, Serializable {
	private static final long serialVersionUID = -357669345268897194L;

	private final Set<Condition<LETTER, PLACE>> mConditions;

	public Set<Condition<LETTER, PLACE>> getConditions(){
		return mConditions;
	}
	/**
	 * Constructor.
	 *
	 * @param conditions
	 *            set of conditions
	 */
	public ConditionMarking(final Set<Condition<LETTER, PLACE>> conditions) {
		mConditions = conditions;
	}

	/**
	 * @param condition
	 *            A condition.
	 * @return {@code true} iff the condition is contained
	 */
	public boolean contains(final Condition<LETTER, PLACE> condition) {
		return mConditions.contains(condition);
	}

	/**
	 * @param conditions
	 *            Some conditions.
	 * @return {@code true} iff all conditions are contained.
	 * @see java.util.Set#containsAll(java.util.Collection)
	 */
	public boolean containsAll(final Collection<Condition<LETTER, PLACE>> conditions) {
		return mConditions.containsAll(conditions);
	}

	/**
	 * @return {@code true} iff there is no condition.
	 * @see java.util.Set#isEmpty()
	 */
	public boolean isEmpty() {
		return mConditions.isEmpty();
	}

	/**
	 * @see java.util.Set#iterator()
	 */
	@Override
	public Iterator<Condition<LETTER, PLACE>> iterator() {
		return Collections.unmodifiableSet(mConditions).iterator();
	}

	/**
	 * @return The number of conditions.
	 * @see java.util.Set#size()
	 */
	public int size() {
		return mConditions.size();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final ConditionMarking<?, ?> other = (ConditionMarking<?, ?>) obj;
		if (mConditions == null) {
			if (other.mConditions != null) {
				return false;
			}
		} else if (!mConditions.equals(other.mConditions)) {
			return false;
		}
		return true;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		return prime + ((mConditions == null) ? 0 : mConditions.hashCode());
	}

	/**
	 * @param event
	 *            An event.
	 * @return true, if the marking enables the specified transition.
	 */
	public boolean isEventEnabled(final Event<LETTER, PLACE> event) {
		return mConditions.containsAll(event.getPredecessorConditions());
	}

	/**
	 * Adds the markings conditions to another set.
	 *
	 * @param other
	 *            another set of conditions
	 */
	public void addTo(final Set<Condition<LETTER, PLACE>> other) {
		other.addAll(mConditions);
	}

	/**
	 * @param event
	 *            An event.
	 * @return the marking to which the occurrence of the specified transition leads.
	 */
	public ConditionMarking<LETTER, PLACE> fireEvent(final Event<LETTER, PLACE> event) {
		assert isEventEnabled(event);
		final HashSet<Condition<LETTER, PLACE>> resultSet = new HashSet<>(mConditions);
		resultSet.removeAll(event.getPredecessorConditions());
		resultSet.addAll(event.getSuccessorConditions());
		return new ConditionMarking<>(resultSet);
	}

	@Override
	public String toString() {
		return this.mConditions.toString();
	}

	/**
	 * @return A new marking containing the places corresponding to the conditionMarkings Conditions.
	 */
	public Marking<LETTER, PLACE> getMarking() throws PetriNetNot1SafeException {
		final HashSet<PLACE> mark = new HashSet<>();
		for (final Condition<LETTER, PLACE> c : mConditions) {
			final boolean wasAddedForTheFirstTime = mark.add(c.getPlace());
			if (!wasAddedForTheFirstTime) {
				throw new PetriNetNot1SafeException(this.getClass(), Collections.singleton(c.getPlace()));
			}
		}
		return new Marking<>(mark);
	}

	public Stream<Condition<LETTER, PLACE>> stream() {
		return mConditions.stream();
	}
}
