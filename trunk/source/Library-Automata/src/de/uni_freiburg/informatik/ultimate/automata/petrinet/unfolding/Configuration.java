/*
 * Copyright (C) 2012-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
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

import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SetOperations;

// TODO: rewrite this class, possibly split it up to resolve this horrible ambiguity
/**
 * Represents a Suffix of a Configuration. A Configuration is a Set of Events which is causally closed and
 * conflict-free. A Set E is called Suffix if there is a Configuration C, such that
 * <ul>
 * <li>C united with E is a Configuration</li>
 * <li>The intersection of C and E is empty</li>
 * </ul>
 * 
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @param <S>
 *            symbol type
 * @param <C>
 *            place content type
 */
public class Configuration<S, C> extends AbstractSet<Event<S, C>> implements Comparable<Configuration<S, C>> {
	private final Set<Event<S, C>> mEvents;
	private Set<Event<S, C>> mMin;
	private ArrayList<Transition<S, C>> mPhi;

	/**
	 * Constructs a Configuration (Not a Suffix). The set given as parameter has to be causally closed and
	 * conflict-free.
	 * 
	 * @param events
	 *            set of events
	 */
	public Configuration(final Set<Event<S, C>> events) {
		this(events, null);
	}

	/**
	 * Constructor with a minimum set of events.
	 * 
	 * @param events
	 *            set of events
	 * @param min
	 *            minimum set of events
	 */
	private Configuration(final Set<Event<S, C>> events, final Set<Event<S, C>> min) {
		mEvents = events;
		mMin = min;
	}

	public List<Transition<S, C>> getPhi() {
		if (mPhi == null) {
			mPhi = new ArrayList<>(mEvents.size());
			for (final Event<S, C> e : mEvents) {
				mPhi.add(e.getTransition());
			}
			Collections.sort(mPhi);
		}
		return mPhi;
	}

	/**
	 * Returns the causally minimal Events in this Configuration.
	 * An Event e is causally minimal in a Configuration,
	 * iff all Events preceding e are not in the configuration.
	 * 
	 * @return causally minimal Events in this Configuration
	 */
	public Configuration<S, C> getMin() {
		if (mMin == null) {
			mMin = computeMin();
		}
		return new Configuration<>(mMin);
	}

	private Set<Event<S, C>> computeMin() {
		return mEvents.stream()
				.filter(event -> SetOperations.disjoint(event.getPredecessorEvents(), mEvents))
				.collect(Collectors.toCollection(HashSet::new));
	}

	@Override
	public Iterator<Event<S, C>> iterator() {
		return mEvents.iterator();
	}

	@Override
	public int size() {
		return mEvents.size();
	}

	@Override
	public boolean add(final Event<S, C> arg0) {
		return mEvents.add(arg0);
	}

	@Override
	public boolean addAll(final Collection<? extends Event<S, C>> arg0) {
		return mEvents.addAll(arg0);
	}

	@Override
	public void clear() {
		mEvents.clear();
	}

	@Override
	public boolean contains(final Object arg0) {
		return mEvents.contains(arg0);
	}

	@Override
	public boolean containsAll(final Collection<?> arg0) {
		return mEvents.containsAll(arg0);
	}

	/**
	 * @param events
	 *            Some events.
	 * @return {@code true} iff the configuration contains any of the specified events
	 */
	public boolean containsAny(final Collection<Event<S, C>> events) {
		for (final Event<S, C> place : events) {
			if (mEvents.contains(place)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean isEmpty() {
		return mEvents.isEmpty();
	}

	@Override
	public boolean remove(final Object arg0) {
		return mEvents.remove(arg0);
	}

	/**
	 * @return A new Configuration that contains the set difference between the original configuration and its minimum
	 *         regarding the casual relation.
	 *         <p>
	 *         requires, that getMin() has been called.
	 */
	public Configuration<S, C> removeMin() {
		assert mMin != null : "getMin() must have been called before removeMin()";
		assert !mMin.isEmpty() : "The minimum of a configuration must not be empty.";
		final HashSet<Event<S, C>> events = new HashSet<>(mEvents);
		events.removeAll(mMin);
		final Set<Event<S, C>> min = Event.getSuccessorEvents(mMin);
		min.retainAll(events);
		final HashSet<Event<S, C>> newmin = new HashSet<>();
		for (final Event<S, C> e : min) {
			final Set<Event<S, C>> predEventsOfE = e.getPredecessorEvents();
			predEventsOfE.retainAll(mEvents);
			if (mMin.containsAll(predEventsOfE)) {
				newmin.add(e);
			}
		}
		return new Configuration<>(events, newmin);
	}

	@Override
	public boolean removeAll(final Collection<?> arg0) {
		return mEvents.removeAll(arg0);
	}

	@Override
	public boolean retainAll(final Collection<?> arg0) {
		return mEvents.retainAll(arg0);
	}

	@Override
	public Object[] toArray() {
		return mEvents.toArray();
	}

	@Override
	public <T> T[] toArray(final T[] arg0) {
		return mEvents.toArray(arg0);
	}

	/**
	 * Compares configurations initially based on size. In case of equal size, lexically compares the ordered sequences
	 * of events with respect to the the total order on their transitions.
	 */
	@Override
	public int compareTo(final Configuration<S, C> other) {
		if (size() != other.size()) {
			return size() - other.size();
		}
		final List<Transition<S, C>> phi1 = getPhi();
		final List<Transition<S, C>> phi2 = other.getPhi();
		for (int i = 0; i < phi1.size(); i++) {
			final Transition<S, C> t1 = phi1.get(i);
			final Transition<S, C> t2 = phi2.get(i);
			final int result = t1.getTotalOrderId() - t2.getTotalOrderId();
			if (result != 0) {
				return result;
			}
		}
		assert phi1.equals(phi2);
		return 0;
	}

	/**
	 * TODO Christian 2016-08-16: This does not override the Object.equals() method. It may be confusing when using in
	 * Collections.
	 * 
	 * @param other
	 *            another configuration
	 * @return {@code true} iff two given configurations have the same events.
	 */
	public boolean equals(final Configuration<S, C> other) {
		return containsAll(other) && other.containsAll(this);
	}

	/*
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result
				+ ((mEvents == null) ? 0 : mEvents.hashCode());
		return result;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		Configuration<S, C> other = (Configuration) obj;
		if (mEvents == null) {
			if (other.mEvents != null)
				return false;
		} else if (!mEvents.equals(other.mEvents))
			return false;
		return true;
	}
	*/
}
