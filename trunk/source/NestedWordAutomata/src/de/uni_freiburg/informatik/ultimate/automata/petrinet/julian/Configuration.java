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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

// TODO: rewrite this class, possibly split it up to resolve this horrible ambiguity
/**
 * Represents a Suffix of a Configuration. A Configuration is a Set of Events
 * which is causally closed and conflict-free. A Set E is called Suffix if there
 * is a Configuration C, such that
 * <ul>
 * <li>
 * C united with E is a Configuration</li>
 * <li>
 * The intersection of C and E is empty</li>
 * </ul>
 * 
 * @param <S>
 * @param <C>
 */
public class Configuration<S, C> extends AbstractSet<Event<S, C>> implements
		Comparable<Configuration<S, C>> {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);
	private Set<Event<S, C>> m_Events;
	private Set<Event<S, C>> m_Min;
	private ArrayList<Transition<S, C>> m_Phi = null;

	/**
	 * constructs a Configuration (Not a Suffix). The set given as parameter has
	 * to be causally closed and conflict-free.
	 * 
	 * @param events
	 */
	public Configuration(Set<Event<S, C>> events) {
		// this.m_Events = new HashSet<Event<S, C>>(events);
		this.m_Events = events;
	}

	private Configuration(Set<Event<S, C>> events, Set<Event<S, C>> min) {
		// this.m_Events = new HashSet<Event<S, C>>(events);
		this.m_Events = events;
		this.m_Min = min;
	}

	private List<Transition<S, C>> getPhi() {

		if (m_Phi == null) {
			m_Phi = new ArrayList<Transition<S, C>>(m_Events.size());
			for (Event<S, C> e : m_Events) {
				m_Phi.add(e.getTransition());
			}
			Collections.sort(m_Phi);
			s_Logger.debug("PhiSorted: " + m_Phi);
		}
		// return Collections.unmodifiableList(m_Phi);
		return m_Phi;
	}

	/*
	 * public Configuration<S, C> getMin() { Set<Event<S, C>> result = new
	 * HashSet<Event<S, C>>();
	 * 
	 * return new Configuration<S, C>(result); }
	 */

	/**
	 * returns the minimum of the Set of Events regarding the causal relation.
	 * 
	 * only yields the correct result, if it either has been precomputed when
	 * the Object was constructed, or this is a proper Configuration (not a
	 * suffix.)
	 * 
	 * @param unf
	 * @return
	 */
	public Configuration<S, C> getMin(BranchingProcess<S, C> unf) {
		Set<Event<S, C>> result;
		if (m_Min != null)
			result = m_Min;
		else {
			result = new HashSet<Event<S, C>>(unf.getMinEvents());
			result.retainAll(m_Events);
			/*
			 * for (Event<S, C> event : unf.getMinDot()) { if
			 * (m_Events.contains(event)) result.add(event); }
			 */
			m_Min = result;
		}
		return new Configuration<S, C>(result);
	}

	@Override
	public Iterator<Event<S, C>> iterator() {
		return m_Events.iterator();
	}

	@Override
	public int size() {
		return m_Events.size();
	}

	@Override
	public boolean add(Event<S, C> arg0) {
		return m_Events.add(arg0);
	}

	@Override
	public boolean addAll(Collection<? extends Event<S, C>> arg0) {
		return m_Events.addAll(arg0);
	}

	@Override
	public void clear() {
		m_Events.clear();
	}

	@Override
	public boolean contains(Object arg0) {
		return m_Events.contains(arg0);
	}

	@Override
	public boolean containsAll(Collection<?> arg0) {
		return m_Events.containsAll(arg0);
	}

	/**
	 * returns true, if the configuration contains any of the specified events.
	 * 
	 * @param events
	 * @return
	 */
	public boolean containsAny(Collection<Event<S, C>> events) {
		for (Event<S, C> place : events) {
			if (m_Events.contains(place))
				return true;
		}
		return false;
	}

	@Override
	public boolean isEmpty() {
		return m_Events.isEmpty();
	}

	@Override
	public boolean remove(Object arg0) {
		return m_Events.remove(arg0);
	}

	/**
	 * returns a new Configuration that contains the set difference between the
	 * original configuration and its minimum regarding the casual relation.
	 * 
	 * requires, that getMin() has been called.
	 * 
	 * @param min
	 * @return
	 */
	public Configuration<S, C> removeMin() {
		assert m_Min != null : "getMin() must have been called before removeMin()";
		assert !m_Min.isEmpty() : "The minimum of a configuration must not be empty.";
		HashSet<Event<S, C>> events = new HashSet<Event<S, C>>(m_Events);
		events.removeAll(m_Min);
		Set<Event<S, C>> min = Event.getSuccessorEvents(m_Min);
		min.retainAll(events);
		HashSet<Event<S, C>> newmin = new HashSet<Event<S, C>>();
		for (Event<S, C> e : min) {
			Set<Event<S, C>> predEventsOfE = e.getPredecessorEvents();
			predEventsOfE.retainAll(m_Events);
			if (m_Min.containsAll(predEventsOfE)) {
				newmin.add(e);
			}
		}
		Configuration<S, C> result = new Configuration<S, C>(events, newmin);
		return result;
	}

	@Override
	public boolean removeAll(Collection<?> arg0) {
		return m_Events.removeAll(arg0);
	}

	@Override
	public boolean retainAll(Collection<?> arg0) {
		return m_Events.retainAll(arg0);
	}

	@Override
	public Object[] toArray() {
		return m_Events.toArray();
	}

	@Override
	public <T> T[] toArray(T[] arg0) {
		return m_Events.toArray(arg0);
	}

	/**
	 * Compares configurations initially based on size. In case of equal size,
	 * lexically compares the ordered sequences of events with respect to the
	 * the total order on their transitions.
	 */
	@Override
	public int compareTo(Configuration<S, C> o) {
		if (size() != o.size())
			return size() - o.size();
		List<Transition<S, C>> phi1 = getPhi();
		List<Transition<S, C>> phi2 = o.getPhi();
		for (int i = 0; i < phi1.size(); i++) {
			Transition<S, C> t1 = phi1.get(i);
			Transition<S, C> t2 = phi2.get(i);
			int result = t1.getTotalOrderID() - t2.getTotalOrderID();
			if (result != 0) {
				s_Logger.debug(phi1.toString() + (result < 0 ? "<" : ">")
						+ phi2.toString());
				return result;
			}
		}
		assert (phi1.equals(phi2));
		return 0;
	}

	public boolean equals(Configuration<S, C> other) {
		return containsAll(other) && other.containsAll(this);
	}

	// @Override
	// public int hashCode() {
	// final int prime = 31;
	// int result = super.hashCode();
	// result = prime * result
	// + ((m_Events == null) ? 0 : m_Events.hashCode());
	// return result;
	// }
	//
	// @Override
	// public boolean equals(Object obj) {
	// if (this == obj)
	// return true;
	// if (!super.equals(obj))
	// return false;
	// if (getClass() != obj.getClass())
	// return false;
	// Configuration<S, C> other = (Configuration) obj;
	// if (m_Events == null) {
	// if (other.m_Events != null)
	// return false;
	// } else if (!m_Events.equals(other.m_Events))
	// return false;
	// return true;
	// }

}
