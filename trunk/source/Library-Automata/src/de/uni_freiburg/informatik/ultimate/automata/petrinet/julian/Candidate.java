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

import java.util.ArrayList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

/**
 * represents an incomplete Event.
 * A <i>Candidate</i> consists of
 * <ul>
 * <li>the transition which belongs to the event</li>
 * <li>a subset of conditions of the set of predecessors of the event.</li>
 * <li>the set of predecessor-places of the transition minus the places that
 * correspond with the conditions in the given condition-set.</li>
 * </ul>
 **/
public class Candidate<S, C> {
	final public Transition<S, C> m_t;
	final public ArrayList<Condition<S, C>> m_Chosen;
	final public ArrayList<Place<S, C>> m_Places;
	
	public Candidate(
			Map.Entry<Transition<S, C>, Map<Place<S, C>, Condition<S, C>>> candidate) {
		this.m_t = candidate.getKey();
		this.m_Chosen = new ArrayList<Condition<S, C>>(candidate.getValue()
				.values());
		this.m_Places = new ArrayList<Place<S, C>>(candidate.getValue().keySet());
	}

	public Candidate(Transition<S, C> t2) {
		this.m_t = t2;
		this.m_Chosen = new ArrayList<Condition<S, C>>(m_t.getPredecessors().size());
		this.m_Places = new ArrayList<Place<S, C>>(m_t.getPredecessors());
	}


	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((m_Chosen == null) ? 0 : m_Chosen.hashCode());
		result = prime * result + ((m_Places == null) ? 0 : m_Places.hashCode());
		result = prime * result + ((m_t == null) ? 0 : m_t.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Candidate<?, ?> other = (Candidate<?, ?>) obj;
		if (m_Chosen == null) {
			if (other.m_Chosen != null)
				return false;
		} else if (!m_Chosen.equals(other.m_Chosen))
			return false;
		if (m_Places == null) {
			if (other.m_Places != null)
				return false;
		} else if (!m_Places.equals(other.m_Places))
			return false;
		if (m_t == null) {
			if (other.m_t != null)
				return false;
		} else if (!m_t.equals(other.m_t))
			return false;
		return true;
	}	
	
	
	
}