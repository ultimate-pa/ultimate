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

import java.io.Serializable;
import java.util.Collection;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

public class Condition<S, C> implements Serializable {
	private static final long serialVersionUID = -497620137647502376L;

	static int s_SerialNumberCounter = 0;
	
	private final Event<S, C> m_Predecessor;
	private final Collection<Event<S, C>> m_Successors;
	private final Place<S, C> m_Place;
	
	private final int m_SerialNumber = s_SerialNumberCounter++;

	public Condition(Event<S, C> predecessor, Place<S, C> place) {
		this.m_Predecessor = predecessor;
		this.m_Successors = new HashSet<Event<S, C>>();
		this.m_Place = place;
	}

	public void addSuccesssor(Event<S, C> e) {
		m_Successors.add(e);
	}

	public Collection<Event<S, C>> getSuccessorEvents() {
		return m_Successors;
	}

	public Event<S, C> getPredecessorEvent() {
		return m_Predecessor;
	}

	public Place<S, C> getPlace() {
		return m_Place;
	}
	
	public String toString() {
		return "c" + m_SerialNumber +  ":CorrespPlace: " + m_Place.toString(); 
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + m_SerialNumber;
		return result;
	}
}
