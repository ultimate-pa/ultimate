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
