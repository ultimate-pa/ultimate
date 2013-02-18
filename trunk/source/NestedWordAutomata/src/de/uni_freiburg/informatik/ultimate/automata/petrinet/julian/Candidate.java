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