package de.uni_freiburg.informatik.ultimate.util.relation;

/**
 * Generic Triple. 
 * @author Matthias Heizmann
 *
 */
public class Pair<E1,E2> {
	
	private final E1 m_FirstElement;
	private final E2 m_SecondElement;
	
	public Pair(E1 first, E2 second) {
		super();
		m_FirstElement = first;
		m_SecondElement = second;
	}

	public E1 getFirst() {
		return m_FirstElement;
	}

	public E2 getSecond() {
		return m_SecondElement;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result	+ m_FirstElement.hashCode();
		result = prime * result	+ m_SecondElement.hashCode();
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
		Pair other = (Pair) obj;
		if (m_FirstElement == null) {
			if (other.m_FirstElement != null)
				return false;
		} else if (!m_FirstElement.equals(other.m_FirstElement))
			return false;
		if (m_SecondElement == null) {
			if (other.m_SecondElement != null)
				return false;
		} else if (!m_SecondElement.equals(other.m_SecondElement))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "[" + m_FirstElement	+ ", " + m_SecondElement + "]";
	}
	
	
	

}
