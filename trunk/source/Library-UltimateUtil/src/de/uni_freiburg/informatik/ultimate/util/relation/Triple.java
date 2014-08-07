package de.uni_freiburg.informatik.ultimate.util.relation;

/**
 * Generic Triple. 
 * @author Matthias Heizmann
 *
 */
public class Triple<E1,E2,E3> {
	
	private final E1 m_FirstElement;
	private final E2 m_SecondElement;
	private final E3 m_ThirdElement;
	
	public Triple(E1 first, E2 second, E3 third) {
		super();
		m_FirstElement = first;
		m_SecondElement = second;
		m_ThirdElement = third;
	}

	public E1 getFirst() {
		return m_FirstElement;
	}

	public E2 getSecond() {
		return m_SecondElement;
	}

	public E3 getThird() {
		return m_ThirdElement;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result	+ m_FirstElement.hashCode();
		result = prime * result	+ m_SecondElement.hashCode();
		result = prime * result	+ m_ThirdElement.hashCode();
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
		Triple other = (Triple) obj;
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
		if (m_ThirdElement == null) {
			if (other.m_ThirdElement != null)
				return false;
		} else if (!m_ThirdElement.equals(other.m_ThirdElement))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return "[" + m_FirstElement	+ ", " + m_SecondElement + ", "
				+ m_ThirdElement + "]";
	}
	
	
	

}
