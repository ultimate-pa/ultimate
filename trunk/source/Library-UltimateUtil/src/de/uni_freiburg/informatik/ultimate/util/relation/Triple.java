/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Util Library.
 * 
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Util Library grant you additional permission 
 * to convey the resulting work.
 */
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
