/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.relation;

/**
 * Generic Quintuple that stores 5 different values.
 * 
 * @author Daniel Tischner
 *
 * @param <E1>
 *            Type of the first element
 * @param <E2>
 *            Type of the second element
 * @param <E3>
 *            Type of the third element
 * @param <E4>
 *            Type of the fourth element
 * @param <E5>
 *            Type of the fifth element
 */
public final class Quin<E1, E2, E3, E4, E5> {

	/**
	 * Fifth element of the tuple.
	 */
	private final E5 m_Fifth;
	/**
	 * First element of the tuple.
	 */
	private final E1 m_First;
	/**
	 * Fourth element of the tuple.
	 */
	private final E4 m_Fourth;
	/**
	 * Second element of the tuple.
	 */
	private final E2 m_Second;
	/**
	 * Third element of the tuple.
	 */
	private final E3 m_Third;

	/**
	 * Creates a new Quintuple with given elements.
	 * 
	 * @param first
	 *            First element of the tuple
	 * @param second
	 *            Second element of the tuple
	 * @param third
	 *            Third element of the tuple
	 * @param fourth
	 *            Fourth element of the tuple
	 * @param fifth
	 *            Fifth element of the tuple
	 */
	public Quin(final E1 first, final E2 second, final E3 third, final E4 fourth, final E5 fifth) {
		m_First = first;
		m_Second = second;
		m_Third = third;
		m_Fourth = fourth;
		m_Fifth = fifth;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof Quin)) {
			return false;
		}
		Quin<?, ?, ?, ?, ?> other = (Quin<?, ?, ?, ?, ?>) obj;
		if (m_Fifth == null) {
			if (other.m_Fifth != null) {
				return false;
			}
		} else if (!m_Fifth.equals(other.m_Fifth)) {
			return false;
		}
		if (m_First == null) {
			if (other.m_First != null) {
				return false;
			}
		} else if (!m_First.equals(other.m_First)) {
			return false;
		}
		if (m_Fourth == null) {
			if (other.m_Fourth != null) {
				return false;
			}
		} else if (!m_Fourth.equals(other.m_Fourth)) {
			return false;
		}
		if (m_Second == null) {
			if (other.m_Second != null) {
				return false;
			}
		} else if (!m_Second.equals(other.m_Second)) {
			return false;
		}
		if (m_Third == null) {
			if (other.m_Third != null) {
				return false;
			}
		} else if (!m_Third.equals(other.m_Third)) {
			return false;
		}
		return true;
	}

	/**
	 * Gets the fifth element of the tuple.
	 * 
	 * @return Fifth element of the tuple.
	 */
	public E5 getFifth() {
		return m_Fifth;
	}

	/**
	 * Gets the first element of the tuple.
	 * 
	 * @return First element of the tuple.
	 */
	public E1 getFirst() {
		return m_First;
	}

	/**
	 * Gets the fourth element of the tuple.
	 * 
	 * @return Fourth element of the tuple.
	 */
	public E4 getFourth() {
		return m_Fourth;
	}

	/**
	 * Gets the second element of the tuple.
	 * 
	 * @return Second element of the tuple.
	 */
	public E2 getSecond() {
		return m_Second;
	}

	/**
	 * Gets the third element of the tuple.
	 * 
	 * @return Third element of the tuple.
	 */
	public E3 getThird() {
		return m_Third;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((m_Fifth == null) ? 0 : m_Fifth.hashCode());
		result = prime * result + ((m_First == null) ? 0 : m_First.hashCode());
		result = prime * result + ((m_Fourth == null) ? 0 : m_Fourth.hashCode());
		result = prime * result + ((m_Second == null) ? 0 : m_Second.hashCode());
		result = prime * result + ((m_Third == null) ? 0 : m_Third.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "[" + m_First + ", " + m_Second + ", " + m_Third + ", " + m_Fourth + ", " + m_Fifth + "]";
	}

}
