/*
 * Copyright (C) 2015-2016 Daniel Tischner
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices;

/**
 * Container that holds a left and a right down state.
 * 
 * @author Daniel Tischner
 *
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class DownStateConfiguration<STATE> {

	/**
	 * Left down state of the configuration.
	 */
	private final STATE m_LeftDownState;
	/**
	 * Right down state of the configuration.
	 */
	private final STATE m_RightDownState;

	/**
	 * Creates a new down state configuration with two given down states.
	 * 
	 * @param leftDownState
	 *            Left down state of the configuration
	 * @param rightDownState
	 *            Right down state of the configuration
	 */
	public DownStateConfiguration(final STATE leftDownState, final STATE rightDownState) {
		m_LeftDownState = leftDownState;
		m_RightDownState = rightDownState;
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
		if (!(obj instanceof DownStateConfiguration)) {
			return false;
		}
		DownStateConfiguration<?> other = (DownStateConfiguration<?>) obj;
		if (m_LeftDownState == null) {
			if (other.m_LeftDownState != null) {
				return false;
			}
		} else if (!m_LeftDownState.equals(other.m_LeftDownState)) {
			return false;
		}
		if (m_RightDownState == null) {
			if (other.m_RightDownState != null) {
				return false;
			}
		} else if (!m_RightDownState.equals(other.m_RightDownState)) {
			return false;
		}
		return true;
	}

	/**
	 * Gets the left down state of the configuration.
	 * 
	 * @return The left down state
	 */
	public STATE getLeftDownState() {
		return m_LeftDownState;
	}

	/**
	 * Gets the right down state of the configuration.
	 * 
	 * @return The right down state
	 */
	public STATE getRightDownState() {
		return m_RightDownState;
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
		result = prime * result + ((m_LeftDownState == null) ? 0 : m_LeftDownState.hashCode());
		result = prime * result + ((m_RightDownState == null) ? 0 : m_RightDownState.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "[" + m_LeftDownState + "," + m_RightDownState + "]";
	}
}
