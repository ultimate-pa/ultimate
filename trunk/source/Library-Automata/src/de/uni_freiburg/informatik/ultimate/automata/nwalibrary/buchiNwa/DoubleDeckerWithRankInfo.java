/*
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;


/**
 * Variant of {@link DoubleDecker} for used in Büchi complementation.
 * @author Matthias Heizmann
 */
public class DoubleDeckerWithRankInfo<STATE> {
	private final StateWithRankInfo<STATE> m_Down;
	private final STATE m_Up;
	
	
	public DoubleDeckerWithRankInfo(StateWithRankInfo<STATE> down, STATE up) {
		super();
		m_Down = down;
		m_Up = up;
	}


	public StateWithRankInfo<STATE> getDown() {
		return m_Down;
	}


	public STATE getUp() {
		return m_Up;
	}


	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((m_Down == null) ? 0 : m_Down.hashCode());
		result = prime * result + ((m_Up == null) ? 0 : m_Up.hashCode());
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
		DoubleDeckerWithRankInfo other = (DoubleDeckerWithRankInfo) obj;
		if (m_Down == null) {
			if (other.m_Down != null)
				return false;
		} else if (!m_Down.equals(other.m_Down))
			return false;
		if (m_Up == null) {
			if (other.m_Up != null)
				return false;
		} else if (!m_Up.equals(other.m_Up))
			return false;
		return true;
	}


	@Override
	public String toString() {
		return "Down: " + m_Down + " Up:" + m_Up;
	}
	
	
	
}