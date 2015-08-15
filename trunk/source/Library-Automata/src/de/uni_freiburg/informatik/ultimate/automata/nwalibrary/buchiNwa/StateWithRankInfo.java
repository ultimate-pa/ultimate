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
 * State together with an int and a boolean.
 * Such a triple is needed for rank-based complementations of Büchi automata.
 * There we assign a state a rank store if it is contained in a set O 
 * (O for odd: state never had an odd rank since the set O was emptied the 
 * last time).
 * The rank has to be nonnegative. A state can only be "in O" if the rank
 * is even.
 * We use this class in the complementation to store rank and "in O" 
 * information about down states.
 * States of the "subset component" do not yet have a rank. To accomodate for
 * this we use Integer.MIN_VALUE to store that a state does not have a rank.
 * In the toString() representation we use the infinity symbol ∞ for states
 * that do not yet have a rank.
 * @author Matthias Heizmann
 */
public class StateWithRankInfo<STATE> {
	
	public static final int s_NoRank = Integer.MIN_VALUE;
	private final STATE m_State;
	private final int m_Rank;
	private final boolean m_InO;
	/**
	 * Constructor for states that have a rank.
	 */
	public StateWithRankInfo(STATE state, int rank, boolean inO) {
		super();
		m_State = state;
		if (rank < 0) {
			throw new IllegalArgumentException("rank has to be nonnegative");
		}
		m_Rank = rank;
//		if (inO && BuchiComplementFKVNwa.isOdd(rank)) {
//			throw new IllegalArgumentException("state can be only in O if rank is even");
//		}
		m_InO = inO;
	}

	/**
	 * Constructor for states that do not yet have a rank.
	 */
	public StateWithRankInfo(STATE state) {
		super();
		m_State = state;
		m_Rank = s_NoRank;
		m_InO = false;
	}
	
	public boolean hasRank() {
		return m_Rank != s_NoRank;
	}
	
	public STATE getState() {
		return m_State;
	}
	public int getRank() {
		return m_Rank;
	}
	public boolean isInO() {
		return m_InO;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (m_InO ? 1231 : 1237);
		result = prime * result + m_Rank;
		result = prime * result + ((m_State == null) ? 0 : m_State.hashCode());
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
		StateWithRankInfo other = (StateWithRankInfo) obj;
		if (m_InO != other.m_InO)
			return false;
		if (m_Rank != other.m_Rank)
			return false;
		if (m_State == null) {
			if (other.m_State != null)
				return false;
		} else if (!m_State.equals(other.m_State))
			return false;
		return true;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(getState());
		sb.append(",");
		if (hasRank()) {
			sb.append(getRank());
			if (isInO()) {
				sb.append("X");
			}
		} else {
			sb.append("∞");
		}
		sb.append(")");
		return sb.toString();
	}

	
	
	
}