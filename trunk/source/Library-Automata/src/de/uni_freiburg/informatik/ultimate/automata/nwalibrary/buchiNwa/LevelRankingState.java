/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;

/**
 * Represents a state (S,O,g) in the complement automaton.
 * <ul>
 *   <li> The level ranking g is modeled by m_LevelRanking
 *   <li> The set O is modeled by m_O (set O contains all states of S that
 *   have not visited an odd state since the last time O was emptied)
 *   <li> The set S contains all DoubleDecker for which m_LevelRanking is
 *   defined 
 * </ul> 
 * TODO Encode O in m_LevelRanking. E.g. map DoubleDecker in O instead of
 * its rank to rank-1000.
 * @author Matthias Heizmann
 */
public class LevelRankingState<LETTER, STATE> implements IFkvState<LETTER, STATE> { 
	protected final Map<StateWithRankInfo<STATE>,HashMap<STATE,Integer>> m_LevelRanking;
	protected final Map<StateWithRankInfo<STATE>,Set<STATE>> m_O;
	
	protected final INestedWordAutomatonSimple<LETTER, STATE> m_Operand;
	
	/**
	 * Highest rank in this LevelRankingState. Only used to get statistics.
	 */
	int m_HighestRank;
	
	LevelRankingState(INestedWordAutomatonSimple<LETTER, STATE> operand) {
		m_LevelRanking = new HashMap<StateWithRankInfo<STATE>,HashMap<STATE,Integer>>();
		m_O = new HashMap<StateWithRankInfo<STATE>,Set<STATE>>();
		m_Operand = operand;
		m_HighestRank = -1;
	}
	
	LevelRankingState(LevelRankingState<LETTER, STATE> lrs) {
		m_LevelRanking = copyLevelRanking(lrs.m_LevelRanking);
		m_O = copyO(lrs.m_O);
		m_HighestRank = lrs.m_HighestRank;
		m_Operand = lrs.getOperand();
	}
	
	Map<StateWithRankInfo<STATE>,HashMap<STATE,Integer>> copyLevelRanking(Map<StateWithRankInfo<STATE>,HashMap<STATE,Integer>> lr) {
		Map<StateWithRankInfo<STATE>,HashMap<STATE,Integer>> result = new HashMap<StateWithRankInfo<STATE>,HashMap<STATE,Integer>>();
		for (Entry<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> entry  : lr.entrySet()) {
			result.put(entry.getKey(), new HashMap<STATE, Integer>(entry.getValue()));
		}
		return result;
	}
	
	Map<StateWithRankInfo<STATE>,Set<STATE>> copyO(Map<StateWithRankInfo<STATE>,Set<STATE>> lr) {
		Map<StateWithRankInfo<STATE>,Set<STATE>> result = new HashMap<StateWithRankInfo<STATE>,Set<STATE>>();
		for (Entry<StateWithRankInfo<STATE>, Set<STATE>> entry  : lr.entrySet()) {
			result.put(entry.getKey(), new HashSet<STATE>(entry.getValue()));
		}
		return result;
	}
	
	public INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return m_Operand;
	}
	
	
	public Set<StateWithRankInfo<STATE>> getDownStates() {
		return m_LevelRanking.keySet();
	}
	
	public Iterable<StateWithRankInfo<STATE>> getUpStates(StateWithRankInfo<STATE> downState) {
		ArrayList<StateWithRankInfo<STATE>> result = new ArrayList<StateWithRankInfo<STATE>>();
		for (STATE state : m_LevelRanking.get(downState).keySet()) {
			int rank = getRank(downState, state);
			boolean inO = inO(downState, state);
			result.add(new StateWithRankInfo<STATE>(state, rank, inO));
		}
		return result;
	}
	
	protected void addRank(StateWithRankInfo<STATE> down, STATE up, Integer rank, boolean addToO) {
		assert rank != null;
		assert isEven(rank) || !m_Operand.isFinal(up) : "final states must have even ranks";
		HashMap<STATE, Integer> up2rank = m_LevelRanking.get(down);
		if (up2rank == null) {
			up2rank = new HashMap<STATE,Integer>();
			m_LevelRanking.put(down, up2rank);
		}
		assert !up2rank.containsKey(up);
		up2rank.put(up,rank);
		if (addToO) {
			assert isEven(getRank(down, up)) : "has to be even";
			addToO(down,up);
		}
		if (m_HighestRank < rank) {
			m_HighestRank = rank;
		}
	}
	
	protected void addToO(StateWithRankInfo<STATE> down, STATE up) {
		Set<STATE> upStates = m_O.get(down);
		if (upStates == null) {
			upStates = new HashSet<STATE>();
			m_O.put(down, upStates);
		}
		upStates.add(up);
	}
	
	public Integer getRank(StateWithRankInfo<STATE> down, STATE up) {
		HashMap<STATE, Integer> up2rank = m_LevelRanking.get(down);
		if (up2rank == null) {
			return null;
		}
		else {
			return up2rank.get(up);
		}
	}
	
	public boolean inO(StateWithRankInfo<STATE> down, STATE up) {
		Set<STATE> upStates = m_O.get(down);
		if (upStates == null) {
			return false;
		}
		return upStates.contains(up);
	}
	
	boolean isOempty() {
		return m_O.isEmpty();
	}
	
	@Override
	public String toString() {
		return m_LevelRanking.toString() +" O"+m_O;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime
				* result
				+ ((m_LevelRanking == null) ? 0 : m_LevelRanking.hashCode());
		result = prime * result + ((m_O == null) ? 0 : m_O.hashCode());
		return result;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		LevelRankingState<LETTER, STATE> other = (LevelRankingState<LETTER, STATE>) obj;
		if (m_LevelRanking == null) {
			if (other.m_LevelRanking != null)
				return false;
		} else if (!m_LevelRanking.equals(other.m_LevelRanking))
			return false;
		if (m_O == null) {
			if (other.m_O != null)
				return false;
		} else if (!m_O.equals(other.m_O))
			return false;
		return true;
	}
	
	boolean isTight() {
		assert m_HighestRank >= 0;
		assert m_HighestRank < Integer.MAX_VALUE : "not applicable";
		if (isEven(m_HighestRank)) {
			return false;
		} else {
			int[] ranks = new int[m_HighestRank+1];
			for (StateWithRankInfo<STATE> down  : getDownStates()) {
				for (StateWithRankInfo<STATE> up : getUpStates(down)) {
					ranks[up.getRank()]++;
				}
			}
			for (int i=1; i<=m_HighestRank; i+=2) {
				if (ranks[i] == 0) {
					return false;
				}
			}
			return true;
		}
	}

//	@Override
//	public Set<STATE> getDownStates() {
//		throw new UnsupportedOperationException("need rank info");
//	}
//
//	@Override
//	public Set<STATE> getUpStates(STATE caller) {
//		throw new UnsupportedOperationException("need rank info");
//	}
	
	
	public static boolean isOdd(int i) {
		if (i >= 0) {
			return i % 2 == 1;
		} else {
			throw new IllegalArgumentException();
		}
	}
	
	public static boolean isEven(int i) {
		if (i >= 0) {
			return i % 2 == 0;
		} else {
			throw new IllegalArgumentException();
		}
	}

	public boolean isEmpty() {
		return m_LevelRanking.isEmpty();
	}
}
