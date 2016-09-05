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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;

/**
 * Represents a state (S,O,g) in the complement automaton.
 * <ul>
 * <li>The level ranking g is modeled by mLevelRanking
 * <li>The set O is modeled by mO (set O contains all states of S that
 * have not visited an odd state since the last time O was emptied)
 * <li>The set S contains all DoubleDecker for which mLevelRanking is
 * defined
 * </ul>
 * TODO Encode O in mLevelRanking. E.g. map DoubleDecker in O instead of
 * its rank to rank-1000.
 * 
 * @author Matthias Heizmann
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class LevelRankingState<LETTER, STATE> implements IFkvState<LETTER, STATE> {
	protected final Map<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> mLevelRanking;
	protected final Map<StateWithRankInfo<STATE>, Set<STATE>> mO;
	
	protected final INestedWordAutomatonSimple<LETTER, STATE> mOperand;
	
	/**
	 * Highest rank in this LevelRankingState. Only used to get statistics.
	 */
	protected int mHighestRank;
	
	LevelRankingState(final INestedWordAutomatonSimple<LETTER, STATE> operand) {
		mLevelRanking = new HashMap<StateWithRankInfo<STATE>, HashMap<STATE, Integer>>();
		mO = new HashMap<StateWithRankInfo<STATE>, Set<STATE>>();
		mOperand = operand;
		mHighestRank = -1;
	}
	
	LevelRankingState(final LevelRankingState<LETTER, STATE> lrs) {
		mLevelRanking = copyLevelRanking(lrs.mLevelRanking);
		mO = copyO(lrs.mO);
		mHighestRank = lrs.mHighestRank;
		mOperand = lrs.getOperand();
	}
	
	/**
	 * Constructor for the non-accepting sink state.
	 */
	public LevelRankingState() {
		mLevelRanking = null;
		mO = null;
		mOperand = null;
	}
	
	Map<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> copyLevelRanking(
			final Map<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> lr) {
		final Map<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> result =
				new HashMap<StateWithRankInfo<STATE>, HashMap<STATE, Integer>>();
		for (final Entry<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> entry : lr.entrySet()) {
			result.put(entry.getKey(), new HashMap<STATE, Integer>(entry.getValue()));
		}
		return result;
	}
	
	Map<StateWithRankInfo<STATE>, Set<STATE>> copyO(final Map<StateWithRankInfo<STATE>, Set<STATE>> lr) {
		final Map<StateWithRankInfo<STATE>, Set<STATE>> result = new HashMap<StateWithRankInfo<STATE>, Set<STATE>>();
		for (final Entry<StateWithRankInfo<STATE>, Set<STATE>> entry : lr.entrySet()) {
			result.put(entry.getKey(), new HashSet<STATE>(entry.getValue()));
		}
		return result;
	}
	
	public INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}
	
	@Override
	public Set<StateWithRankInfo<STATE>> getDownStates() {
		return mLevelRanking.keySet();
	}
	
	@Override
	public Iterable<StateWithRankInfo<STATE>> getUpStates(final StateWithRankInfo<STATE> downState) {
		final ArrayList<StateWithRankInfo<STATE>> result = new ArrayList<StateWithRankInfo<STATE>>();
		for (final STATE state : mLevelRanking.get(downState).keySet()) {
			final int rank = getRank(downState, state);
			final boolean inO = inO(downState, state);
			result.add(new StateWithRankInfo<STATE>(state, rank, inO));
		}
		return result;
	}
	
	protected void addRank(final StateWithRankInfo<STATE> down, final STATE up, final Integer rank,
			final boolean addToO) {
		assert rank != null;
		assert isEven(rank) || !mOperand.isFinal(up) : "final states must have even ranks";
		HashMap<STATE, Integer> up2rank = mLevelRanking.get(down);
		if (up2rank == null) {
			up2rank = new HashMap<STATE, Integer>();
			mLevelRanking.put(down, up2rank);
		}
		assert !up2rank.containsKey(up);
		up2rank.put(up, rank);
		if (addToO) {
			assert isEven(getRank(down, up)) : "has to be even";
			addToO(down, up);
		}
		if (mHighestRank < rank) {
			mHighestRank = rank;
		}
	}
	
	protected void addToO(final StateWithRankInfo<STATE> down, final STATE up) {
		Set<STATE> upStates = mO.get(down);
		if (upStates == null) {
			upStates = new HashSet<STATE>();
			mO.put(down, upStates);
		}
		upStates.add(up);
	}
	
	public Integer getRank(final StateWithRankInfo<STATE> down, final STATE up) {
		final HashMap<STATE, Integer> up2rank = mLevelRanking.get(down);
		if (up2rank == null) {
			return null;
		} else {
			return up2rank.get(up);
		}
	}
	
	public boolean inO(final StateWithRankInfo<STATE> down, final STATE up) {
		final Set<STATE> upStates = mO.get(down);
		if (upStates == null) {
			return false;
		}
		return upStates.contains(up);
	}
	
	boolean isOempty() {
		return mO.isEmpty();
	}
	
	@Override
	public String toString() {
		if (mLevelRanking == null) {
			return "NON_ACCEPTING_SINK";
		} else {
			return mLevelRanking.toString() + " O" + mO;
		}
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
				+ ((mLevelRanking == null) ? 0 : mLevelRanking.hashCode());
		result = prime * result + ((mO == null) ? 0 : mO.hashCode());
		return result;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final LevelRankingState<LETTER, STATE> other = (LevelRankingState<LETTER, STATE>) obj;
		if (mLevelRanking == null) {
			if (other.mLevelRanking != null) {
				return false;
			}
		} else if (!mLevelRanking.equals(other.mLevelRanking)) {
			return false;
		}
		if (mO == null) {
			if (other.mO != null) {
				return false;
			}
		} else if (!mO.equals(other.mO)) {
			return false;
		}
		return true;
	}
	
	private int[] constructRanksHistogram() {
		assert mHighestRank >= 0;
		assert mHighestRank < Integer.MAX_VALUE : "not applicable";
		final int[] ranks = new int[mHighestRank + 1];
		for (final StateWithRankInfo<STATE> down : getDownStates()) {
			for (final StateWithRankInfo<STATE> up : getUpStates(down)) {
				ranks[up.getRank()]++;
			}
		}
		return ranks;
	}
	
	boolean isTight() {
		assert mHighestRank >= 0;
		assert mHighestRank < Integer.MAX_VALUE : "not applicable";
		if (isEven(mHighestRank)) {
			return false;
		} else {
			final int[] ranks = constructRanksHistogram();
			for (int i = 1; i <= mHighestRank; i += 2) {
				if (ranks[i] == 0) {
					return false;
				}
			}
			return true;
		}
	}
	
	/**
	 * See Sven's STACS 2009 paper.
	 */
	boolean isMaximallyTight() {
		assert mHighestRank >= 0;
		assert mHighestRank < Integer.MAX_VALUE : "not applicable";
		if (isEven(mHighestRank)) {
			return false;
		} else {
			final int[] ranks = constructRanksHistogram();
			for (int i = 1; i < mHighestRank; i += 2) {
				if (ranks[i] != 1) {
					return false;
				}
			}
			if (ranks[mHighestRank] == 0) {
				return false;
			}
			for (int i = 0; i < mHighestRank - 1; i += 2) {
				if (ranks[i] != 0) {
					return false;
				}
			}
			
			return true;
		}
	}
	
	boolean isElastic() {
		assert mHighestRank >= 0;
		assert mHighestRank < Integer.MAX_VALUE : "not applicable";
		if (isEven(mHighestRank)) {
			return false;
		} else {
			final int[] ranks = constructRanksHistogram();
			final int[] oddRanks = new int[ranks.length];
			for (int i = 1; i < ranks.length; i += 2) {
				oddRanks[i] = ranks[i];
			}
			final int[] downwardAggregatedOddranks = oddRanks.clone();
			for (int i = ranks.length - 3; i > 0; i -= 2) {
				downwardAggregatedOddranks[i] += downwardAggregatedOddranks[i + 2];
			}
			int requiredAmount = 1;
			for (int i = ranks.length - 1; i > 0; i -= 2) {
				if (downwardAggregatedOddranks[i] < requiredAmount) {
					return false;
				}
				requiredAmount++;
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
	
	public static boolean isOdd(final int i) {
		if (i >= 0) {
			return i % 2 == 1;
		} else {
			throw new IllegalArgumentException();
		}
	}
	
	public static boolean isEven(final int i) {
		if (i >= 0) {
			return i % 2 == 0;
		} else {
			throw new IllegalArgumentException();
		}
	}
	
	public boolean isEmpty() {
		return mLevelRanking.isEmpty();
	}
	
	public boolean isNonAcceptingSink() {
		return mLevelRanking == null;
	}
}
