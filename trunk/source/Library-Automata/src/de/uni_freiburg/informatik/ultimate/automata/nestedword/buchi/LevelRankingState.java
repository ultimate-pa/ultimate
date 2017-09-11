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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;

/**
 * Represents a state (S,O,g) in the complement automaton.
 * <ul>
 * <li>The level ranking g is modeled by mLevelRanking
 * <li>The set O is modeled by mO (set O contains all states of S that have not visited an odd state since the last time
 * O was emptied)
 * <li>The set S contains all DoubleDecker for which mLevelRanking is defined
 * </ul>
 * TODO Encode O in mLevelRanking. E.g. map DoubleDecker in O instead of its rank to rank-1000.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class LevelRankingState<LETTER, STATE> implements IFkvState<LETTER, STATE> {
	private static final String NOT_APPLICABLE = "not applicable";
	private static final int TWO = 2;
	private static final int THREE = 3;
	protected final Map<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> mLevelRanking;
	protected final Map<StateWithRankInfo<STATE>, Set<STATE>> mO;

	protected final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;

	/**
	 * Highest rank in this LevelRankingState. Only used to get statistics.
	 */
	protected int mHighestRank;

	LevelRankingState(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) {
		mLevelRanking = new HashMap<>();
		mO = new HashMap<>();
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

	final Map<StateWithRankInfo<STATE>, HashMap<STATE, Integer>>
			copyLevelRanking(final Map<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> levelRanking) {
		final Map<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> result = new HashMap<>();
		for (final Entry<StateWithRankInfo<STATE>, HashMap<STATE, Integer>> entry : levelRanking.entrySet()) {
			result.put(entry.getKey(), new HashMap<>(entry.getValue()));
		}
		return result;
	}

	final Map<StateWithRankInfo<STATE>, Set<STATE>>
			copyO(final Map<StateWithRankInfo<STATE>, Set<STATE>> levelRanking) {
		final Map<StateWithRankInfo<STATE>, Set<STATE>> result = new HashMap<>();
		for (final Entry<StateWithRankInfo<STATE>, Set<STATE>> entry : levelRanking.entrySet()) {
			result.put(entry.getKey(), new HashSet<>(entry.getValue()));
		}
		return result;
	}

	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Set<StateWithRankInfo<STATE>> getDownStates() {
		return mLevelRanking.keySet();
	}

	@Override
	public Iterable<StateWithRankInfo<STATE>> getUpStates(final StateWithRankInfo<STATE> downState) {
		final ArrayList<StateWithRankInfo<STATE>> result = new ArrayList<>();
		for (final STATE state : mLevelRanking.get(downState).keySet()) {
			final int rank = getRank(downState, state);
			final boolean inO = inO(downState, state);
			result.add(new StateWithRankInfo<>(state, rank, inO));
		}
		return result;
	}

	protected void addRank(final StateWithRankInfo<STATE> downState, final STATE upState, final Integer rank,
			final boolean addToO) {
		assert rank != null;
		assert isEven(rank) || !mOperand.isFinal(upState) : "final states must have even ranks";
		HashMap<STATE, Integer> up2rank = mLevelRanking.get(downState);
		if (up2rank == null) {
			up2rank = new HashMap<>();
			mLevelRanking.put(downState, up2rank);
		}
		assert !up2rank.containsKey(upState);
		up2rank.put(upState, rank);
		if (addToO) {
			assert isEven(getRank(downState, upState)) : "has to be even";
			addToO(downState, upState);
		}
		if (mHighestRank < rank) {
			mHighestRank = rank;
		}
	}

	protected void addToO(final StateWithRankInfo<STATE> downState, final STATE upState) {
		Set<STATE> upStates = mO.get(downState);
		if (upStates == null) {
			upStates = new HashSet<>();
			mO.put(downState, upStates);
		}
		upStates.add(upState);
	}

	/**
	 * @param downState
	 *            The down state.
	 * @param upState
	 *            up state
	 * @return the rank of the down/up state pair
	 */
	public Integer getRank(final StateWithRankInfo<STATE> downState, final STATE upState) {
		final HashMap<STATE, Integer> up2rank = mLevelRanking.get(downState);
		if (up2rank == null) {
			return null;
		}
		return up2rank.get(upState);
	}

	/**
	 * @param downState
	 *            The down state.
	 * @param upState
	 *            up state
	 * @return {@code true} iff the down/up state pair is in O
	 */
	public boolean inO(final StateWithRankInfo<STATE> downState, final STATE upState) {
		final Set<STATE> upStates = mO.get(downState);
		if (upStates == null) {
			return false;
		}
		return upStates.contains(upState);
	}

	boolean isOempty() {
		return mO.isEmpty();
	}

	@Override
	public String toString() {
		if (mLevelRanking == null) {
			return "NON_ACCEPTING_SINK";
		}
		return mLevelRanking.toString() + " O" + mO;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mLevelRanking == null) ? 0 : mLevelRanking.hashCode());
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
		final LevelRankingState<?, ?> other = (LevelRankingState<?, ?>) obj;
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
		assert mHighestRank < Integer.MAX_VALUE : NOT_APPLICABLE;
		final int[] ranks = new int[mHighestRank + 1];
		for (final StateWithRankInfo<STATE> downState : getDownStates()) {
			for (final StateWithRankInfo<STATE> upState : getUpStates(downState)) {
				ranks[upState.getRank()]++;
			}
		}
		return ranks;
	}

	boolean isTight() {
		assert mHighestRank >= 0;
		assert mHighestRank < Integer.MAX_VALUE : NOT_APPLICABLE;
		if (isEven(mHighestRank)) {
			return false;
		}
		final int[] ranks = constructRanksHistogram();
		for (int i = 1; i <= mHighestRank; i += TWO) {
			if (ranks[i] == 0) {
				return false;
			}
		}
		return true;
	}

	/**
	 * See Sven's STACS 2009 paper.
	 */
	boolean isMaximallyTight() {
		assert mHighestRank >= 0;
		assert mHighestRank < Integer.MAX_VALUE : NOT_APPLICABLE;
		if (isEven(mHighestRank)) {
			return false;
		}
		final int[] ranks = constructRanksHistogram();
		for (int i = 1; i < mHighestRank; i += TWO) {
			if (ranks[i] != 1) {
				return false;
			}
		}
		if (ranks[mHighestRank] == 0) {
			return false;
		}
		for (int i = 0; i < mHighestRank - 1; i += TWO) {
			if (ranks[i] != 0) {
				return false;
			}
		}
		return true;
	}

	boolean isElastic() {
		assert mHighestRank >= 0;
		assert mHighestRank < Integer.MAX_VALUE : NOT_APPLICABLE;
		if (isEven(mHighestRank)) {
			return false;
		}
		final int[] ranks = constructRanksHistogram();
		final int[] oddRanks = new int[ranks.length];
		for (int i = 1; i < ranks.length; i += TWO) {
			oddRanks[i] = ranks[i];
		}
		final int[] downwardAggregatedOddranks = oddRanks.clone();
		for (int i = ranks.length - THREE; i > 0; i -= TWO) {
			downwardAggregatedOddranks[i] += downwardAggregatedOddranks[i + TWO];
		}
		int requiredAmount = 1;
		for (int i = ranks.length - 1; i > 0; i -= TWO) {
			if (downwardAggregatedOddranks[i] < requiredAmount) {
				return false;
			}
			requiredAmount++;
		}
		return true;
	}

	/**
	 * @param number
	 *            A number.
	 * @return {@code true} iff the number is odd and nonnegative
	 */
	public static boolean isOdd(final int number) {
		if (number < 0) {
			throw new IllegalArgumentException();
		}
		return number % 2 != 0;
	}

	/**
	 * @param number
	 *            A number.
	 * @return {@code true} iff the number is even and nonnegative
	 */
	public static boolean isEven(final int number) {
		if (number < 0) {
			throw new IllegalArgumentException();
		}
		return number % 2 == 0;
	}

	public boolean isEmpty() {
		return mLevelRanking.isEmpty();
	}

	public boolean isNonAcceptingSink() {
		return mLevelRanking == null;
	}
	
	public boolean isLazyS(final Set<DoubleDecker<StateWithRankInfo<STATE>>> doubleDeckersEligibleForVoluntaryDecrease,
			final LevelRankingConstraintDrdCheck<LETTER, STATE> lrc) {
		if (isOempty()) {
			return true;
		} else {
			for (final DoubleDecker<StateWithRankInfo<STATE>> dd : doubleDeckersEligibleForVoluntaryDecrease) {
				if (isOdd(mLevelRanking.get(dd.getDown()).get(dd.getUp().getState()))
						&& !lrc.inO(dd.getDown(), dd.getUp().getState())) {
					return false;
				}
			}
		}
		return true;
	}
}
