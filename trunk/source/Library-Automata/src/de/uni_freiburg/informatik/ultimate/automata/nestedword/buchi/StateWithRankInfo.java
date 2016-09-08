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
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <STATE>
 *            state type
 */
public class StateWithRankInfo<STATE> {
	public static final int NO_RANK = Integer.MIN_VALUE;
	
	private final STATE mState;
	private final int mRank;
	private final boolean mInO;
	
	/**
	 * Constructor for states that have a rank.
	 * 
	 * @param state
	 *            state
	 * @param rank
	 *            rank
	 * @param inO
	 *            {@code true} iff the state is in O
	 */
	public StateWithRankInfo(final STATE state, final int rank, final boolean inO) {
		super();
		mState = state;
		if (rank < 0) {
			throw new IllegalArgumentException("rank has to be nonnegative");
		}
		mRank = rank;
//		if (inO && BuchiComplementFKVNwa.isOdd(rank)) {
//			throw new IllegalArgumentException("state can be only in O if rank is even");
//		}
		mInO = inO;
	}
	
	/**
	 * Constructor for states that do not yet have a rank.
	 * 
	 * @param state
	 *            state
	 */
	public StateWithRankInfo(final STATE state) {
		super();
		mState = state;
		mRank = NO_RANK;
		mInO = false;
	}
	
	/**
	 * @return {@code true} iff the rank is not the <tt>no rank</tt> value.
	 */
	public boolean hasRank() {
		return mRank != NO_RANK;
	}
	
	public STATE getState() {
		return mState;
	}
	
	public int getRank() {
		return mRank;
	}
	
	public boolean isInO() {
		return mInO;
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mInO ? 1231 : 1237);
		result = prime * result + mRank;
		result = prime * result + ((mState == null) ? 0 : mState.hashCode());
		return result;
	}
	
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
		final StateWithRankInfo<?> other = (StateWithRankInfo<?>) obj;
		if (mInO != other.mInO) {
			return false;
		}
		if (mRank != other.mRank) {
			return false;
		}
		if (mState == null) {
			if (other.mState != null) {
				return false;
			}
		} else if (!mState.equals(other.mState)) {
			return false;
		}
		return true;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
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
