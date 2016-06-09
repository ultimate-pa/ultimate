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
package de.uni_freiburg.informatik.ultimate.util.datastructures.relation;

/**
 * Generic Nonuple that stores 9 different values.
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
 * @param <E6>
 *            Type of the sixth element
 * @param <E7>
 *            Type of the seventh element
 * @param <E8>
 *            Type of the eighth element
 * @param <E9>
 *            Type of the ninth element
 */
public final class Non<E1, E2, E3, E4, E5, E6, E7, E8, E9> {

	/**
	 * Eighth element of the tuple.
	 */
	private final E8 mEighth;
	/**
	 * Fifth element of the tuple.
	 */
	private final E5 mFifth;
	/**
	 * First element of the tuple.
	 */
	private final E1 mFirst;
	/**
	 * Fourth element of the tuple.
	 */
	private final E4 mFourth;
	/**
	 * Ninth element of the tuple.
	 */
	private final E9 mNinth;
	/**
	 * Second element of the tuple.
	 */
	private final E2 mSecond;
	/**
	 * Seventh element of the tuple.
	 */
	private final E7 mSeventh;
	/**
	 * Sixth element of the tuple.
	 */
	private final E6 mSixth;
	/**
	 * Third element of the tuple.
	 */
	private final E3 mThird;

	/**
	 * Creates a new Ninuple with given elements.
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
	 * @param sixth
	 *            Sixth element of the tuple
	 * @param seventh
	 *            Seventh element of the tuple
	 * @param eighth
	 *            Eighth element of the tuple
	 * @param ninth
	 *            Ninth element of the tuple
	 */
	public Non(final E1 first, final E2 second, final E3 third, final E4 fourth, final E5 fifth, final E6 sixth,
			final E7 seventh, final E8 eighth, final E9 ninth) {
		mFirst = first;
		mSecond = second;
		mThird = third;
		mFourth = fourth;
		mFifth = fifth;
		mSixth = sixth;
		mSeventh = seventh;
		mEighth = eighth;
		mNinth = ninth;
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
		if (!(obj instanceof Non)) {
			return false;
		}
		Non<?, ?, ?, ?, ?, ?, ?, ?, ?> other = (Non<?, ?, ?, ?, ?, ?, ?, ?, ?>) obj;
		if (mEighth == null) {
			if (other.mEighth != null) {
				return false;
			}
		} else if (!mEighth.equals(other.mEighth)) {
			return false;
		}
		if (mFifth == null) {
			if (other.mFifth != null) {
				return false;
			}
		} else if (!mFifth.equals(other.mFifth)) {
			return false;
		}
		if (mFirst == null) {
			if (other.mFirst != null) {
				return false;
			}
		} else if (!mFirst.equals(other.mFirst)) {
			return false;
		}
		if (mFourth == null) {
			if (other.mFourth != null) {
				return false;
			}
		} else if (!mFourth.equals(other.mFourth)) {
			return false;
		}
		if (mNinth == null) {
			if (other.mNinth != null) {
				return false;
			}
		} else if (!mNinth.equals(other.mNinth)) {
			return false;
		}
		if (mSecond == null) {
			if (other.mSecond != null) {
				return false;
			}
		} else if (!mSecond.equals(other.mSecond)) {
			return false;
		}
		if (mSeventh == null) {
			if (other.mSeventh != null) {
				return false;
			}
		} else if (!mSeventh.equals(other.mSeventh)) {
			return false;
		}
		if (mSixth == null) {
			if (other.mSixth != null) {
				return false;
			}
		} else if (!mSixth.equals(other.mSixth)) {
			return false;
		}
		if (mThird == null) {
			if (other.mThird != null) {
				return false;
			}
		} else if (!mThird.equals(other.mThird)) {
			return false;
		}
		return true;
	}

	/**
	 * Gets the eighth element of the tuple.
	 * 
	 * @return Eighth element of the tuple.
	 */
	public E8 getEighth() {
		return mEighth;
	}

	/**
	 * Gets the fifth element of the tuple.
	 * 
	 * @return Fifth element of the tuple.
	 */
	public E5 getFifth() {
		return mFifth;
	}

	/**
	 * Gets the first element of the tuple.
	 * 
	 * @return First element of the tuple.
	 */
	public E1 getFirst() {
		return mFirst;
	}

	/**
	 * Gets the fourth element of the tuple.
	 * 
	 * @return Fourth element of the tuple.
	 */
	public E4 getFourth() {
		return mFourth;
	}

	/**
	 * Gets the ninth element of the tuple.
	 * 
	 * @return Ninth element of the tuple.
	 */
	public E9 getNinth() {
		return mNinth;
	}

	/**
	 * Gets the second element of the tuple.
	 * 
	 * @return Second element of the tuple.
	 */
	public E2 getSecond() {
		return mSecond;
	}

	/**
	 * Gets the seventh element of the tuple.
	 * 
	 * @return Seventh element of the tuple.
	 */
	public E7 getSeventh() {
		return mSeventh;
	}

	/**
	 * Gets the sixth element of the tuple.
	 * 
	 * @return Sixth element of the tuple.
	 */
	public E6 getSixth() {
		return mSixth;
	}

	/**
	 * Gets the third element of the tuple.
	 * 
	 * @return Third element of the tuple.
	 */
	public E3 getThird() {
		return mThird;
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
		result = prime * result + ((mEighth == null) ? 0 : mEighth.hashCode());
		result = prime * result + ((mFifth == null) ? 0 : mFifth.hashCode());
		result = prime * result + ((mFirst == null) ? 0 : mFirst.hashCode());
		result = prime * result + ((mFourth == null) ? 0 : mFourth.hashCode());
		result = prime * result + ((mNinth == null) ? 0 : mNinth.hashCode());
		result = prime * result + ((mSecond == null) ? 0 : mSecond.hashCode());
		result = prime * result + ((mSeventh == null) ? 0 : mSeventh.hashCode());
		result = prime * result + ((mSixth == null) ? 0 : mSixth.hashCode());
		result = prime * result + ((mThird == null) ? 0 : mThird.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "Non [mEighth=" + mEighth + ", mFifth=" + mFifth + ", mFirst=" + mFirst + ", mFourth=" + mFourth
				+ ", mSecond=" + mSecond + ", mSeventh=" + mSeventh + ", mSixth=" + mSixth + ", mThird=" + mThird
				+ ", mNinth=" + mNinth + "]";
	}
}
