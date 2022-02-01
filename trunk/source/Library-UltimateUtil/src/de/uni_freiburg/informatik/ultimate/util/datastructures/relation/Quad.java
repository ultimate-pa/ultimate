/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.util.datastructures.relation;

/**
 * Generic Quadruple.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class Quad<E1, E2, E3, E4> {
	private final E1 mFirst;
	private final E2 mSecond;
	private final E3 mThird;
	private final E4 mFourth;

	public Quad(final E1 first, final E2 second, final E3 third, final E4 fourth) {
		super();
		mFirst = first;
		mSecond = second;
		mThird = third;
		mFourth = fourth;
	}

	public E1 getFirst() {
		return mFirst;
	}

	public E2 getSecond() {
		return mSecond;
	}

	public E3 getThird() {
		return mThird;
	}

	public E4 getFourth() {
		return mFourth;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mFirst == null) ? 0 : mFirst.hashCode());
		result = prime * result + ((mFourth == null) ? 0 : mFourth.hashCode());
		result = prime * result + ((mSecond == null) ? 0 : mSecond.hashCode());
		result = prime * result + ((mThird == null) ? 0 : mThird.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final Quad<?, ?, ?, ?> other = (Quad<?, ?, ?, ?>) obj;
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
		if (mSecond == null) {
			if (other.mSecond != null) {
				return false;
			}
		} else if (!mSecond.equals(other.mSecond)) {
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

	@Override
	public String toString() {
		return "[" + mFirst + ", " + mSecond + ", " + mThird + ", " + mFourth + "]";
	}

}
