/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
 * Generic Triple.
 * 
 * @author Matthias Heizmann
 *
 */
public class Triple<E1, E2, E3> {

	private final E1 mFirstElement;
	private final E2 mSecondElement;
	private final E3 mThirdElement;

	public Triple(E1 first, E2 second, E3 third) {
		super();
		mFirstElement = first;
		mSecondElement = second;
		mThirdElement = third;
	}

	public E1 getFirst() {
		return mFirstElement;
	}

	public E2 getSecond() {
		return mSecondElement;
	}

	public E3 getThird() {
		return mThirdElement;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + mFirstElement.hashCode();
		result = prime * result + mSecondElement.hashCode();
		result = prime * result + mThirdElement.hashCode();
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
		final Triple other = (Triple) obj;
		if (mFirstElement == null) {
			if (other.mFirstElement != null) {
				return false;
			}
		} else if (!mFirstElement.equals(other.mFirstElement)) {
			return false;
		}
		if (mSecondElement == null) {
			if (other.mSecondElement != null) {
				return false;
			}
		} else if (!mSecondElement.equals(other.mSecondElement)) {
			return false;
		}
		if (mThirdElement == null) {
			if (other.mThirdElement != null) {
				return false;
			}
		} else if (!mThirdElement.equals(other.mThirdElement)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return "[" + mFirstElement + ", " + mSecondElement + ", " + mThirdElement + "]";
	}

}
