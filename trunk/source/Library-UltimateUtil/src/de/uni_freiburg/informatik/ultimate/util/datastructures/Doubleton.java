/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.datastructures;


/**
 * We call a multiset of two elements a doubleton.
 * @author Matthias Heizmann
 *
 * @param <E>
 */
public class Doubleton<E> {
	private final E mOneElement;
	private final E mOtherElement;
	
	public Doubleton(final E oneElement, final E otherElement) {
		if (oneElement == null || otherElement == null) {
			throw new IllegalArgumentException();
		}
		mOneElement = oneElement;
		mOtherElement = otherElement;
	}
	
	public E getOneElement() {
		return mOneElement;
	}
	
	public E getOtherElement() {
		return mOtherElement;
	}
	
	public E[] toArray() {
		@SuppressWarnings("unchecked")
		final E[] result = (E[]) new Object[] { mOneElement, mOtherElement};
		return result;
	}
	
	@Override
	public int hashCode() {
		return mOneElement.hashCode() + mOtherElement.hashCode();
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
		@SuppressWarnings("unchecked")
		final Doubleton<E> other = (Doubleton<E>) obj;
		final boolean equalSameOrder = this.getOneElement().equals(other.getOneElement())
				&& this.getOtherElement().equals(other.getOtherElement());
		if (equalSameOrder) {
			return true;
		}
		final boolean equalSwappedOrder = this.getOneElement().equals(other.getOtherElement())
				&& this.getOtherElement().equals(other.getOneElement());
		return equalSwappedOrder;
	}
	
	@Override
	public String toString() {
		return "[" + mOneElement + ", " + mOtherElement + "]";
	}
}
