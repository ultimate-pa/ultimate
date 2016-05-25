/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
/* SimpleSet Copyright (C) 1998-2002 Jochen Hoenicke.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; see the file COPYING.LESSER.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: SimpleSet.java 1367 2002-05-29 12:06:47Z hoenicke $
 */

package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;
import java.util.AbstractSet;
import java.util.Iterator;

public class SimpleSet<E> extends AbstractSet<E> implements Cloneable {
	E[] mElementObjects;
	int mCount = 0;

	public SimpleSet() {
		this(2);
	}

	@SuppressWarnings("unchecked")
	public SimpleSet(int initialSize) {
		mElementObjects = (E[]) new Object[initialSize];
	}

	@Override
	public int size() {
		return mCount;
	}

	@Override
	@SuppressWarnings("unchecked")
	public boolean add(E element) {
		if (element == null) {
			throw new NullPointerException();
		}

		for (int i = 0; i < mCount; i++) {
			if (element.equals(mElementObjects[i])) {
				return false;
			}
		}
		
		if (mCount == mElementObjects.length) {
			final E[] newArray = (E[]) new Object[(mCount + 1) * 2];
			System.arraycopy(mElementObjects,0,newArray,0,mCount);
			mElementObjects = newArray;
		}
		mElementObjects[mCount++] = element;
		return true;
	}
		
	@Override
	@SuppressWarnings("unchecked")
	public Object clone() {
		try {
			final SimpleSet<E> other = (SimpleSet<E>) super.clone();
			other.mElementObjects = mElementObjects.clone();
			return other;
		} catch (final CloneNotSupportedException ex) {
			throw new InternalError("Clone?");
		}
	}

	@Override
	public Iterator<E> iterator() {
		return new Iterator<E>() {
			int mPos = 0;

			@Override
			public boolean hasNext() {
				return mPos < mCount;
			}
			
			@Override
			public E next() {
				return mElementObjects[mPos++];
			}
		  
			@Override
			public void remove() {
				if (mPos < mCount) {
					System.arraycopy(mElementObjects, mPos, 
									 mElementObjects, mPos - 1, mCount - mPos);
				}
				mCount--;
				mPos--;
			}
		};
	}
}
