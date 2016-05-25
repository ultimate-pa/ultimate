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
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.util.AbstractCollection;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Queue;

public class ArrayQueue<E> extends AbstractCollection<E> implements Queue<E> {
	private int mFront, mSize;
	private Object[] mContents;
	
	public ArrayQueue(int size) {
		int i;
		for (i = 1; i < size; i += i) {
			;
		}
		mContents = new Object[i];
		mFront = size = 0;
	}
	
	public ArrayQueue() {
		this(32);
	}
	
	private void resize() {
		assert (mSize == mContents.length);
		final Object[] oldcontents = mContents;
		mContents = new Object[2 * mSize];
		System.arraycopy(oldcontents, mFront, mContents, 0, mSize - mFront);
		System.arraycopy(oldcontents, 0, mContents, mSize - mFront, mFront);
		mFront = 0;
	}

	@Override
	public boolean add(E e) {
		if (mSize == mContents.length) {
			resize();
		}
		mContents[(mFront + mSize++) & (mContents.length - 1)] = e;
		return true;
	}

	@SuppressWarnings("unchecked")
	@Override
	public E element() {
		if (mSize == 0) {
			throw new NoSuchElementException();
		}
		return (E) mContents[mFront];
	}

	@Override
	public boolean offer(E e) {
		return add(e);
	}

	@SuppressWarnings("unchecked")
	@Override
	public E peek() {
		return (E) mContents[mFront];
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public E poll() {
		if (mSize == 0) {
			return null;
		}
		final E elem = (E) mContents[mFront];
		mSize--;
		mContents[mFront++] = null;
		mFront &= mContents.length - 1;
		return elem;
	}

	@Override
	public E remove() {
		return poll();
	}

	@Override
	public void clear() {
		if (mFront + mSize > mContents.length) {
			mSize -= mContents.length - mFront;
			while (mFront < mContents.length) {
				mContents[mFront++] = null;
			}
			mFront = 0;
		}
		while (mSize > 0) {
			mContents[mFront + --mSize] = null;
		}
	}

	@Override
	public Iterator<E> iterator() {
		return new Iterator<E>() {
			int mPtr = mFront;
			@Override
			public boolean hasNext() {
				return mPtr < mFront + mSize;
			}
			@Override
			@SuppressWarnings("unchecked")
			public E next() {
				return (E) mContents[(mPtr++) & (mContents.length - 1)];
			}
			@Override
			public void remove() {
				/* remove from inside is not supported */
				throw new UnsupportedOperationException();
			}
		};
	}

	@Override
	public int size() {
		return mSize;
	}
}
