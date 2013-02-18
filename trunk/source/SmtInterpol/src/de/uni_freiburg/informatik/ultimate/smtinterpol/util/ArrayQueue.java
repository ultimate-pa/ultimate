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
	private int front, size;
	private Object[] contents;
	
	public ArrayQueue(int size) {
		int i;
		for (i = 1; i < size; i+=i);
		contents = new Object[i];
		front = size = 0;
	}
	
	public ArrayQueue() {
		this(32);
	}
	
	private void resize() {
		assert (size == contents.length);
		Object[] oldcontents = contents;
		contents = new Object[2*size];
		System.arraycopy(oldcontents, front, contents, 0, size - front);
		System.arraycopy(oldcontents, 0, contents, size-front, front);
		front = 0;
	}

	@Override
	public boolean add(E e) {
		if (size == contents.length)
			resize();
		contents[(front+size++) & (contents.length - 1)] = e;
		return true;
	}

	@SuppressWarnings("unchecked")
	@Override
	public E element() {
		if (size == 0)
			throw new NoSuchElementException();
		return (E) contents[front];
	}

	@Override
	public boolean offer(E e) {
		return add(e);
	}

	@SuppressWarnings("unchecked")
	@Override
	public E peek() {
		return (E) contents[front];
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public E poll() {
		if (size == 0)
			return null;
		E elem = (E) contents[front];
		size--;
		contents[front++] = null;
		front &= contents.length-1;
		return elem;
	}

	@Override
	public E remove() {
		return poll();
	}

	@Override
	public void clear() {
		if (front + size > contents.length) {
			size -= contents.length - front;
			while (front < contents.length)
				contents[front++] = null;
			front = 0;
		}
		while (size > 0)
			contents[front + --size] = null;
	}

	@Override
	public Iterator<E> iterator() {
		return new Iterator<E>() {
			int ptr = front;
			public boolean hasNext() {
				return ptr < front+size;
			}
			@SuppressWarnings("unchecked")
			public E next() {
				return (E) contents[(ptr++) & (contents.length-1)];
			}
			public void remove() {
				/* remove from inside is not supported */
				throw new UnsupportedOperationException();
			}
		};
	}

	@Override
	public int size() {
		return size;
	}
}