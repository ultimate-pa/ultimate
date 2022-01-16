/*
 * Copyright (C) 2022 Dennis Wölfing
 * Copyright (C) 2022 University of Freiburg
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

import java.util.ListIterator;

/**
 * An iterator that iterates in reversed order.
 *
 * @param <E>
 *            The type to iterate over.
 */
public class ReversedIterator<E> implements ListIterator<E> {
	private final ListIterator<E> mIter;

	/**
	 * Constructs a reversed iterator.
	 *
	 * @param iter
	 *            An existing iterator to be reversed.
	 */
	public ReversedIterator(final ListIterator<E> iter) {
		mIter = iter;
	}

	@Override
	public boolean hasNext() {
		return mIter.hasPrevious();
	}

	@Override
	public E next() {
		return mIter.previous();
	}

	@Override
	public void add(final E arg0) {
		throw new UnsupportedOperationException("ReversedIterator does not support modifying the list.");
	}

	@Override
	public boolean hasPrevious() {
		return mIter.hasNext();
	}

	@Override
	public int nextIndex() {
		return mIter.previousIndex();
	}

	@Override
	public E previous() {
		return mIter.next();
	}

	@Override
	public int previousIndex() {
		return mIter.nextIndex();
	}

	@Override
	public void remove() {
		throw new UnsupportedOperationException("ReversedIterator does not support modifying the list.");

	}

	@Override
	public void set(final E arg0) {
		throw new UnsupportedOperationException("ReversedIterator does not support modifying the list.");
	}
}
