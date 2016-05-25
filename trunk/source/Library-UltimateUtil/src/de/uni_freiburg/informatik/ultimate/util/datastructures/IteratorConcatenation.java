/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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

import java.util.Iterator;
import java.util.List;

/**
 * Returns an Iterator that is the sequential composition of a list of 
 * Iterators.
 * @author heizmann@informatik.uni-freiburg.de
 * 
 * @param <E> Type of elements over which we iterate.
 * 
 */
public class IteratorConcatenation<E> implements Iterator<E> {
	private final List<Iterator<E>> mIterators;
	private int mCurrent;
	private E mNext;
	

	public IteratorConcatenation(List<Iterator<E>> iterators) {
		super();
		mIterators = iterators;
		mCurrent = 0;
		if (mIterators.isEmpty()) {
			mNext = null;
		} else {
			mNext = getNext();
		}
	}


	private E getNext() {
		Iterator<E> currentIterator = mIterators.get(mCurrent);
		while (!currentIterator.hasNext() && mCurrent + 1 < mIterators.size()) {
			mCurrent++;
			currentIterator = mIterators.get(mCurrent);
		}
		if (currentIterator.hasNext()) {
			return currentIterator.next();
		} else {
			return null;
		}
	}


	@Override
	public boolean hasNext() {
		return mNext != null;
	}


	@Override
	public E next() {
		final E result = mNext;
		mNext = getNext();
		return result;
	}


	@Override
	public void remove() {
		throw new UnsupportedOperationException(
				"IteratorConcatenation is not modifiable");
	}

	
}
