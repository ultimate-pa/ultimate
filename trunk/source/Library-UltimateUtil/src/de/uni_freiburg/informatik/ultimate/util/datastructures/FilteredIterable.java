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

import de.uni_freiburg.informatik.ultimate.util.IPredicate;

/**
 * Filter a given Iterable. Iterator returns only elements on which a given
 * predicate evaluates to true.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <T> element type
 */
public class FilteredIterable<T> implements Iterable<T> {
	final Iterable<T> mIterable;
	final IPredicate<T> mPredicate;
	
	public FilteredIterable(final Iterable<T> iterable, final IPredicate<T> remainingElements) {
		mIterable = iterable;
		mPredicate = remainingElements;
	}
	
	@Override
	public Iterator<T> iterator() {
		return new PredicateIterator(mIterable);
	}
	
	private final class PredicateIterator implements Iterator<T> {
		final Iterator<T> mIterator;
		T mNext;
		
		public PredicateIterator(final Iterable<T> iterable) {
			mIterator = iterable.iterator();
			getNextThatSatisfiesPredicate();
		}
		
		private void getNextThatSatisfiesPredicate() {
			if (mIterator.hasNext()) {
				mNext = mIterator.next();
				while (mNext != null && !mPredicate.evaluate(mNext)) {
					if (mIterator.hasNext()) {
						mNext = mIterator.next();
					} else {
						mNext = null;
					}
				}
			} else {
				mNext = null;
			}
		}
		
		@Override
		public boolean hasNext() {
			return mNext != null;
		}
		
		@Override
		public T next() {
			final T result = mNext;
			getNextThatSatisfiesPredicate();
			return result;
		}
		
		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
	}
}
