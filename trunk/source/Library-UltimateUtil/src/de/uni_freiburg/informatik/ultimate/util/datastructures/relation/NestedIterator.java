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
package de.uni_freiburg.informatik.ultimate.util.datastructures.relation;

import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.function.Function;

/**
 * Concatenate a sequence of Iterators. The iterators are provided by a given
 * Function whose range are the iterators and an iterator that iterates over
 * the functions domain.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 * @param IE
 *            element of inner iterator
 * @param OE
 *            element of outer iterator
 */
public class NestedIterator<IE, OE> implements Iterator<OE> {

	private final Iterator<IE> mInnerIterator;
	private IE mCurrentInnerElement;
	private Iterator<OE> mOuterIterator;
	private final Function<IE, Iterator<OE>> mNextOuterIteratorProvider;

	public NestedIterator(final Iterator<IE> innerIterator,
			final Function<IE, Iterator<OE>> nextOuterIteratorProvider) {
		mInnerIterator = innerIterator;
		mNextOuterIteratorProvider = nextOuterIteratorProvider;
		nextLetter();
	}

	private void nextLetter() {
		if (mInnerIterator.hasNext()) {
			do {
				mCurrentInnerElement = mInnerIterator.next();
				mOuterIterator = mNextOuterIteratorProvider.apply(mCurrentInnerElement); 
			} while (!mOuterIterator.hasNext() && mInnerIterator.hasNext());
			if (!mOuterIterator.hasNext()) {
				mCurrentInnerElement = null;
				mOuterIterator = null;
			}
		} else {
			mCurrentInnerElement = null;
			mOuterIterator = null;
		}
	}

	@Override
	public boolean hasNext() {
		return mCurrentInnerElement != null;
	}

	@Override
	public OE next() {
		if (mCurrentInnerElement == null) {
			throw new NoSuchElementException();
		}
		final OE result = mOuterIterator.next();
		if (!mOuterIterator.hasNext()) {
			nextLetter();
		}
		return result;
	}

}
