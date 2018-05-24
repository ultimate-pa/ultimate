/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender;

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Extends an Iterable by an additional Object. The additional Object is only returned in the iteration sequence if it
 * occurs not already in the iteration sequence (comparison via reference not equals!).
 *
 * @author Matthias Heizmann
 *
 * @param <E>
 */
public class IterableWithAdditionalElement<E> implements Iterable<E> {

	private final Iterable<E> mIterable;
	private final E mAdditionalElement;

	public IterableWithAdditionalElement(final Iterable<E> iterable, final E additionalElement) {
		super();
		mIterable = iterable;
		mAdditionalElement = additionalElement;
	}

	@Override
	public Iterator<E> iterator() {

		return new Iterator<E>() {
			final Iterator<E> mIterator = mIterable.iterator();
			boolean mAdditionalElementSeen = false;
			boolean mAdditionalElementReturned = false;

			@Override
			public boolean hasNext() {
				if (mIterator.hasNext()) {
					return true;
				}
				if (mAdditionalElementSeen) {
					return false;
				}
				return !mAdditionalElementReturned;
			}

			@Override
			public E next() {
				if (mIterator.hasNext()) {
					final E next = mIterator.next();
					if (next == mAdditionalElement) {
						mAdditionalElementSeen = true;
					}
					return next;
				}
				if (mAdditionalElementSeen) {
					throw new NoSuchElementException();
				}
				if (mAdditionalElementReturned) {
					throw new NoSuchElementException();
				}
				mAdditionalElementReturned = true;
				return mAdditionalElement;
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}
		};
	}

}
