/*
 * Copyright (C) 2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

/**
 * Iterate efficiently over the intersection of two sets
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class IterableIntersection<E> implements Iterable<E> {

	private final Collection<E> mIteratedCollection;
	private final Set<E> mFilterSet;

	public IterableIntersection(final Set<E> set1, final Set<E> set2) {
		super();
		if (set1.size() <= set2.size()) {
			mIteratedCollection = set1;
			mFilterSet = set2;
		} else {
			mIteratedCollection = set2;
			mFilterSet = set1;
		}
	}

	@Override
	public Iterator<E> iterator() {
		return new Iterator<E>() {
			Iterator<E> mIt = mIteratedCollection.iterator();
			E mNext = preComputeNext();

			@Override
			public boolean hasNext() {
				return mNext != null;
			}

			private E preComputeNext() {
				E found = null;
				while (found == null && mIt.hasNext()) {
					final E next = mIt.next();
					if (mFilterSet.contains(next)) {
						found = next;
					}
				}
				return found;
			}

			@Override
			public E next() {
				final E result = mNext;
				mNext = preComputeNext();
				return result;
			}
		};
	}
}