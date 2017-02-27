/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

/**
 * Iterator for entries in the relation.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class MapOfSetIterator<D, R> implements Iterator<Map.Entry<D, R>> {
	private final Iterator<Entry<D, Set<R>>> mOuterIterator;
	private D mLhs;
	private Iterator<R> mRhsIterator;

	public MapOfSetIterator(final Map<D, Set<R>> map) {
		mOuterIterator = map.entrySet().iterator();
		nextLhs();
	}

	@Override
	public boolean hasNext() {
		while (!mRhsIterator.hasNext()) {
			nextLhs();
		}
		return mRhsIterator.hasNext();
	}

	@Override
	public Entry<D, R> next() {
		final D lhs = mLhs;
		final R rhs = mRhsIterator.next();
		return new Entry<D, R>() {
			@Override
			public D getKey() {
				return lhs;
			}

			@Override
			public R getValue() {
				return rhs;
			}

			@Override
			public R setValue(final R value) {
				throw new UnsupportedOperationException("setValue() is not allowed.");
			}

			@Override
			public String toString() {
				return lhs + "=" + rhs;
			}

			@Override
			public final int hashCode() {
				return lhs.hashCode() ^ Objects.hashCode(rhs);
			}

			@Override
			public final boolean equals(final Object other) {
				if (other == this) {
					return true;
				}
				if (!(other instanceof Map.Entry<?, ?>)) {
					return false;
				}
				final Map.Entry<?, ?> entry = (Map.Entry<?, ?>) other;
				return Objects.equals(lhs, entry.getKey()) && Objects.equals(rhs, entry.getValue());
			}
		};
	}

	private void nextLhs() {
		if (mOuterIterator.hasNext()) {
			final Entry<D, Set<R>> entry = mOuterIterator.next();
			mLhs = entry.getKey();
			mRhsIterator = entry.getValue().iterator();
		}
	}
}