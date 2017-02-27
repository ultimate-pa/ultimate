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