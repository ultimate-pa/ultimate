package de.uni_freiburg.informatik.ultimate.util.datastructures.relation;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Set;


/***
 * DisjointSets data structure.
 *
 * TODO: can this class be deleted and UnionFind used instead??
 *
 * @author Mostafa M.A. <mostafa.amin93@gmail.com>
 *
 * @param <T> Elements of the sets
 */
public class DisjointSets<T> {
	// Representative element of the set of the element
	private final Map<T, T> mRepresentative;
	// The sets pointed by the representative
	private final Map<T, Set<T>> mSubsets;

	public DisjointSets(final Set<T> elements) {
		mRepresentative = new HashMap<>();
		mSubsets = new HashMap<>();
		// We begin with singleton disjoint sets
		for (final T x : elements) {
			mRepresentative.put(x, x);
			final Set<T> sub = new HashSet<>();
			sub.add(x);
			mSubsets.put(x, sub);
		}
	}

	/*
	public DisjointSets(final Set<T> elements_sets,...) {
		mRepresentative = new HashMap<>();
		mSubsets = new HashMap<>();
		// We begin with singleton disjoint sets
		for (final Set<T> s : elements_sets) {
			final T representative = s.iterator().next();
			for (final T x : s) {
				mRepresentative.put(x, representative);
			}
			final Set<T> sub = new HashSet<>();
			sub.addAll(s);
			mSubsets.put(representative, sub);
		}
	}
	*/

	@Override
	public String toString() {
		final StringBuilder res = new StringBuilder("Rep:");
		for (final Entry<T, T> s : mRepresentative.entrySet()) {
			res.append(" " + s.getKey() + "in" + s.getValue());
		}
		res.append("\nPart:");
		for (final Entry<T, Set<T>> s : mSubsets.entrySet()) {
			res.append(" " + s.getKey() + " in " + getPartition(s.getKey()));//s.getValue());
		}
		return res.toString();
	}

	/***
	 * The number of distinct disjoint sets
	 * @return
	 */
	public int size() {
		int siz = 0;
		for (final Set<T> subset : mSubsets.values()) {
			if (!subset.isEmpty()) {
				++siz;
			}
		}
		return siz;
	}

	private T changeRepresentative(final T x, final T rNew) {
		final T rOld = mRepresentative.get(x);
		if (rOld == rNew) {
			return rNew;
		}
		mRepresentative.put(x, rNew);
		if (mSubsets.containsKey(rOld)) {
			mSubsets.get(rOld).remove(x);
		}
		mSubsets.get(rNew).add(x);
		return rNew;
	}

	/***
	 * Union of the two disjoint sets.
	 * @param x
	 * @param y
	 */
	public void union(final T x, final T y) {
		changeRepresentative(find(y), find(x));
	}

	/***
	 * Find (and update) the representative of the corresponding disjoint set.
	 * @param x
	 * @return
	 */
	public T find(final T x) {
		final T res = mRepresentative.get(x);
		if (res == x) {
			return res;
		}
		return changeRepresentative(x, find(res));
	}

	/***
	 * Check if two elements are equivalent by checking if the disjoint sets are the same.
	 * @param x
	 * @param y
	 * @return
	 */
	public boolean equiv(final T x, final T y) {
		return find(x) == find(y);
	}

	public Set<T> getPartition(final T x) {
		return mSubsets.get(find(x));
	}

	private void findAll(final T x) {
		for (final T y : mSubsets.get(x)) {
			if (y != x) {
				findAll(y);
			}
		}
		find(x);
	}

	@Override
	public boolean equals(final Object set) {
		// TODO: Did you possibly want to override equals here? You did not, and I made that explicit by renaming
		// this method to equalsTo
		if (!(set instanceof DisjointSets)) {
			return false;
		} else {
			@SuppressWarnings("unchecked")
			final DisjointSets<T> other = (DisjointSets<T>) set;
			if (!other.mRepresentative.keySet().equals(mRepresentative.keySet())) {
				// Not same elements
				return false;
			}
			for (final T x : other.mRepresentative.keySet()) {
				// the partition of every element, is not the same partition in the other disjoint-set
				if (!other.mSubsets.get(other.mRepresentative.get(x)).equals(mSubsets.get(mRepresentative.get(x)))) {
					return false;
				}
			}
			return true;
		}
	}

	public Iterator<Set<T>> getParitionsIterator() {
		final Iterator<T> it = mSubsets.keySet().iterator();

		return new Iterator<Set<T>>() {
			T mCur = null;

			public boolean keepMoving() {
				if (!it.hasNext()) {
					mCur = null;
					return false;
				}
				do {
					mCur = it.next();
					findAll(mCur);
				} while (it.hasNext() && mSubsets.get(mCur).isEmpty());
				if (mSubsets.get(mCur).isEmpty()) {
					mCur = null;
					return false;
				}
				return true;
			}

			@Override
			public boolean hasNext() {
				if (mCur == null) {
					return keepMoving();
				}
				return true;
			}

			@Override
			public Set<T> next() {
				if (hasNext()) {
					final Set<T> res = mSubsets.get(mCur);
					keepMoving();
					return res;
				}
				throw new NoSuchElementException("No more elments to iterate.");
			}
		};
	}
}