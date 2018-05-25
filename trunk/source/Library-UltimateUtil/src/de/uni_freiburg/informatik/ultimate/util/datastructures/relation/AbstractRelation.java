/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.util.datastructures.relation;

import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;

/**
 * Object that represents a binary relation (i.e. a set of ordered pairs). Given an element of this relation (d,r)
 * <ul>
 * <li>we call the first entry d the domain element of relation, and
 * <li>we call the second entry r the range element of the relation.
 * </ul>
 * We use a Map from domain elements to sets of range elements to store this relation. Therefore we can directly get
 * <ul>
 * <li>the set of all domain elements and
 * <li>the set of all range elements for a given domain element.
 * </ul>
 * This is an abstract class that does not define which Map data structure is used.
 *
 * @author Matthias Heizmann
 * @param <D>
 *            Type of the elements that are in the domain of the relation.
 * @param <R>
 *            Type of the elements that are in the range of the relation.
 * @param <MAP>
 *            Type of Map that is used to store the relation.
 */
public abstract class AbstractRelation<D, R, MAP extends Map<D, Set<R>>> implements Iterable<Entry<D, R>> {
	private static final String NOT_YET_IMPLEMENTED = "not yet implemented";

	protected final MAP mMap;

	public AbstractRelation() {
		mMap = newMap();
	}

	public AbstractRelation(final AbstractRelation<D, R, ?> rel) {
		this();
		this.addAll(rel);
	}

	protected abstract MAP newMap();

	protected abstract Set<R> newSet();

	/**
	 * Add a pair (domainElem, rangeElem) to the relation.
	 *
	 * @return if this relation did not already contain the specified pair.
	 */
	public boolean addPair(final D domainElem, final R rangeElem) {
		Set<R> rangeElems = mMap.get(domainElem);
		if (rangeElems == null) {
			rangeElems = newSet();
			mMap.put(domainElem, rangeElems);
		}
		return rangeElems.add(rangeElem);
	}

	/**
	 * For each rangeElem in rangeElems, add a pair (domainElem, rangeElem) to the relation.
	 *
	 * @return if the relation has changed through this operation.
	 */
	public boolean addAllPairs(final D domainElem, final Collection<R> rangeElems) {
		Set<R> oldRangeElems = mMap.get(domainElem);
		if (oldRangeElems == null) {
			oldRangeElems = newSet();
			mMap.put(domainElem, oldRangeElems);
		}
		return oldRangeElems.addAll(rangeElems);
	}

	/**
	 * Remove the pair (domainElem, rangeElem) from the relation.
	 *
	 * @return true if the set contained the specified pair.
	 */
	public boolean removePair(final D domainElem, final R rangeElem) {
		final boolean result;
		final Set<R> rangeElems = mMap.get(domainElem);
		if (rangeElems == null) {
			result = false;
		} else {
			result = rangeElems.remove(rangeElem);
			if (rangeElems.isEmpty()) {
				mMap.remove(domainElem);
			}
		}
		return result;
	}

	/**
	 * Removes all pairs from the given relation from this relation.
	 * (i.e., subtracts the argument relation from this one)
	 *
	 * @param rel relation to subtract from this one
	 */
	public void removeAllPairs(final AbstractRelation<D, R, ?> rel) {
		for (final Entry<D, R> en : rel.entrySet()) {
			removePair(en.getKey(), en.getValue());
		}
	}

	/**
	 * Removes all pairs from this relation whose left entry equals the given key.
	 *
	 * @param left
	 */
	public Set<R> removeDomainElement(final D left) {
		final Set<R> result = mMap.remove(left);
		assert sanityCheck();
		return result;
	}

	/**
	 * Removes all pairs from this relation whose right entry equals the given key.
	 *
	 * @param elem
	 */
	public void removeRangeElement(final R elem) {
		final MAP mapCopy = newMap();
		mapCopy.putAll(mMap);
		for (final Entry<D, Set<R>> en : mapCopy.entrySet()) {
			en.getValue().remove(elem);
			if (en.getValue().isEmpty()) {
				mMap.remove(en.getKey());
			}
		}
		assert sanityCheck();
	}


	/**
	 * Replaces all occurrences of an element on the left hand side of a pair in this relation by some other element.
	 *
	 * @param element
	 * @param replacement
	 */
	public void replaceDomainElement(final D element, final D replacement) {
		assert replacement != null;
		final Set<R> image = mMap.get(element);

		if (image == null) {
			// relation has no pair where element is left entry -- nothing to do
			return;
		}

		for (final R rangeElement : image) {
			addPair(replacement, rangeElement);
		}
		removeDomainElement(element);
		assert sanityCheck();
	}

	/**
	 * Replaces all occurrences of an element on the right hand side of a pair in this relation by some other element.
	 *
	 * @param element
	 * @param replacement
	 */
	public void replaceRangeElement(final R element, final R replacement) {
		for (final Entry<D, Set<R>> en : mMap.entrySet()) {
			if (en.getValue().contains(element)) {
				en.getValue().remove(element);
				en.getValue().add(replacement);
			}
		}
		assert sanityCheck();
	}

	public void transformElements(final Function<D, D> dTransformer, final Function<R, R> rTransformer) {
		// TODO: would be nicer if we did not use HashRelation but something more generic for the copy
		for (final Entry<D, R> pair : new HashRelation<>(this)) {
			removePair(pair.getKey(), pair.getValue());
			addPair(dTransformer.apply(pair.getKey()), rTransformer.apply(pair.getValue()));
		}
	}

	/**
	 * Add all elements contained in relation rel to this relation. Does not reuse sets of the relation rel but
	 * constructs new sets if necessary.
	 */
	public void addAll(final AbstractRelation<D, R, ?> rel) {
		for (final Entry<D, Set<R>> entry : rel.mMap.entrySet()) {
			Set<R> rangeElems = mMap.get(entry.getKey());
			if (rangeElems == null) {
				rangeElems = newSet();
				mMap.put(entry.getKey(), rangeElems);
			}
			rangeElems.addAll(entry.getValue());
		}
	}

	/**
	 * @return true if the pair (domainElem, rangeElem) is contained in the relation.
	 */
	public boolean containsPair(final D domainElem, final R rangeElem) {
		final Set<R> rangeElems = mMap.get(domainElem);
		if (rangeElems == null) {
			return false;
		}
		return rangeElems.contains(rangeElem);
	}

	/**
	 * @return the set of all elements d such that for some r the pair (d,r) is in the relation.
	 */
	public Set<D> getDomain() {
		return mMap.keySet();
	}

	/**
	 * @return the set of all elements r such that for a the given element domainElem, the pair (domainElem, r) is in
	 *         the relation.
	 */
	public Set<R> getImage(final D domainElem) {
		final Set<R> set = mMap.get(domainElem);
		if (set == null) {
			return Collections.emptySet();
		}
		return Collections.unmodifiableSet(mMap.get(domainElem));
	}

	/**
	 * @return the number of all pairs contained in this relation.
	 */
	public int size() {
		int result = 0;
		for (final Entry<D, Set<R>> entry : mMap.entrySet()) {
			result += entry.getValue().size();
		}
		return result;
	}

	/**
	 * @return the number of pairs (d,r) such that the first entry d coincides with the parameter domainElem.
	 */
	public int numberOfPairsWithGivenDomainElement(final D domainElem) {
		if (getDomain().contains(domainElem)) {
			return getImage(domainElem).size();
		}
		return 0;
	}

	@Override
	public String toString() {
		return mMap.toString();
	}

	/**
	 * @return true iff there is no element in this relation.
	 */
	public boolean isEmpty() {
		return mMap.isEmpty();
	}

	@Override
	public Iterator<Entry<D, R>> iterator() {
		return new MapToCollectionIterator<>(mMap);
	}

	/**
	 * Remove all entries from this relation.
	 */
	public void clear() {
		mMap.clear();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mMap == null) ? 0 : mMap.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final AbstractRelation<?, ?, ?> other = (AbstractRelation<?, ?, ?>) obj;
		if (mMap == null) {
			if (other.mMap != null) {
				return false;
			}
		} else if (!mMap.equals(other.mMap)) {
			return false;
		}
		return true;
	}

	private boolean sanityCheck() {
		for (final Entry<D, Set<R>> en : this.mMap.entrySet()) {
			if (en.getKey() == null) {
				return false;
			}
			if (en.getValue() == null) {
				return false;
			}
			if (en.getValue().isEmpty()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Returns a Set view of the pairs contained in this relation. The set is backed by the relation, so changes to the
	 * map are reflected in the set, and vice-versa. TODO 2016-05-26 Matthias: This method was implemented accidentally
	 * and is not yet used and was not testet. Remove this warning once this method was tested.
	 *
	 * @return a set view of the pairs contained in this relation
	 */
	public Set<Map.Entry<D, R>> entrySet() {
		return new Set<Map.Entry<D, R>>() {

			@Override
			public boolean add(final Entry<D, R> arg0) {
				return addPair(arg0.getKey(), arg0.getValue());
			}

			@Override
			public boolean addAll(final Collection<? extends Entry<D, R>> arg0) {
				throw new UnsupportedOperationException(NOT_YET_IMPLEMENTED);
			}

			@Override
			public void clear() {
				throw new UnsupportedOperationException(NOT_YET_IMPLEMENTED);
			}

			@SuppressWarnings("unchecked")
			@Override
			public boolean contains(final Object arg0) {
				if (arg0 instanceof Map.Entry) {
					final Map.Entry<D, R> entry = (Entry<D, R>) arg0;
					return containsPair(entry.getKey(), entry.getValue());
				}
				return false;
			}

			@Override
			public boolean containsAll(final Collection<?> arg0) {
				throw new UnsupportedOperationException(NOT_YET_IMPLEMENTED);
			}

			@Override
			public boolean isEmpty() {
				return mMap.isEmpty();
			}

			@Override
			public Iterator<Entry<D, R>> iterator() {
				return new Iterator<Map.Entry<D, R>>() {
					private Entry<D, R> mNextEntry;
					private Iterator<Entry<D, Set<R>>> mOuterIterator;
					private Iterator<R> mInnerIterator;
					private Entry<D, Set<R>> mNextOuter;

					{
						mOuterIterator = mMap.entrySet().iterator();
						mNextEntry = constructNext();
					}

					private Entry<D, R> constructNext() {
						if (mInnerIterator == null || !mInnerIterator.hasNext()) {
							if (mOuterIterator.hasNext()) {
								mNextOuter = mOuterIterator.next();
								mInnerIterator = mNextOuter.getValue().iterator();
							} else {
								mInnerIterator = null;
							}
						}
						if (mInnerIterator != null) {
							assert mInnerIterator.hasNext();
							final R next = mInnerIterator.next();
							return new Entry<D, R>() {
								private final D mKey;
								private final R mValue;
								{
									mKey = mNextOuter.getKey();
									mValue = next;
								}

								@Override
								public D getKey() {
									return mKey;
								}

								@Override
								public R getValue() {
									return mValue;
								}

								@Override
								public R setValue(final R arg0) {
									throw new UnsupportedOperationException(NOT_YET_IMPLEMENTED);
								}
							};
						}
						return null;

					}

					@Override
					public boolean hasNext() {
						return mNextEntry != null;
					}

					@Override
					public Entry<D, R> next() {
						final Entry<D, R> result = mNextEntry;
						mNextEntry = constructNext();
						return result;
					}
				};
			}

			@SuppressWarnings("unchecked")
			@Override
			public boolean remove(final Object arg0) {
				if (arg0 instanceof Map.Entry) {
					final Map.Entry<D, R> entry = (Entry<D, R>) arg0;
					return removePair(entry.getKey(), entry.getValue());
				}
				return false;
			}

			@Override
			public boolean removeAll(final Collection<?> arg0) {
				throw new UnsupportedOperationException(NOT_YET_IMPLEMENTED);
			}

			@Override
			public boolean retainAll(final Collection<?> arg0) {
				throw new UnsupportedOperationException(NOT_YET_IMPLEMENTED);
			}

			@Override
			public int size() {
				return AbstractRelation.this.size();
			}

			@Override
			public Object[] toArray() {
				throw new UnsupportedOperationException(NOT_YET_IMPLEMENTED);
			}

			@Override
			public <T> T[] toArray(final T[] a) {
				throw new UnsupportedOperationException(NOT_YET_IMPLEMENTED);
			}

		};
	}
}
