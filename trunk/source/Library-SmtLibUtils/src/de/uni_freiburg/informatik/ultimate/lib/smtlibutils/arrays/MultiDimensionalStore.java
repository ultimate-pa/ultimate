/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Data structure for a (possibly) nested array select expression.
 * In the array theory of SMT-LIB the Array sort has only two parameters one
 * for the index and one for the value.
 * We model multidimensional arrays by nesting arrays. E.g. an array with two
 * integer indices and real values has the following Sort.
 * (Array Int -> (Array Int -> Real))
 * The store function has the following signature.
 * (store (Array X Y) X Y (Array X Y))
 * Hence we have to use nested store expressions for multidimensional array
 * reads, e.g., in order to get the array that differs from array a only
 * because at index (i1,i2) the value of v was stored we use the following
 * expression.
 * (store a i1 (store (select a i1) i2 v))
 * This is data structure is a wrapper for such a nested select expression which
 * allows you to directly access the array, the indices and the value.

 * @author Matthias Heizmann
 */
public class MultiDimensionalStore implements ITermProvider {
	private final Term mArray;
	private final ArrayIndex mIndex;
	private final Term mValue;

	public MultiDimensionalStore(final Term array, final ArrayIndex index, final Term value) {
		super();
		if (index.isEmpty()) {
			throw new AssertionError("Zero dimensions are not supported");
		}
		assert MultiDimensionalSort.areDimensionsConsistent(array, index, value);
		mArray = array;
		mIndex = index;
		mValue = value;
	}

	private static boolean isStore(final Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName().equals("store");
		} else {
			return false;
		}
	}

	static boolean isCompatibleSelect(final Term term, final Term array, final List<Term> index) {
		if (index.isEmpty()) {
			return term == array;
		} else {
			final MultiDimensionalSelect mdSelect = MultiDimensionalSelect.of(term);
			if (mdSelect == null) {
				return false;
			} else {
				return mdSelect.getArray() == array && index.equals(mdSelect.getIndex());
			}
		}
	}

	public Term getArray() {
		return mArray;
	}

	public ArrayIndex getIndex() {
		return mIndex;
	}

	public Term getValue() {
		return mValue;
	}

	public int getDimension() {
		return getIndex().size();
	}

	@Override
	public Term toTerm(final Script script) {
		return SmtUtils.multiDimensionalStore(script, getArray(), getIndex(), getValue());
	}

	public static MultiDimensionalStore of(final Term term) {
		return of(term, Integer.MAX_VALUE);
	}

	private static MultiDimensionalStore of(final Term term, final int maxDimension) {
		final ArrayList<Term> index = new ArrayList<Term>();
		Term remainder = term;
		final Term array;
		if (isStore(term)) {
			array = ((ApplicationTerm) term).getParameters()[0];
			index.add(((ApplicationTerm) term).getParameters()[1]);
			remainder = ((ApplicationTerm) term).getParameters()[2];
			int dimension = 1;
			while (dimension < maxDimension && isStore(remainder)
					&& isCompatibleSelect(((ApplicationTerm) remainder).getParameters()[0], array, index)) {
				index.add(((ApplicationTerm) remainder).getParameters()[1]);
				remainder = ((ApplicationTerm) remainder).getParameters()[2];
				dimension ++;
			}
		} else {
			return null;
		}
		return new MultiDimensionalStore(array, new ArrayIndex(index), remainder);
	}

	public MultiDimensionalStore getOutermost(final Script script, final int k) {
		if (k <= 0) {
			throw new AssertionError("Must extract at least one dimension");
		}
		if (k >= getDimension()) {
			throw new AssertionError("Must not extract all dimensions");
		}
		final ArrayIndex lowerIndex = mIndex.getFirst(k);
		final ArrayIndex higherIndex = mIndex.getLast(mIndex.size() - k);
		final MultiDimensionalSelect selectInner = new MultiDimensionalSelect(mArray, lowerIndex);
		final MultiDimensionalStore updateInner = new MultiDimensionalStore(selectInner.toTerm(script), higherIndex,
				mValue);
		return new MultiDimensionalStore(mArray, lowerIndex, updateInner.toTerm(script));
	}

	@Override
	public String toString() {
		// not SMT-LIB syntax, but easier to read
		return String.format("(store %s %s %s)", mArray, mIndex, mValue);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mArray == null) ? 0 : mArray.hashCode());
		result = prime * result + ((mIndex == null) ? 0 : mIndex.hashCode());
		result = prime * result + ((mValue == null) ? 0 : mValue.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final MultiDimensionalStore other = (MultiDimensionalStore) obj;
		if (mArray == null) {
			if (other.mArray != null)
				return false;
		} else if (!mArray.equals(other.mArray))
			return false;
		if (mIndex == null) {
			if (other.mIndex != null)
				return false;
		} else if (!mIndex.equals(other.mIndex))
			return false;
		if (mValue == null) {
			if (other.mValue != null)
				return false;
		} else if (!mValue.equals(other.mValue))
			return false;
		return true;
	}

	/**
	 * Return all MultiDimensionalStore objects for all multidimensional
	 * store expressions that occur in term.
	 * If one multidimensional store occurs in another multidimensional
	 * store expression (e.g. as index) the nested one is not returned by
	 * this method.
	 * If a store term occurs multiple times it is contained multiple times
	 * in the result.
	 */
	public static List<MultiDimensionalStore> extractArrayStoresShallow(final Term term) {
		final List<MultiDimensionalStore> arrayStoreDefs = new ArrayList<MultiDimensionalStore>();
		final Set<ApplicationTerm> storeTerms = SmtUtils.extractApplicationTerms("store", term, true);
		for (final Term storeTerm : storeTerms) {
			final MultiDimensionalStore mdStore = MultiDimensionalStore.of(storeTerm);
			if (mdStore.getIndex().size() == 0) {
				throw new AssertionError("store must not have dimension 0");
			}
			arrayStoreDefs.add(mdStore);
		}
		return arrayStoreDefs;
	}


	/**
	 * Return all MultiDimensionalStore objects for all store expressions
	 * that occur in term. This method also return the inner multidimensional
	 * store expressions in other multidimensional store expressions.
	 * If a store term occurs multiple times it is contained multiple times
	 * in the result.
	 * If multidimensional stores are nested, the inner ones occur earlier
	 * in the resulting list.
	 */
	public static List<MultiDimensionalStore> extractArrayStoresDeep(final Term term) {
		final List<MultiDimensionalStore> result = new LinkedList<MultiDimensionalStore>();
		List<MultiDimensionalStore> foundInThisIteration = extractArrayStoresShallow(term);
		while (!foundInThisIteration.isEmpty()) {
			result.addAll(0, foundInThisIteration);
			final List<MultiDimensionalStore> foundInLastIteration = foundInThisIteration;
			foundInThisIteration = new ArrayList<MultiDimensionalStore>();
			for (final MultiDimensionalStore asd : foundInLastIteration) {
				foundInThisIteration.addAll(extractArrayStoresShallow(asd.getArray()));
				foundInThisIteration.addAll(extractArrayStoresShallow(asd.getValue()));
				final ArrayIndex index = asd.getIndex();
				for (final Term entry : index) {
					foundInThisIteration.addAll(extractArrayStoresShallow(entry));
				}
			}
		}
		return result;
	}

}
