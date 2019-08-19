/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Data structure that represents a sequence of {@link MultiDimensionalStore}s
 * that are nested. I.e., if the array operand (first operand) of the
 * {@link MultiDimensionalStore} is itself a {@link MultiDimensionalStore} it is
 * explicitly represented by this data structure.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class MultiDimensionalNestedStore {
	private final Term mArray;
	private final List<ArrayIndex> mIndices;
	private final List<Term> mValues;
	private final Term mTerm;

	public MultiDimensionalNestedStore(final Script script, final Term array, final List<ArrayIndex> indices,
			final List<Term> values) {
		mArray = array;
		mIndices = indices;
		mValues = values;
		mTerm = toTerm(script, array, indices, values);
	}

	public MultiDimensionalNestedStore(final MultiDimensionalStore mds) {
		mArray = mds.getArray();
		mIndices = Collections.singletonList(mds.getIndex());
		mValues = Collections.singletonList(mds.getValue());
		mTerm = mds.getStoreTerm();
	}

	public Term getArray() {
		return mArray;
	}

	/**
	 * Innermost indices first.
	 */
	public List<ArrayIndex> getIndices() {
		return mIndices;
	}

	public List<Term> getValues() {
		return mValues;
	}

	public int getDimension() {
		return mIndices.get(0).size();
	}

	private static Term toTerm(final Script script, final Term array, final List<ArrayIndex> indices,
			final List<Term> values) {
		Term result = array;
		for (int i = 0; i < indices.size(); i++) {
			result = SmtUtils.multiDimensionalStore(script, result, indices.get(i), values.get(i));
		}
		return result;
	}


	public Term toTerm(final Script script) {
		Term array = mArray;
		for (int i = 0; i < mIndices.size(); i++) {
			array = SmtUtils.multiDimensionalStore(script, array, mIndices.get(i), mValues.get(i));
		}
		return array;
	}

//	@Override
//	public String toString() {
//		String s = mArray.toString();
//		for (int i = 0; i < mIndices.size(); i++) {
//			s = String.format("(store %s %s %s)", s, mIndices.get(i), mValues.get(i));
//		}
//		return s;
//	}

	public MultiDimensionalStore getInnermost(final int k) {
		if (k < 1) {
			throw new IllegalArgumentException("must extract at least one MultiDimensionalStore");
		}
		if (k > mIndices.size()) {
			throw new IllegalArgumentException("only " + mIndices.size() + " stores in sequence");
		}
		MultiDimensionalStore mds = MultiDimensionalStore.convert(mTerm);
		for (int i = 0; i < mIndices.size() - k; i++) {
			mds = MultiDimensionalStore.convert(mds.getArray());
		}
		assert mArray == mds.getArray();
		return mds;
	}

//	public static MultiDimensionalNestedStore convert(final Term term) {
//		if (!term.getSort().isArraySort()) {
//			throw new IllegalArgumentException("no array");
//		}
////		final int dimension = new MultiDimensionalSort(term.getSort()).getDimension();
//		final LinkedList<ArrayIndex> indices = new LinkedList<>();
//		final LinkedList<Term> values = new LinkedList<>();
//		Term currentArray = term;
//		MultiDimensionalStore currentStore = MultiDimensionalStore.convert(term);
//		if (currentStore == null) {
//			return null;
//		}
////		if (currentStore.getDimension() != dimension) {
////			return null;
//////			throw new AssertionError("illegal dimension");
////		}
//		final int firstSeenDimension = currentStore.getDimension();
//		while (currentStore != null && (currentStore.getDimension() == firstSeenDimension)) {
//			indices.addFirst(currentStore.getIndex());
//			values.addFirst(currentStore.getValue());
//			currentArray = currentStore.getArray();
//			currentStore = MultiDimensionalStore.convert(currentArray);
//		}
//		return new MultiDimensionalNestedStore(currentArray, indices, values);
//	}


	public static MultiDimensionalNestedStore convert(final Script script, final Term term) {
		MultiDimensionalNestedStore result = convert1mdseq(script, term);
		if (result == null) {
			return null;
		} else {
			Term innerArray = result.getArray();
			MultiDimensionalNestedStore innerArrayMds = convert1mdseq(script, innerArray);
			while (innerArrayMds != null) {
				innerArray = innerArrayMds.getArray();
				result = result.addInnerSequence(script, innerArrayMds);
				innerArrayMds = convert1mdseq(script, innerArray);
			}
		}
		return result;
	}


	/**
	 * Combine this {@link MultiDimensionalNestedStore} with innerArrayMdns such
	 * that the store operations of innerArrayMdns are first and the store
	 * operations this are applied afterwards.
	 */
	private MultiDimensionalNestedStore addInnerSequence(final Script script,
			final MultiDimensionalNestedStore innerArrayMdns) {
		final List<ArrayIndex> indices = new ArrayList<>(innerArrayMdns.getIndices());
		indices.addAll(mIndices);
		final List<Term> values = new ArrayList<>(innerArrayMdns.getValues());
		values.addAll(mValues);
		final MultiDimensionalNestedStore result = new MultiDimensionalNestedStore(script, innerArrayMdns.getArray(),
				indices, values);
		return result;
	}

	public static MultiDimensionalNestedStore convert1mdseq(final Script script, final Term term) {
		final ArrayStore as = ArrayStore.convert(term);
		if (as == null) {
			return null;
		}
		final Term array = as.getArray();
		final List<Term> indexEntries = new ArrayList<>();
		indexEntries.add(as.getIndex());
		Term remainingValue = as.getValue();
		MultiDimensionalNestedStore remainingValueAsMdns = MultiDimensionalNestedStore.convert(script, remainingValue);
		while (remainingValueAsMdns != null
				&& MultiDimensionalStore.isCompatibleSelect(remainingValueAsMdns.getArray(), array, indexEntries)) {
			if (remainingValueAsMdns.getDimension() == 1 && remainingValueAsMdns.getIndices().size() == 1) {
				assert remainingValueAsMdns.getIndices().size() == 1;
				assert remainingValueAsMdns.getIndices().get(0).size() == 1;
				indexEntries.add(remainingValueAsMdns.getIndices().get(0).get(0));
				remainingValue = remainingValueAsMdns.getValues().get(0);
				remainingValueAsMdns = MultiDimensionalNestedStore.convert(script, remainingValue);
			} else {
				final MultiDimensionalNestedStore result = remainingValueAsMdns.addDimensionsAtBeginning(script, array,
						indexEntries, term);
				return result;
			}
		}
		final MultiDimensionalStore mds = new MultiDimensionalStore(array, new ArrayIndex(indexEntries), remainingValue,
				term);
		return new MultiDimensionalNestedStore(mds);
	}

	private MultiDimensionalNestedStore addDimensionsAtBeginning(final Script script, final Term array,
			final List<Term> indexEntries, final Term term) {
		return new MultiDimensionalNestedStore(script, array,
				ArrayIndex.appendEntriesAtBeginning(mIndices, indexEntries), mValues);
	}

}
