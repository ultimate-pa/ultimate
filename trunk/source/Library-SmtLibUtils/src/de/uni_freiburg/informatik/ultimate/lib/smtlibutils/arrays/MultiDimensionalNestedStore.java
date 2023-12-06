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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Data structure that represents a sequence of {@link MultiDimensionalStore}s
 * that are nested. I.e., if the array operand (first operand) of the
 * {@link MultiDimensionalStore} is itself a {@link MultiDimensionalStore} it is
 * explicitly represented by this data structure.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class MultiDimensionalNestedStore implements ITermProvider {
	private final Term mArray;
	private final List<ArrayIndex> mIndices;
	private final List<Term> mValues;

	public MultiDimensionalNestedStore(final Term array, final List<ArrayIndex> indices, final List<Term> values) {
		mArray = array;
		mIndices = indices;
		mValues = values;
	}

	public MultiDimensionalNestedStore(final MultiDimensionalStore mds) {
		mArray = mds.getArray();
		mIndices = Collections.singletonList(mds.getIndex());
		mValues = Collections.singletonList(mds.getValue());
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

	@Override
	public Term toTerm(final Script script) {
		Term array = mArray;
		for (int i = 0; i < mIndices.size(); i++) {
			array = SmtUtils.multiDimensionalStore(script, array, mIndices.get(i), mValues.get(i));
		}
		return array;
	}

	public MultiDimensionalStore getInnermost() {
		return new MultiDimensionalStore(mArray, mIndices.get(0), mValues.get(0));
	}

	/**
	 * Get a only a part of this {@link MultiDimensionalNestedStore}. This part is
	 * only a {@link MultiDimensionalStore} the array of the result is the array of
	 * the input. The index of the result is a restriction of the input's innermost
	 * store to its i-highest dimensions. The value of the result is what is written
	 * to the restricted input. <br />
	 * In the special case where the restriction to the i highest dimension
	 * coincides for all indices coincides, the output is only a different
	 * representation of the input.
	 *
	 * @param i Number of highest dimension that are extracted from the innermost
	 *          index.
	 */
	public MultiDimensionalStore extractDowngradeToHigherDimensions(final Script script, final int i) {
		assert (i >= 1 && i < getDimension());
		// take outer index and reduce to chosen dimension
		// new array is the outer array that we find a this reduced index
		final ArrayIndex reducedOuterIndex = mIndices.get(0).getFirst(i);
		final Term newArray = new MultiDimensionalSelect(mArray, reducedOuterIndex).toTerm(script);
		final List<ArrayIndex> newIndices = new ArrayList<>();
		for (final ArrayIndex ai : mIndices) {
			// if several of the nested stores indices coincide on the outer dimensions, the
			// result has several nested stores
			final ArrayIndex outer = ai.getFirst(i);
			if (outer.equals(reducedOuterIndex)) {
				final ArrayIndex inner = ai.getLast(getDimension() - i);
				newIndices.add(inner);
			} else {
				// if the first index is different the remaining corresponding stores are not
				// part of the result
				break;
			}
		}
		final List<Term> newValues = mValues.stream().limit(newIndices.size()).collect(Collectors.toList());
		final MultiDimensionalNestedStore innerMds = new MultiDimensionalNestedStore(newArray, newIndices, newValues);
		return new MultiDimensionalStore(mArray, reducedOuterIndex, innerMds.toTerm(script));
	}


	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mArray == null) ? 0 : mArray.hashCode());
		result = prime * result + ((mIndices == null) ? 0 : mIndices.hashCode());
		result = prime * result + ((mValues == null) ? 0 : mValues.hashCode());
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
		final MultiDimensionalNestedStore other = (MultiDimensionalNestedStore) obj;
		if (mArray == null) {
			if (other.mArray != null) {
				return false;
			}
		} else if (!mArray.equals(other.mArray)) {
			return false;
		}
		if (mIndices == null) {
			if (other.mIndices != null) {
				return false;
			}
		} else if (!mIndices.equals(other.mIndices)) {
			return false;
		}
		if (mValues == null) {
			if (other.mValues != null) {
				return false;
			}
		} else if (!mValues.equals(other.mValues)) {
			return false;
		}
		return true;
	}

	public static MultiDimensionalNestedStore of(final Term term) {
		MultiDimensionalNestedStore result = convert1mdseq(term);
		if (result == null) {
			return null;
		} else {
			Term innerArray = result.getArray();
			MultiDimensionalNestedStore innerArrayMds = convert1mdseq(innerArray);
			while (innerArrayMds != null) {
				if (innerArrayMds.getDimension() != result.getDimension()) {
					// incompatible dimensions, cannot concatenate both sequences
					return result;
				}
				innerArray = innerArrayMds.getArray();
				result = result.addInnerSequence(innerArrayMds);
				innerArrayMds = convert1mdseq(innerArray);
			}
		}
		return result;
	}

	/**
	 * Combine this {@link MultiDimensionalNestedStore} with innerArrayMdns such
	 * that the store operations of innerArrayMdns are first and the store
	 * operations this are applied afterwards.
	 */
	private MultiDimensionalNestedStore addInnerSequence(final MultiDimensionalNestedStore innerArrayMdns) {
		final List<ArrayIndex> indices = new ArrayList<>(innerArrayMdns.getIndices());
		indices.addAll(mIndices);
		final List<Term> values = new ArrayList<>(innerArrayMdns.getValues());
		values.addAll(mValues);
		final MultiDimensionalNestedStore result = new MultiDimensionalNestedStore(innerArrayMdns.getArray(), indices,
				values);
		return result;
	}

	private static MultiDimensionalNestedStore convert1mdseq(final Term term) {
		final ArrayStore as = ArrayStore.of(term);
		if (as == null) {
			return null;
		}
		final Term array = as.getArray();
		final List<Term> indexEntries = new ArrayList<>();
		indexEntries.add(as.getIndex());
		Term remainingValue = as.getValue();
		MultiDimensionalNestedStore remainingValueAsMdns = MultiDimensionalNestedStore.of(remainingValue);
		while (remainingValueAsMdns != null
				&& MultiDimensionalStore.isCompatibleSelect(remainingValueAsMdns.getArray(), array, indexEntries)) {
			if (remainingValueAsMdns.getDimension() == 1 && remainingValueAsMdns.getIndices().size() == 1) {
				assert remainingValueAsMdns.getIndices().size() == 1;
				assert remainingValueAsMdns.getIndices().get(0).size() == 1;
				indexEntries.add(remainingValueAsMdns.getIndices().get(0).get(0));
				remainingValue = remainingValueAsMdns.getValues().get(0);
				remainingValueAsMdns = MultiDimensionalNestedStore.of(remainingValue);
			} else {
				final MultiDimensionalNestedStore result = remainingValueAsMdns.addDimensionsAtBeginning(array,
						indexEntries, term);
				return result;
			}
		}
		final MultiDimensionalStore mds = new MultiDimensionalStore(array, new ArrayIndex(indexEntries), remainingValue);
		return new MultiDimensionalNestedStore(mds);
	}

	private MultiDimensionalNestedStore addDimensionsAtBeginning(final Term array, final List<Term> indexEntries,
			final Term term) {
		return new MultiDimensionalNestedStore(array, ArrayIndex.appendEntriesAtBeginning(mIndices, indexEntries),
				mValues);
	}

	public MultiDimensionalNestedStore removeOneIndex(final int i) {
		final List<ArrayIndex> newIndices = DataStructureUtils.copyAllButOne(mIndices, i);
		final List<Term> newValues = DataStructureUtils.copyAllButOne(mValues, i);
		return new MultiDimensionalNestedStore(mArray, newIndices, newValues);
	}

	/**
	 * Construct new {@link MultiDimensionalNestedStore} by applying a substitution
	 * to the array, all indices, and all values.
	 */
	public MultiDimensionalNestedStore applySubstitution(final ManagedScript mgdScript,
			final Map<? extends Term, ? extends Term> substitutionMapping) {
		final Term newArray = Substitution.apply(mgdScript, substitutionMapping, mArray);
		final List<ArrayIndex> newIndices = mIndices.stream()
				.map(x -> x.applySubstitution(mgdScript, substitutionMapping)).collect(Collectors.toList());
		final List<Term> newValues = mValues.stream().map(x -> Substitution.apply(mgdScript, substitutionMapping, x))
				.collect(Collectors.toList());
		return new MultiDimensionalNestedStore(newArray, newIndices, newValues);
	}

	@Override
	public String toString() {
		// not SMT-LIB syntax, but easier to read
		return String.format("(%s %s %s)", mArray, mIndices, mValues);
	}
}
