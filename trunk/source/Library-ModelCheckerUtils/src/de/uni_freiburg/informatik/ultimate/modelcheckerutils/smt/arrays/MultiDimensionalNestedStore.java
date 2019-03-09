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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

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

	public MultiDimensionalNestedStore(final Term array, final List<ArrayIndex> indices,
			final List<Term> values) {
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

	public MultiDimensionalStore getInnermost(final Script script) {
		return new MultiDimensionalStore(mArray, mIndices.get(0), mValues.get(0), script);
	}

	public static MultiDimensionalNestedStore convert(final Term term) {
		if (!term.getSort().isArraySort()) {
			throw new IllegalArgumentException("no array");
		}
//		final int dimension = new MultiDimensionalSort(term.getSort()).getDimension();
		final LinkedList<ArrayIndex> indices = new LinkedList<>();
		final LinkedList<Term> values = new LinkedList<>();
		Term currentArray = term;
		MultiDimensionalStore currentStore = MultiDimensionalStore.convert(term);
		if (currentStore == null) {
			return null;
		}
//		if (currentStore.getDimension() != dimension) {
//			return null;
////			throw new AssertionError("illegal dimension");
//		}
		final int firstSeenDimension = currentStore.getDimension();
		while (currentStore != null && (currentStore.getDimension() == firstSeenDimension)) {
			indices.addFirst(currentStore.getIndex());
			values.addFirst(currentStore.getValue());
			currentArray = currentStore.getArray();
			currentStore = MultiDimensionalStore.convert(currentArray);
		}
		return new MultiDimensionalNestedStore(currentArray, indices, values);
	}

}
