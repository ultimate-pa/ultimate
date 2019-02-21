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

import java.util.List;

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
	private final List<ArrayIndex> mValues;

	public MultiDimensionalNestedStore(final Term array, final List<ArrayIndex> indices,
			final List<ArrayIndex> values) {
		mArray = array;
		mIndices = indices;
		mValues = values;
	}

	public Term getArray() {
		return mArray;
	}

	public List<ArrayIndex> getIndices() {
		return mIndices;
	}

	public List<ArrayIndex> getValues() {
		return mValues;
	}

//	public Term toTerm(final Script script) {
//		Term array = mArray;
//		for (int i = 0; i < mIndices.size(); i++) {
//			array = SmtUtils.store(script, array, mIndices.get(i), mValues.get(i));
//		}
//		return array;
//	}

//	@Override
//	public String toString() {
//		String s = mArray.toString();
//		for (int i = 0; i < mIndices.size(); i++) {
//			s = String.format("(store %s %s %s)", s, mIndices.get(i), mValues.get(i));
//		}
//		return s;
//	}
//
//	public static MultiDimensionalNestedStore convert(final Term term) {
//		if (!term.getSort().isArraySort()) {
//			throw new IllegalArgumentException("no array");
//		}
//		final LinkedList<Term> indices = new LinkedList<>();
//		final LinkedList<Term> values = new LinkedList<>();
//		Term currentArray = term;
//		ArrayStore currentStore = ArrayStore.convert(term);
//		if (currentStore == null) {
//			return null;
//		}
//		while (currentStore != null) {
//			indices.addFirst(currentStore.getIndex());
//			values.addFirst(currentStore.getValue());
//			currentArray = currentStore.getArray();
//			currentStore = ArrayStore.convert(currentArray);
//		}
//		return new MultiDimensionalNestedStore(currentArray, indices, values);
//	}
}
