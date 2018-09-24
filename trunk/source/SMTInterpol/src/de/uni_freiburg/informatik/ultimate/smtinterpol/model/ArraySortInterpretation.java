/*
 * Copyright (C) 2014 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class ArraySortInterpretation implements SortInterpretation {
	
	private final SortInterpretation mIndexSort;
	private final SortInterpretation mValueSort;
	
	private final ArrayList<ArrayValue> mValues;
	private HashMap<ArrayValue, Integer> mUnifier;
	
	public ArraySortInterpretation(SortInterpretation index,
			SortInterpretation value) {
		mIndexSort = index;
		mValueSort = value;
		mValues = new ArrayList<ArrayValue>();
		mValues.add(0, ArrayValue.DEFAULT_ARRAY);
	}

	@Override
	public int ensureCapacity(int numValues) {
		while (mValues.size() < numValues) {
			extendFresh();
		}
		return mValues.size();
	}

	public int createEmptyArrayValue() {
		final int val = mValues.size();
		final ArrayValue fresh = new ArrayValue();
		mValues.add(val, fresh);
		return val;
	}

	@Override
	public int extendFresh() {
		final int val = mValues.size();
		final ArrayValue fresh = new ArrayValue();
		mValueSort.ensureCapacity(2);
		final int idxval = mIndexSort.extendFresh();
		final int old = fresh.store(idxval, 1);
		assert old == 1 : "Fresh index already used!";
		mValues.add(val, fresh);
		if (mUnifier != null) {
			mUnifier.put(fresh, val);
		}
		return val;
	}

	@Override
	public int size() {
		return mValues.size();
	}

	@Override
	public Term get(int idx, Sort s, Theory t) throws IndexOutOfBoundsException {
		if (idx < 0 || idx >= mValues.size()) {
			throw new IndexOutOfBoundsException();
		}
		return mValues.get(idx).toSMTLIB(s, t, mIndexSort, mValueSort);
	}

	@Override
	public Term toSMTLIB(Theory t, Sort sort) {
		// TODO Auto-generated method stub
		return null;
	}

	public ArrayValue getValue(int idx) {
		return mValues.get(idx);
	}

	public SortInterpretation getIndexInterpretation() {
		return mIndexSort;
	}
	
	public SortInterpretation getValueInterpretation() {
		return mValueSort;
	}
	
	public int value2index(ArrayValue value) {
		if (mUnifier == null) {
			mUnifier = new HashMap<ArrayValue, Integer>();
			for (int i = 0; i < mValues.size(); ++i) {
				final Integer prev = mUnifier.put(mValues.get(i), i);
				assert (prev == null) : "Same array values at different indices";
			}
		}
		final Integer res = mUnifier.get(value);
		if (res != null) {
			return res;
		}
		// Create a new element
		final int idx = mValues.size();
		mValues.add(idx, value);
		mUnifier.put(value, idx);
		return idx;
	}
	
}
