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

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

class FunctionValue {

	static class Index {
		private final int[] mIdx;
		private final int mHash;
		public Index(int[] idx) {
			mIdx = idx;
			mHash = Arrays.hashCode(mIdx);
		}
		public int hashCode() {
			return mHash;
		}
		public boolean equals(Object o) {
			if (o instanceof Index)
				return Arrays.equals(mIdx, ((Index) o).mIdx);
			return false;
		}
		public int[] getArray() {
			return mIdx;
		}
	}

	private Map<Index, Integer> mValues;
	
	private int mDefault;
	
	public FunctionValue() {
		this(0); // 0 is default for every sort
	}
	
	public FunctionValue(int idx) {
		mDefault = idx;
	}
	
	public void put(int value, int... idx) {
		if (idx.length == 0) {
			assert mDefault == 0;
			mDefault = value;
		} else {
			if (mValues == null)
				mValues = new HashMap<Index, Integer>();
			mValues.put(new Index(idx), value);
		}
	}
	
	public int get(int[] idx, boolean partial) {
		if (idx == null || idx.length == 0)
			return mDefault;
		if (mValues == null)
			return partial ? -1 : mDefault;
		Integer res = mValues.get(new Index(idx));
		return res == null ? partial ? -1 : mDefault : res.intValue();
	}

	public int getDefault() {
		return mDefault;
	}
	
	public Map<Index, Integer> values() {
		Map<Index, Integer> empty = Collections.emptyMap();
		return mValues == null ? empty : mValues;
	}
}
