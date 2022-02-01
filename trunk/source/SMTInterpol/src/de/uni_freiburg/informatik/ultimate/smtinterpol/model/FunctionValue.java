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

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class FunctionValue {

	public static class Index {
		private final Term[] mIdx;
		private final int mHash;

		public Index(final Term[] idx) {
			mIdx = idx;
			mHash = Arrays.hashCode(mIdx);
		}

		@Override
		public int hashCode() {
			return mHash;
		}

		@Override
		public boolean equals(final Object o) {
			if (o instanceof Index) {
				return Arrays.equals(mIdx, ((Index) o).mIdx);
			}
			return false;
		}

		public Term[] toArray() {
			return mIdx;
		}

		@Override
		public String toString() {
			return Arrays.toString(mIdx);
		}
	}

	private Map<Index, Term> mValues;

	private Term mDefault;

	public FunctionValue() {
		mDefault = null;
	}

	public FunctionValue(final Term defaultValue) {
		mDefault = defaultValue;
	}

	public void put(final Term value, final Term... idx) {
		if (idx.length == 0) {
			assert mDefault == null;
			mDefault = value;
		} else {
			if (mValues == null) {
				mValues = new HashMap<>();
			}
			mValues.put(new Index(idx), value);
		}
	}

	public Term get(final Term[] idx) {
		if (mValues == null) {
			return mDefault;
		}
		final Term res = mValues.get(new Index(idx));
		return res == null ? mDefault : res;
	}

	public Term getDefault() {
		return mDefault;
	}

	public Map<Index, Term> values() {
		return mValues != null ? mValues : Collections.emptyMap();
	}
}
