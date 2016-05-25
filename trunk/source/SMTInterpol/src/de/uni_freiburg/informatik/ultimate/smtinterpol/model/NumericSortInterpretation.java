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

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class NumericSortInterpretation implements SortInterpretation {
	
	private final BidiMap<Rational> mValues = new BidiMap<Rational>();
	// Desired invariants:
	// mBiggest.isIntegral()
	// (\forall int i; 0<=i<mValues.size; mValues.get(i).compareTo(mBiggest) < 0)
	private Rational mBiggest = Rational.TWO;

	public NumericSortInterpretation() {
		mValues.add(0, Rational.ZERO);
		mValues.add(1, Rational.ONE);
	}
	
	@Override
	public Term toSMTLIB(Theory t, Sort sort) {
		throw new InternalError("Should never be called!");
	}

	public int extend(Rational rat) {
		if (mValues.containsVal(rat)) {
			return mValues.get(rat);
		}
		final int idx = mValues.size();
		mValues.add(idx, rat);
		if (rat.compareTo(mBiggest) >= 0) {
			mBiggest = rat.ceil().add(Rational.ONE);
		}
		return idx;
	}
	
	@Override
	public int extendFresh() {
		final int idx = mValues.size();
		mValues.add(idx, mBiggest);
		mBiggest = mBiggest.add(Rational.ONE);
		return idx;
	}

	@Override
	public String toString() {
		return mValues.toString();
	}

	@Override
	public int ensureCapacity(int numValues) {
		while (mValues.size() < numValues) {
			extendFresh();
		}
		return mValues.size();
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
		final Rational rat = mValues.get(idx);
		return rat.toTerm(s);
	}
	
	public Rational get(int idx) {
		return mValues.get(idx);
	}

}
