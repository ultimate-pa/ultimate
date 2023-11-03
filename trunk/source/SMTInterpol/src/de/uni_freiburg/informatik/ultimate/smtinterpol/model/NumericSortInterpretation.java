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

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class NumericSortInterpretation implements SortInterpretation {

	// Desired invariants:
	// mBiggest.isIntegral()
	// (\forall int i; 0<=i<mValues.size; mValues.get(i).compareTo(mBiggest) < 0)
	private Rational mBiggest = Rational.TWO;

	public NumericSortInterpretation() {
	}

	@Override
	public Term toSMTLIB(final Theory t, final Sort sort) {
		throw new InternalError("Should never be called!");
	}

	@Override
	public void register(Term term) {
		// This must only be called with rational constants
		final Rational rat = (Rational) ((ConstantTerm) term).getValue();
		if (rat.compareTo(mBiggest) >= 0) {
			mBiggest = rat.floor().add(Rational.ONE);
		}
	}

	@Override
	public Term extendFresh(final Sort sort) {
		final Rational rat = mBiggest;
		mBiggest = mBiggest.add(Rational.ONE);
		return rat.toTerm(sort);
	}

	@Override
	public String toString() {
		return "numericSort[biggest=" + mBiggest + "]";
	}

	public static Rational toRational(final Term constTerm) {
		return ((Rational) ((ConstantTerm) constTerm).getValue());
	}

	@Override
	public Term getModelValue(final int idx, final Sort sort) {
		return Rational.valueOf(idx, 1).toTerm(sort);
	}
}
