/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.ArrayDeque;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;

public class LATerm extends Term {
	public LATerm(InterpolatorAffineTerm s, InfinitNumber k, Term F) {
		super(F.hashCode());
		if (!s.isConstant()) {
			final Rational gcd = s.getGCD().abs();
			if (!gcd.equals(Rational.ONE)) {
				// normalize s-Term by dividing by gcd
				s.div(gcd);
				k = k.div(gcd);
				// if s is an integer term, round the constants accordingly
				if (s.isInt()) {
					// s <= 0 iff ceil(s) <= 0.
					final InfinitNumber c = s.getConstant();
					// ceil(s) = s - c + ceil(c) = s + cdiff
					final InfinitNumber cdiff = c.ceil().add(c.negate());
					s.add(cdiff);
					// -k <= s iff -k+cdiff <= s + cdiff
					//         iff ceil(-k+cdiff) <= s + cdiff
					// -ceil(-k+cdiff) = floor(k-cdiff)
					k = k.add(cdiff.negate()).floor();
				}
			}
		}
		mS = s;
		mK = k;
		mF = F;
	}
	
	InterpolatorAffineTerm mS;
	InfinitNumber mK;
	Term mF;
	
	@Override
	public Sort getSort() {
		return mF.getSort();
	}

	@Override
	public void toStringHelper(ArrayDeque<Object> mTodo) {
		mTodo.addLast(")");
		mTodo.addLast(mF);
		mTodo.addLast(", " + mK + ", ");
		mTodo.addLast(mS);
		mTodo.addLast("LA(");
	}
}
