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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;

public class SharedTermEvaluator {
	private final LinArSolve mLa;
	public SharedTermEvaluator(final LinArSolve la) {
		mLa = la;
	}
	public Rational evaluate(final SharedTerm st, final Theory t) {
		if (st.validShared()) {
			if (st.getLinVar() == null) {
				/* This can only happen if st.getTerm() is a numeric constant term */
				return (Rational) ((ConstantTerm) st.getTerm()).getValue();
			}
			final Rational val = st.getFactor().mul(mLa.realValue(st.getLinVar())).
				add(st.getOffset());
			return val;
		}
		throw new InternalError("Not a valid shared term: " + st.getTerm());
	}
}
