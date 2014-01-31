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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class ExactInfinitNumber {
	private final Rational mReal;
	private final Rational mEps;
	public ExactInfinitNumber(Rational real, Rational eps) {
		mReal = real;
		mEps = eps;
	}
	public Rational getRealValue() {
		return mReal;
	}
	public Rational getEpsilon() {
		return mEps;
	}
	public String toString() {
		if (mEps.signum() == 0)
			return mReal.toString();
		if (mEps.signum() > 0)
			return mReal.toString() + "+" + mEps.toString() + "eps";
		return mReal.toString() + "-" + mEps.abs().toString() + "eps";
	}
	public boolean equals(Object o) {
		if (o instanceof ExactInfinitNumber) {
			ExactInfinitNumber n = (ExactInfinitNumber) o;
			return mReal.equals(n.mReal) && mEps.equals(n.mEps);
		}
		return false;
	}
	public int hashCode() {
		return mReal.hashCode() + 65537 * mEps.hashCode();
	}
}
