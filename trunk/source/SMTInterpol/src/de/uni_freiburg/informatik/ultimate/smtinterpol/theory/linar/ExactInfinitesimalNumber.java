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

public class ExactInfinitesimalNumber implements Comparable<ExactInfinitesimalNumber> {
	public final static ExactInfinitesimalNumber ZERO = new ExactInfinitesimalNumber(Rational.ZERO, Rational.ZERO);
	public final static ExactInfinitesimalNumber POSITIVE_INFINITY =
			new ExactInfinitesimalNumber(Rational.POSITIVE_INFINITY, Rational.ZERO);
	public final static ExactInfinitesimalNumber NEGATIVE_INFINITY =
			new ExactInfinitesimalNumber(Rational.NEGATIVE_INFINITY, Rational.ZERO);
	private final Rational mReal;
	private final Rational mEps;

	public ExactInfinitesimalNumber(final Rational real) {
		mReal = real;
		mEps = Rational.ZERO;
	}

	public ExactInfinitesimalNumber(final Rational real, final Rational eps) {
		mReal = real;
		mEps = eps;
	}

	public ExactInfinitesimalNumber(final InfinitesimalNumber approx) {
		mReal = approx.mReal;
		mEps = Rational.valueOf(approx.mEps, 1);
	}

	public Rational getRealValue() {
		return mReal;
	}

	public Rational getEpsilon() {
		return mEps;
	}

	@Override
	public String toString() {
		if (mEps.signum() == 0) {
			return mReal.toString();
		}
		if (mEps.signum() > 0) {
			return mReal.toString() + "+" + mEps.toString() + "eps";
		}
		return mReal.toString() + "-" + mEps.abs().toString() + "eps";
	}

	@Override
	public boolean equals(final Object o) {
		if (o instanceof InfinitesimalNumber) {
			final InfinitesimalNumber n = (InfinitesimalNumber) o;
			return mReal.equals(n.mReal) && mEps.equals(Rational.valueOf(n.mEps, 1));
		}
		if (o instanceof ExactInfinitesimalNumber) {
			final ExactInfinitesimalNumber n = (ExactInfinitesimalNumber) o;
			return mReal.equals(n.mReal) && mEps.equals(n.mEps);
		}
		return false;
	}

	@Override
	public int hashCode() {
		return mReal.hashCode() + 65537 * mEps.hashCode();
	}
	public ExactInfinitesimalNumber add(final Rational real) {
		return new ExactInfinitesimalNumber(mReal.add(real), mEps);
	}
	public ExactInfinitesimalNumber add(final InfinitesimalNumber other) {
		return new ExactInfinitesimalNumber(mReal.add(other.mReal),
				mEps.add(Rational.valueOf(other.mEps, 1)));
	}
	public ExactInfinitesimalNumber add(final ExactInfinitesimalNumber other) {
		return new ExactInfinitesimalNumber(mReal.add(other.mReal), mEps.add(other.mEps));
	}
	public ExactInfinitesimalNumber sub(final ExactInfinitesimalNumber other) {
		return new ExactInfinitesimalNumber(mReal.sub(other.mReal), mEps.sub(other.mEps));
	}
	/**
	 * Returns <code>first - this</code> but does not change <code>this</code>.
	 * @param first The first operand of the subtraction.
	 * @return Result of <code>first - this</code>.
	 */
	public ExactInfinitesimalNumber isub(final InfinitesimalNumber first) {
		return new ExactInfinitesimalNumber(first.mReal.sub(mReal),
				Rational.valueOf(first.mEps, 1).sub(mEps));
	}
	public ExactInfinitesimalNumber negate() {
		return new ExactInfinitesimalNumber(mReal.negate(), mEps.negate());
	}
	public ExactInfinitesimalNumber mul(final Rational c) {
		return new ExactInfinitesimalNumber(mReal.mul(c), mEps.mul(c));
	}
	public ExactInfinitesimalNumber div(final Rational d) {
		return new ExactInfinitesimalNumber(mReal.div(d), mEps.div(d));
	}

	/**
	 * Computes the absolute value.
	 *
	 * @return the absolute value of this.
	 */
	public ExactInfinitesimalNumber abs() {
		return signum() < 0 ? negate() : this;
	}

	public InfinitesimalNumber roundToInfinitesimal() {
		return new InfinitesimalNumber(mReal, mEps.signum());
	}

	public int compareTo(final InfinitesimalNumber other) {
		final int cmp = mReal.compareTo(other.mReal);
		return cmp == 0 ? mEps.compareTo(Rational.valueOf(other.mEps, 1)) : cmp;
	}

	@Override
	public int compareTo(final ExactInfinitesimalNumber other) {
		final int cmp = mReal.compareTo(other.mReal);
		return cmp == 0 ? mEps.compareTo(other.mEps) : cmp;
	}

	public int signum() {
		return mReal == Rational.ZERO ? mEps.signum() : mReal.signum();
	}
}
