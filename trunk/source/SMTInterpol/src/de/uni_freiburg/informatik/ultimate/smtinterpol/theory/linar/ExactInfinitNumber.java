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

public class ExactInfinitNumber implements Comparable<ExactInfinitNumber> {
	public final static ExactInfinitNumber POSITIVE_INFINITY =
			new ExactInfinitNumber(Rational.POSITIVE_INFINITY, Rational.ZERO);
	public final static ExactInfinitNumber NEGATIVE_INFINITY =
			new ExactInfinitNumber(Rational.NEGATIVE_INFINITY, Rational.ZERO);
	private final Rational mReal;
	private final Rational mEps;
	public ExactInfinitNumber() {
		mReal = mEps = Rational.ZERO;
	}
	public ExactInfinitNumber(Rational real) {
		mReal = real;
		mEps = Rational.ZERO;
	}
	public ExactInfinitNumber(Rational real, Rational eps) {
		mReal = real;
		mEps = eps;
	}
	public ExactInfinitNumber(InfinitNumber approx) {
		mReal = approx.mA;
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
	public boolean equals(Object o) {
		if (o instanceof ExactInfinitNumber) {
			final ExactInfinitNumber n = (ExactInfinitNumber) o;
			return mReal.equals(n.mReal) && mEps.equals(n.mEps);
		}
		return false;
	}
	@Override
	public int hashCode() {
		return mReal.hashCode() + 65537 * mEps.hashCode();
	}
	public ExactInfinitNumber add(Rational real) {
		return new ExactInfinitNumber(mReal.add(real), mEps);
	}
	public ExactInfinitNumber add(InfinitNumber other) {
		return new ExactInfinitNumber(mReal.add(other.mA),
				mEps.add(Rational.valueOf(other.mEps, 1)));
	}
	public ExactInfinitNumber add(ExactInfinitNumber other) {
		return new ExactInfinitNumber(mReal.add(other.mReal), mEps.add(other.mEps));
	}
	public ExactInfinitNumber sub(ExactInfinitNumber other) {
		return new ExactInfinitNumber(mReal.sub(other.mReal), mEps.sub(other.mEps));
	}
	/**
	 * Returns <code>first - this</code> but does not change <code>this</code>.
	 * @param first The first operand of the subtraction.
	 * @return Result of <code>first - this</code>.
	 */
	public ExactInfinitNumber isub(InfinitNumber first) {
		return new ExactInfinitNumber(first.mA.sub(mReal),
				Rational.valueOf(first.mEps, 1).sub(mEps));
	}
	public ExactInfinitNumber negate() {
		return new ExactInfinitNumber(mReal.negate(), mEps.negate());
	}
	public ExactInfinitNumber mul(Rational c) {
		return new ExactInfinitNumber(mReal.mul(c), mEps.mul(c));
	}
	public ExactInfinitNumber div(Rational d) {
		return new ExactInfinitNumber(mReal.div(d), mEps.div(d));
	}
	/**
	 * Approximates the current value to make is suitable as value for a
	 * nonbasic variable.  We only consider the values <pre>a+b*eps</pre> where
	 * b is limited to the values -1, 0, 1.  If a different amount of epsilons
	 * should be used, this method fails and returns <code>null</code>.  
	 * @return An InfinitNumber usable as value for a nonbasic variable or
	 *         <code>null</code> if no such conversion is possible. 
	 */
	public InfinitNumber toInfinitNumber() {
		if (mEps == Rational.ZERO) {
			return new InfinitNumber(mReal, 0);
		}
		if (mEps == Rational.MONE) {
			return new InfinitNumber(mReal, -1);
		}
		if (mEps == Rational.ONE) {
			return new InfinitNumber(mReal, 1);
		}
		return null;
	}
	/**
	 * Transform this number to an {@link InfinitNumber} such that the resulting
	 * number is not bigger than this number.  Formally,
	 * <code>this.compareTo(new ExactInfinitNumber(\result)) >= 0</code> where
	 * equality only holds, if the result of {@link #toInfinitNumber()} is not
	 * <code>null</code>.
	 * @return Possibly floored InfinitNumber representation of this number.
	 */
	public InfinitNumber toInfinitNumberFloor() {
		return new InfinitNumber(mReal, mEps.floor().signum());
	}
	/**
	 * Transform this number to an {@link InfinitNumber} such that the resulting
	 * number is not smaller than this number.  Formally,
	 * <code>this.compareTo(new ExactInfinitNumber(\result)) <= 0</code> where
	 * equality only holds, if the result of {@link #toInfinitNumber()} is not
	 * <code>null</code>.
	 * @return Possibly ceiled InfinitNumber representation of this number.
	 */
	public InfinitNumber toInfinitNumberCeil() {
		return new InfinitNumber(mReal, mEps.ceil().signum());
	}

	@Override
	public int compareTo(ExactInfinitNumber other) {
		final int cmp = mReal.compareTo(other.mReal);
		return cmp == 0 ? mEps.compareTo(other.mEps) : cmp;
	}

	public int signum() {
		return mReal == Rational.ZERO ? mEps.signum() : mReal.signum();
	}
	public boolean isInfinite() {
		return !mReal.isRational();
	}
}
