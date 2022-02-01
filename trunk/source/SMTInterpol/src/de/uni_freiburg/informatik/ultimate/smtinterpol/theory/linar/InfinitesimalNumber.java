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

/**
 * Class representing a number in the two dimensional infinitesimal space. (a,b) is a representation of a+b*eps,
 * b\in{-1,0,1}, where eps is an infinitesimal parameter used to handle strict inequalities.
 *
 * @author Juergen Christ
 */
public class InfinitesimalNumber implements Comparable<InfinitesimalNumber> {
	// Real part
	public final Rational mReal;
	// Infinitesimal part
	public final int mEps;
	/// --- Construction ---
	/**
	 * Zero constructor.
	 */
	public InfinitesimalNumber() {
		this(Rational.ZERO,0);
	}
	/**
	 * Constructor for arbitrary infinitesimal numbers.
	 * @param a Rational part of the number.
	 * @param b Infinitesimal part of the number.
	 */
	public InfinitesimalNumber(final Rational a, final int eps) {
		mReal = a;
		mEps = eps;
	}
	public static final InfinitesimalNumber POSITIVE_INFINITY =
			new InfinitesimalNumber(Rational.POSITIVE_INFINITY,0);
	public static final InfinitesimalNumber NEGATIVE_INFINITY =
			new InfinitesimalNumber(Rational.NEGATIVE_INFINITY,0);
	public static final InfinitesimalNumber ZERO = new InfinitesimalNumber(Rational.ZERO,0);
	public static final InfinitesimalNumber ONE = new InfinitesimalNumber(Rational.ONE,0);
	public static final InfinitesimalNumber EPSILON =
			new InfinitesimalNumber(Rational.ZERO,1);

	static int normEpsilon(final int eps) {
		return Integer.signum(eps);
	}
	/// --- Arithmetic ---
	/**
	 * Returns this + other.
	 */
	public InfinitesimalNumber add(final InfinitesimalNumber other) {
		// Unfortunately, in many places we add "incompatible" InfinitNumbers.
		// Sometimes, because we are only interested in the ma part, sometimes
		// intentionally, for example to get rid of the epsilon by adding it.
		// TODO: check these places more carefully
		// assert (meps * other.meps < 0);
		return new InfinitesimalNumber(mReal.add(other.mReal),
				normEpsilon(mEps + other.mEps));
	}
	/**
	 * Returns this - other.
	 */
	public InfinitesimalNumber sub(final InfinitesimalNumber other) {
		// Unfortunately, in many places we add "incompatible" InfinitNumbers.
		// Sometimes, because we are only interested in the ma part, sometimes
		// intentionally, for example to get rid of the epsilon by adding it.
		// TODO: check these places more carefully
		// assert (meps * other.meps > 0);
		return new InfinitesimalNumber(mReal.sub(other.mReal),
				normEpsilon(mEps - other.mEps));
	}

	public ExactInfinitesimalNumber sub(final ExactInfinitesimalNumber other) {
		return new ExactInfinitesimalNumber(mReal.sub(other.getRealValue()),
				Rational.valueOf(mEps, 1).sub(other.getEpsilon()));
	}
	/**
	 * Returns c*this.
	 */
	public InfinitesimalNumber mul(final Rational c) {
		return new InfinitesimalNumber(mReal.mul(c),mEps * c.signum());
	}
	/**
	 * Returns this/c.
	 */
	public InfinitesimalNumber div(final Rational c) {
		return new InfinitesimalNumber(mReal.div(c),mEps * c.signum());
	}

	/**
	 * Return the absolute value of this.
	 *
	 * @return the absolute value.
	 */
	public InfinitesimalNumber abs() {
		if (signum() < 0) {
			return negate();
		} else {
			return this;
		}
	}
	/**
	 * Returns -this.
	 */
	public InfinitesimalNumber negate() {
		return new InfinitesimalNumber(mReal.negate(),-mEps);
	}
	/**
	 * Returns this+(fac1*fac2)
	 * @param fac1
	 * @param fac2
	 * @return
	 */
	public InfinitesimalNumber addmul(final InfinitesimalNumber fac1,final Rational fac2) {
		//if (meps * fac1.meps*fac2.signum() < 0) throw new AssertionError(); // TODO make assert
		return new InfinitesimalNumber(mReal.addmul(fac1.mReal,fac2),
				normEpsilon(mEps + fac1.mEps * fac2.signum()));
	}
	/**
	 * Returns (this-s)/d
	 * @param s
	 * @param d
	 * @return
	 */
	public InfinitesimalNumber subdiv(final InfinitesimalNumber s,final Rational d) {
		//if (meps * s.meps*d.signum() > 0) throw new AssertionError(); // TODO make assert
		return new InfinitesimalNumber(mReal.subdiv(s.mReal,d),
				normEpsilon(mEps - s.mEps) * d.signum());
	}
	/// --- Comparing ---
	@Override
	public int compareTo(final InfinitesimalNumber arg0) {
		final int ac = mReal.compareTo(arg0.mReal);
		if (ac == 0) {
			return mEps - arg0.mEps;
		}
		return ac;
	}

	@Override
	public boolean equals(final Object o) {
		if (o instanceof InfinitesimalNumber) {
			final InfinitesimalNumber n = (InfinitesimalNumber) o;
			return mReal.equals(n.mReal) && mEps == n.mEps;
		}
		return false;
	}

	@Override
	public int hashCode() {
		return mReal.hashCode() + 65537 * mEps;
	}
	/**
	 * Returns <code>true</code> iff this is less then other. This function is
	 * considered slightly more efficient than
	 * <code>this.compareTo(other) < 0</code> but yields the same result.
	 * @param other Number to compare against.
	 * @return <code>true</code> iff this is less than other.
	 */
	public boolean less(final InfinitesimalNumber other) {
		final int ac = mReal.compareTo(other.mReal);
		return ac < 0 || (ac == 0 && mEps < other.mEps);
	}
	/**
	 * Returns <code>true</code> iff this is less then or equal to other. This
	 * function is considered slightly more efficient than
	 * <code>this.compareTo(other) <= 0</code> but yields the same result.
	 * @param other Number to compare against.
	 * @return <code>true</code> iff this is less than or equal to other.
	*/
	public boolean lesseq(final InfinitesimalNumber other) {
		final int ac = mReal.compareTo(other.mReal);
		return ac < 0 || (ac == 0 && mEps <= other.mEps);
	}
	/// --- Checks ---
	/**
	 * Returns true iff this represents either positive or negative infinity.
	 */
	public boolean isInfinity() {
		return mReal == Rational.POSITIVE_INFINITY || mReal == Rational.NEGATIVE_INFINITY;
	}

	@Override
	public String toString() {
		if (mEps == 0) {
			return mReal.toString();
		}
		return mReal + (mEps > 0 ? "+" : "-") + "eps";
	}
	/**
	 * Check whether this number represents an integral value. Both infinity
	 * values are treated as integral, but no factor of eps is integral.
	 * @return <code>true</code> iff value is integral.
	 */
	public boolean isIntegral() {
		return mReal.isIntegral() && mEps == 0;
	}
	/**
	 * Returns the next lower integral number. Flooring depends on the value
	 * of the infinitesimal coefficient. Note that the result will have a zero
	 * infinitesimal coefficient.
	 * @return The largest integral number less or equal to the current value.
	 */
	public InfinitesimalNumber floor() {
		if (!mReal.isIntegral()) {
			return new InfinitesimalNumber(mReal.floor(),0);
		}
		if (mEps >= 0) {
			return new InfinitesimalNumber(mReal,0);
		}
		return new InfinitesimalNumber(mReal.sub(Rational.ONE),0);
	}
	/**
	 * Returns the next higher integral number. Ceiling depends on the value
	 * of the infinitesimal coefficient. Note that the result will have a zero
	 * infinitesimal coefficient.
	 * @return The smallest integral number greater or equal to the current value.
	 */
	public InfinitesimalNumber ceil() {
		if (!mReal.isIntegral()) {
			return new InfinitesimalNumber(mReal.ceil(),0);
		}
		if (mEps <= 0) {
			return new InfinitesimalNumber(mReal,0);
		}
		return new InfinitesimalNumber(mReal.add(Rational.ONE),0);
	}

	public int signum() {
		return mReal == Rational.ZERO ? mEps : mReal.signum();
	}

	public InfinitesimalNumber inverse() {
		// Note that for c != 0:
		//    1/(c + sign*eps) ~= 1/c - sign*eps/(c*c)
		// Since c*c is positive, the sign of eps is always negated.
		return new InfinitesimalNumber(mReal.inverse(), -mEps);
	}
}
