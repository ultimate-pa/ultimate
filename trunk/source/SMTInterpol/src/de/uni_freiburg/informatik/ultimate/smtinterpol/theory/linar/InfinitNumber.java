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
 * Class representing a number in the two dimensional infinitesimal space.
 * (a,b) is a representation of a+b*e where e>0 is an infinitesimal parameter
 * used to handle strict inequalities.
 * 
 * Note that members of this class are immutable. Use 
 * <code>MutableInfinitNumber</code> for a mutable version.
 * 
 * @author Juergen Christ
 */
public class InfinitNumber implements Comparable<InfinitNumber> {
	// Real part
	public final Rational mA;
	// Infinitesimal part
	public final int mEps;
	/// --- Construction ---
	/**
	 * Zero constructor.
	 */
	public InfinitNumber() {
		this(Rational.ZERO,0);
	}
	/**
	 * Constructor for arbitrary infinitesimal numbers.
	 * @param a Rational part of the number.
	 * @param b Infinitesimal part of the number.
	 */
	public InfinitNumber(Rational a, int eps) {
		mA = a;
		mEps = eps;
	}
	public static final InfinitNumber POSITIVE_INFINITY =
			new InfinitNumber(Rational.POSITIVE_INFINITY,0);
	public static final InfinitNumber NEGATIVE_INFINITY =
			new InfinitNumber(Rational.NEGATIVE_INFINITY,0);
	public static final InfinitNumber ZERO = new InfinitNumber(Rational.ZERO,0);
	public static final InfinitNumber ONE = new InfinitNumber(Rational.ONE,0);
	public static final InfinitNumber EPSILON =
			new InfinitNumber(Rational.ZERO,1);
	
	static int normEpsilon(int eps) {
		return eps > 0 ? 1 : eps < 0 ? -1 : 0;
	}
	/// --- Arithmetic ---
	/**
	 * Returns this + other.
	 */
	public InfinitNumber add(InfinitNumber other) {
		// Unfortunately, in many places we add "incompatible" InfinitNumbers.
		// Sometimes, because we are only interested in the ma part, sometimes
		// intentionally, for example to get rid of the epsilon by adding it.
		// TODO: check these places more carefully
		// assert (meps * other.meps < 0);
		return new InfinitNumber(mA.add(other.mA),
				normEpsilon(mEps + other.mEps));
	}
	/**
	 * Returns this - other.
	 */
	public InfinitNumber sub(InfinitNumber other) {
		// Unfortunately, in many places we add "incompatible" InfinitNumbers.
		// Sometimes, because we are only interested in the ma part, sometimes
		// intentionally, for example to get rid of the epsilon by adding it.
		// TODO: check these places more carefully
		// assert (meps * other.meps > 0);
		return new InfinitNumber(mA.sub(other.mA),
				normEpsilon(mEps - other.mEps));
	}

	public ExactInfinitNumber sub(ExactInfinitNumber other) {
		return new ExactInfinitNumber(mA.sub(other.getRealValue()), 
				Rational.valueOf(mEps, 1).sub(other.getEpsilon()));
	}
	/**
	 * Returns c*this.
	 */
	public InfinitNumber mul(Rational c) {
		return new InfinitNumber(mA.mul(c),mEps * c.signum());
	}
	/**
	 * Returns this/c.
	 */
	public InfinitNumber div(Rational c) {
		return new InfinitNumber(mA.div(c),mEps * c.signum());
	}
	/**
	 * Returns -this.
	 */
	public InfinitNumber negate() {
		return new InfinitNumber(mA.negate(),-mEps);
	}
	/**
	 * Returns this+(fac1*fac2)
	 * @param fac1
	 * @param fac2
	 * @return
	 */
	public InfinitNumber addmul(InfinitNumber fac1,Rational fac2) {
		//if (meps * fac1.meps*fac2.signum() < 0) throw new AssertionError(); // TODO make assert
		return new InfinitNumber(mA.addmul(fac1.mA,fac2),
				normEpsilon(mEps + fac1.mEps * fac2.signum()));
	}
	/**
	 * Returns (this-s)/d
	 * @param s
	 * @param d
	 * @return
	 */
	public InfinitNumber subdiv(InfinitNumber s,Rational d) {
		//if (meps * s.meps*d.signum() > 0) throw new AssertionError(); // TODO make assert
		return new InfinitNumber(mA.subdiv(s.mA,d),
				normEpsilon(mEps - s.mEps) * d.signum());
	}
	/// --- Comparing ---
	@Override
	public int compareTo(InfinitNumber arg0) {
		final int ac = mA.compareTo(arg0.mA);
		if (ac == 0) {
			return mEps - arg0.mEps;
		}
		return ac;
	}
	@Override
	public boolean equals(Object o) {
		if (o instanceof InfinitNumber) {
			final InfinitNumber n = (InfinitNumber) o;
			return mA.equals(n.mA) && mEps == n.mEps;
		}
		if (o instanceof MutableInfinitNumber) {
			return ((MutableInfinitNumber)o).equals(this);
		}
		return false;
	}
	@Override
	public int hashCode() {
		return mA.hashCode() + 65537 * mEps;
	}
	/**
	 * Returns <code>true</code> iff this is less then other. This function is
	 * considered slightly more efficient than 
	 * <code>this.compareTo(other) < 0</code> but yields the same result. 
	 * @param other Number to compare against.
	 * @return <code>true</code> iff this is less than other.
	 */
	public boolean less(InfinitNumber other) {
		final int ac = mA.compareTo(other.mA);
		return ac < 0 || (ac == 0 && mEps < other.mEps);
	}
	/**
	 * Returns <code>true</code> iff this is less then or equal to other. This 
	 * function is considered slightly more efficient than 
	 * <code>this.compareTo(other) <= 0</code> but yields the same result. 
	 * @param other Number to compare against.
	 * @return <code>true</code> iff this is less than or equal to other.
	*/
	public boolean lesseq(InfinitNumber other) {
		final int ac = mA.compareTo(other.mA);
		return ac < 0 || (ac == 0 && mEps <= other.mEps);
	}
	/// --- Checks ---
	/**
	 * Returns true iff this represents either positive or negative infinity.
	 */
	public boolean isInfinity() {
		return mA == Rational.POSITIVE_INFINITY || mA == Rational.NEGATIVE_INFINITY;
	}
	
	@Override
	public String toString() {
		if (mEps == 0) {
			return mA.toString();
		}
		return mA + (mEps > 0 ? "+" : "-") + "eps";
	}
	/**
	 * Check whether this number represents an integral value. Both infinity
	 * values are treated as integral, but no factor of eps is integral.
	 * @return <code>true</code> iff value is integral.
	 */
	public boolean isIntegral() {
		return mA.isIntegral() && mEps == 0;
	}
	/**
	 * Returns the next lower integral number. Flooring depends on the value
	 * of the infinitesimal coefficient. Note that the result will have a zero
	 * infinitesimal coefficient.
	 * @return The largest integral number less or equal to the current value.
	 */
	public InfinitNumber floor() {
		if (!mA.isIntegral()) {
			return new InfinitNumber(mA.floor(),0);
		}
		if (mEps >= 0) {
			return new InfinitNumber(mA,0);
		}
		return new InfinitNumber(mA.sub(Rational.ONE),0);
	}
	/**
	 * Returns the next higher integral number. Ceiling depends on the value
	 * of the infinitesimal coefficient. Note that the result will have a zero
	 * infinitesimal coefficient.
	 * @return The smallest integral number greater or equal to the current value.
	 */
	public InfinitNumber ceil() {
		if (!mA.isIntegral()) {
			return new InfinitNumber(mA.ceil(),0);
		}
		if (mEps <= 0) {
			return new InfinitNumber(mA,0);
		}
		return new InfinitNumber(mA.add(Rational.ONE),0);
	}
	
	public int signum() {
		return mA == Rational.ZERO ? mEps : mA.signum();
	}
	
	public InfinitNumber inverse() {
		// Note that for c != 0:
		//    1/(c + sign*eps) ~= 1/c - sign*eps/(c*c)
		// Since c*c is positive, the sign of eps is always negated.
		return new InfinitNumber(mA.inverse(), -mEps);
	}
}
