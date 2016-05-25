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

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.MutableRational;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Mutable version of the {@link InfinitNumber} class. All arithmetic
 * operations change the value of this object.
 * 
 * This class is intended to save some unneeded temporary objects in bigger
 * calculations. This should reduce the number of garbage collections such that
 * the program should run faster.
 * 
 * @author Juergen Christ
 */
public class MutableInfinitNumber implements Comparable<MutableInfinitNumber> {
	// Real part
	MutableRational mA;
	// Infinitesimal part
	int mEps;
	/// --- Construction ---
	public MutableInfinitNumber() {
		this(Rational.ZERO,0);
	}
	public MutableInfinitNumber(Rational a, int eps) {
		mA = new MutableRational(a);
		mEps = eps;
	}
	public MutableInfinitNumber(InfinitNumber other) {
		mA = new MutableRational(other.mA);
		mEps = other.mEps;
	}
	public MutableInfinitNumber(MutableInfinitNumber other) {
		mA = new MutableRational(other.mA);
		mEps = other.mEps;
	}
	MutableInfinitNumber assign(MutableInfinitNumber other) {
		mA = new MutableRational(other.mA);
		mEps = other.mEps;
		return this;
	}
	MutableInfinitNumber assign(InfinitNumber other) {
		mA = new MutableRational(other.mA);
		mEps = other.mEps;
		return this;
	}
	/// --- Arithmetic ---
	/**
	 * Returns this + other.
	 */
	public MutableInfinitNumber add(InfinitNumber other) {
		mA.add(other.mA);
		mEps = InfinitNumber.normEpsilon(mEps + other.mEps);
		return this;
	}
	/**
	 * Returns this - other.
	 */
	public MutableInfinitNumber sub(InfinitNumber other) {
		mA.sub(other.mA);
		mEps = InfinitNumber.normEpsilon(mEps - other.mEps);
		return this;
	}
	/**
	 * Returns c*this.
	 */
	public MutableInfinitNumber mul(Rational c) {
		mA.mul(c);
		mEps *= c.signum();
		return this;
	}
	/**
	 * Returns this/c.
	 */
	public MutableInfinitNumber div(Rational c) {
		mA.div(c);
		mEps *= c.signum();
		return this;
	}
	/**
	 * Returns this+(fac1*fac2)
	 * @param fac1
	 * @param fac2
	 * @return
	 */
	public MutableInfinitNumber addmul(InfinitNumber fac1,Rational fac2) {
		mA.addmul(fac1.mA,fac2);
		mEps = InfinitNumber.normEpsilon(mEps + fac1.mEps * fac2.signum());
		return this;
	}
	/**
	 * Returns this+(fac1*fac2)
	 * @param fac1
	 * @param fac2
	 * @return
	 */
	public MutableInfinitNumber addmul(InfinitNumber fac1,BigInteger fac2) {
		mA.addmul(fac1.mA,fac2);
		mEps = InfinitNumber.normEpsilon(mEps + fac1.mEps * fac2.signum());
		return this;
	}
	/**
	 * Returns (this-s)/d
	 * @param s
	 * @param d
	 * @return
	 */
	public MutableInfinitNumber subdiv(InfinitNumber s,Rational d) {
		mA.subdiv(s.mA,d);
		mEps = InfinitNumber.normEpsilon(mEps - s.mEps) * d.signum();
		return this;
	}
	public MutableInfinitNumber negate() {
		mA.negate();
		mEps = -mEps;
		return this;
	}
	/// --- Comparing ---
	@Override
	public int compareTo(MutableInfinitNumber arg0) {
		final int ac = mA.compareTo(arg0.mA);
		if (ac == 0) {
			return mEps - arg0.mEps;
		}
		return ac;
	}
	public int compareTo(InfinitNumber other) {
		final int ac = mA.compareTo(other.mA);
		if (ac == 0) {
			return mEps - other.mEps;
		}
		return ac;
	}
	@Override
	public boolean equals(Object o) {
		if (o instanceof InfinitNumber) {
			final InfinitNumber n = (InfinitNumber)o;
			return mA.equals(n.mA) && mEps == n.mEps;
		}
		if (o instanceof MutableInfinitNumber) {
			final MutableInfinitNumber n = (MutableInfinitNumber) o;
			return mA.equals(n.mA) && mEps == n.mEps;
		}
		return false;
	}
	@Override
	public int hashCode() {
		return mA.hashCode() + 257 * mEps;
	}
	/// --- Checks ---
	public boolean isInfinity() {
		return mA.equals(Rational.POSITIVE_INFINITY) || mA.equals(Rational.NEGATIVE_INFINITY);
	}
	
	@Override
	public String toString() {
		if (mEps == 0) {
			return mA.toString();
		}
		return mA + (mEps > 0 ? "+" : "-") + "eps";
	}

	public InfinitNumber toInfinitNumber() {
		return new InfinitNumber(mA.toRational(),mEps);
	}
}
