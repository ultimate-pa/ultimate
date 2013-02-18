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
	MutableRational ma;
	// Infinitesimal part
	int meps;
	/// --- Construction ---
	public MutableInfinitNumber() {
		this(Rational.ZERO,0);
	}
	public MutableInfinitNumber(Rational a, int eps) {
		ma = new MutableRational(a);
		meps = eps;
	}
	public MutableInfinitNumber(InfinitNumber other) {
		ma = new MutableRational(other.ma);
		meps = other.meps;
	}
	public MutableInfinitNumber(MutableInfinitNumber other) {
		ma = new MutableRational(other.ma);
		meps = other.meps;
	}
	MutableInfinitNumber assign(MutableInfinitNumber other) {
		ma = new MutableRational(other.ma);
		meps = other.meps;
		return this;
	}
	MutableInfinitNumber assign(InfinitNumber other) {
		ma = new MutableRational(other.ma);
		meps = other.meps;
		return this;
	}
	/// --- Arithmetic ---
	/**
	 * Returns this + other.
	 */
	public MutableInfinitNumber add(InfinitNumber other) {
		ma.add(other.ma);
		meps = InfinitNumber.normEpsilon(meps + other.meps);
		return this;
	}
	/**
	 * Returns this - other.
	 */
	public MutableInfinitNumber sub(InfinitNumber other) {
		ma.sub(other.ma);
		meps = InfinitNumber.normEpsilon(meps - other.meps);
		return this;
	}
	/**
	 * Returns c*this.
	 */
	public MutableInfinitNumber mul(Rational c) {
		ma.mul(c);
		meps *= c.signum();
		return this;
	}
	/**
	 * Returns this/c.
	 */
	public MutableInfinitNumber div(Rational c) {
		ma.div(c);
		meps *= c.signum();
		return this;
	}
	/**
	 * Returns this+(fac1*fac2)
	 * @param fac1
	 * @param fac2
	 * @return
	 */
	public MutableInfinitNumber addmul(InfinitNumber fac1,Rational fac2) {
		ma.addmul(fac1.ma,fac2);
		meps = InfinitNumber.normEpsilon(meps + fac1.meps * fac2.signum());
		return this;
	}
	/**
	 * Returns this+(fac1*fac2)
	 * @param fac1
	 * @param fac2
	 * @return
	 */
	public MutableInfinitNumber addmul(InfinitNumber fac1,BigInteger fac2) {
		ma.addmul(fac1.ma,fac2);
		meps = InfinitNumber.normEpsilon(meps + fac1.meps * fac2.signum());
		return this;
	}
	/**
	 * Returns (this-s)/d
	 * @param s
	 * @param d
	 * @return
	 */
	public MutableInfinitNumber subdiv(InfinitNumber s,Rational d) {
		ma.subdiv(s.ma,d);
		meps = InfinitNumber.normEpsilon(meps - s.meps)*d.signum();
		return this;
	}
	public MutableInfinitNumber negate() {
		ma.negate();
		meps = -meps;
		return this;
	}
	/// --- Comparing ---
	@Override
	public int compareTo(MutableInfinitNumber arg0) {
		int ac = ma.compareTo(arg0.ma);
		if( ac == 0 )
			return meps - arg0.meps;
		return ac;
	}
	public boolean equals(Object o) {
		if( o instanceof InfinitNumber ) {
			InfinitNumber n = (InfinitNumber)o;
			return ma.equals(n.ma) && meps == n.meps;
		}
		if( o instanceof MutableInfinitNumber ) {
			MutableInfinitNumber n = (MutableInfinitNumber) o;
			return ma.equals(n.ma) && meps == n.meps;
		}
		return false;
	}
	public int hashCode() {
		return ma.hashCode() + 257 * meps;
	}
	/// --- Checks ---
	public boolean isInfinity() {
		return ma.equals(Rational.POSITIVE_INFINITY) || ma.equals(Rational.NEGATIVE_INFINITY);
	}
	
	public String toString() {
		if (meps == 0)
			return ma.toString();
		return ma + (meps > 0 ? "+" : "-") + "eps";
	}

	public InfinitNumber toInfinitNumber() {
		return new InfinitNumber(ma.toRational(),meps);
	}
}
