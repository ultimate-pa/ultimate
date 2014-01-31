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
package de.uni_freiburg.informatik.ultimate.logic;

import java.math.BigInteger;

/**
 * Mutable version of the {@link Rational} class. All arithmetic
 * operations change the value of this object.
 * 
 * This class is intended to save some unneeded temporary objects in bigger
 * calculations. This should reduce the number of garbage collections such that
 * the program should run faster.
 * 
 * @author Juergen Christ
 */
public class MutableRational implements Comparable<MutableRational> {
	int mNum;
	int mDenom;
	BigInteger mBignum;
	BigInteger mBigdenom;
	
	public MutableRational(int num, int denom) {
		setValue(num, denom);
	}
	
	public MutableRational(BigInteger num, BigInteger denom) {
		mBignum = num;
		mBigdenom = denom;
		normalize();
	}
	
	public MutableRational(Rational r) {
		mNum = r.mNum;
		mDenom = r.mDenom;
		if (r instanceof Rational.BigRational) {
			mBignum = r.numerator();
			mBigdenom = r.denominator();
		}
	}
	
	public MutableRational(MutableRational r) {
		mNum = r.mNum;
		mDenom = r.mDenom;
		mBignum = r.mBignum;
		mBigdenom = r.mBigdenom;
	}

	public void setValue(Rational value) {
		mNum = value.mNum;
		mDenom = value.mDenom;
		if (value instanceof Rational.BigRational) {
			mBignum = value.numerator();
			mBigdenom = value.denominator();
		} else {
			mBignum = mBigdenom = null;
		}
	}
	
	public void setValue(long newnum, long newdenom) {
		long gcd2 = Rational.gcd(Math.abs(newnum), Math.abs(newdenom));
		if (newdenom < 0)
			gcd2 = -gcd2;
		if (gcd2 != 0) {
			newnum /= gcd2;
			newdenom /= gcd2;
		}
		
		if (Integer.MIN_VALUE <= newnum && newnum <= Integer.MAX_VALUE
			&& newdenom <= Integer.MAX_VALUE) {
			mNum = (int) newnum;
			mDenom = (int) newdenom;
			mBignum = mBigdenom = null;
		} else {
			mBignum = BigInteger.valueOf(newnum);
			mBigdenom = BigInteger.valueOf(newdenom);
		}
	}
	
	private void normalize() {
		if (mBignum == null) {
			int norm = Rational.gcd(mNum, mDenom);
			if (norm != 0 && norm != 1) {
				mNum /= norm;
				mDenom /= norm;
			}
			if (mDenom < 0) {
				mNum = -mNum;
				mDenom = -mDenom;
			}
		} else {
			if (!mBigdenom.equals(BigInteger.ONE)) {
				BigInteger norm = Rational.gcd(mBignum, mBigdenom).abs();
				if (mBigdenom.signum() < 0)
					norm = norm.negate();
				if (!norm.equals(BigInteger.ZERO)
					&& !norm.equals(BigInteger.ONE)) {
					mBignum = mBignum.divide(norm);
					mBigdenom = mBigdenom.divide(norm);
				}
			}
			if (mBigdenom.bitLength() < 32 && mBignum.bitLength() < 32) { // NOCHECKSTYLE
				mNum = mBignum.intValue();
				mDenom = mBigdenom.intValue();
				mBignum = mBigdenom = null;
			}
		}
	}

	public MutableRational add(Rational other) {
		/* fast path */
		if (other == Rational.ZERO)
			return this;
		if (mBignum == null && !(other instanceof Rational.BigRational)) {
			if (mDenom == other.mDenom) {
				/* handle gcd = 0 correctly 
				 * two INFINITYs with same sign give INFINITY,
				 * otherwise it gives NAN.
				 */
				if (mDenom == 0) {
					if (mNum != other.mNum)
						mNum = 0;
				} else {
					/* a common, very simple case, e.g. for integers */
					setValue((long) mNum + other.mNum, mDenom);
				}
			} else {
				int gcd = Rational.gcd(mDenom, other.mDenom);
				long denomgcd = (long) (mDenom / gcd); 
				long otherdenomgcd = (long) (other.mDenom / gcd); 
				long newdenom = denomgcd * other.mDenom;
				long newnum = otherdenomgcd * mNum + denomgcd * other.mNum;
				setValue(newnum, newdenom);
			}
			return this;
		}

		if (this.mBignum == null && this.mNum == 0 && this.mDenom == 1) {
			/* This is zero; set result to other */
			mBignum = other.numerator();
			mBigdenom = other.denominator();
			return this;
		}
		
		BigInteger tdenom = denominator();
		BigInteger odenom = other.denominator();
		if (tdenom.equals(odenom)) {
			mBignum = numerator().add(other.numerator());
			mBigdenom = tdenom; 
		} else {
			BigInteger gcd = Rational.gcd(tdenom, odenom);
			BigInteger tdenomgcd = tdenom.divide(gcd);
			BigInteger odenomgcd = odenom.divide(gcd);
			mBignum = numerator().multiply(odenomgcd)
				.add(other.numerator().multiply(tdenomgcd));
			mBigdenom = tdenom.multiply(odenomgcd);
		}
		normalize();
		return this;
	}
	
	public MutableRational negate() {
		if (mBignum == null) {
			if (mNum == Integer.MIN_VALUE)
				setValue(-(long)Integer.MIN_VALUE, mDenom);
			else
				mNum = -mNum;
		} else
			mBignum = mBignum.negate();
		return this;
	}
	
	public MutableRational sub(Rational other) {
		return add(other.negate());
	}
	
	public MutableRational mul(Rational other) {
		/* fast path */
		if (other == Rational.ONE)
			return this;
		if (other == Rational.MONE)
			return this.negate();
		if (mBignum == null && !(other instanceof Rational.BigRational)) {
			long newnum = (long)mNum * other.mNum;
			long newdenom = (long)mDenom * other.mDenom;
			setValue(newnum, newdenom);
			return this;
		}
		
		mBignum = numerator().multiply(other.numerator());
		mBigdenom = denominator().multiply(other.denominator());
		normalize();
		return this;
	}
	
	public MutableRational div(Rational other) {
		/* fast path */
		if (other == Rational.ZERO)
			throw new ArithmeticException("Division by ZERO");
		if (mBignum == null && mNum == 0)
			return this;
		if (other == Rational.ONE)
			return this;
		if (other == Rational.MONE)
			return this.negate();
		if (mBignum == null && !(other instanceof Rational.BigRational)) {
			long newnum = (long)mNum * other.mDenom;
			long newdenom = (long)mDenom * other.mNum;
			// +-inf : -c = -+inf
			if (newdenom == 0 && other.mNum < 0)
				newnum = -newnum;
			setValue(newnum, newdenom);
			return this;
		}
		mBignum = numerator().multiply(other.denominator());
		mBigdenom = denominator().multiply(other.numerator());
		// +-inf : -c = -+inf
		if (mBigdenom.equals(BigInteger.ZERO)
				&& other.numerator().signum() == -1)
			mBignum = mBignum.negate();
		normalize();
		return this;
	}
	
	public MutableRational inverse() {
		if (mBignum == null) {
			setValue(mDenom, mNum);
		} else {
			BigInteger tmp = mBigdenom;
			if (mBignum.signum() < 0) {
				mBigdenom = mBignum.negate();
				mBignum = tmp.negate();
			} else {
				mBigdenom = mBignum;
				mBignum = tmp;
			}
		}
		return this;
	}
	
	public boolean isNegative() {
		return numerator().signum() < 0;
	}
	/**
	 * Returns <code>this+(fac1*fac2)</code>
	 */
	public MutableRational addmul(Rational fac1,Rational fac2) {
		return add(fac1.mul(fac2));
	}
	/**
	 * Returns <code>this+(fac1*fac2)</code>
	 */
	public MutableRational addmul(Rational fac1,BigInteger fac2) {
		return add(fac1.mul(fac2));
	}
	/**
	 * Returns <code>(this-s)/d</code>
	 */
	public MutableRational subdiv(Rational s,Rational d) {
		return sub(s).div(d);
	}

	@Override
	public int compareTo(MutableRational o) {
		/* fast path */
		if (mBignum == null && o.mBignum == null) {
			/* handle infinities and nan */
			if (o.mDenom == mDenom)
				return mNum < o.mNum ? -1 : mNum == o.mNum ? 0 : 1;
			long valt = (long)mNum * o.mDenom;
			long valo = (long)o.mNum * mDenom;
			return valt < valo ? -1 : valt == valo ? 0 : 1; 
		}
		BigInteger valthis = numerator().multiply(o.denominator());
		BigInteger valo = o.numerator().multiply(denominator());
		return valthis.compareTo(valo);
	}
		
	public boolean equals(Object o) {
		if (o instanceof Rational) {
			Rational r = (Rational) o;
			// Works thanks to normalization!!!
			return mBignum == null
				? !(r instanceof Rational.BigRational)
					&& mNum == r.mNum && mDenom == r.mDenom
				: mBignum.equals(r.numerator())
					&& mBigdenom.equals(r.denominator());
		}
		if (o instanceof MutableRational) {
			MutableRational r = (MutableRational) o;
			// Works thanks to normalization!!!
			return mBignum == null
				? r.mBignum == null && mNum == r.mNum && mDenom == r.mDenom
				: mBignum.equals(r.mBignum) && mBigdenom.equals(r.mBigdenom);
		}
		return false;
	}
	
	public BigInteger numerator() {
		return mBignum == null ? BigInteger.valueOf(mNum) : mBignum;
	}
	public BigInteger denominator() {
		return mBigdenom == null ? BigInteger.valueOf(mDenom) : mBigdenom;
	}
	
	public int hashCode() {
		if (mBignum == null)
			return mNum * 257 + mDenom;
		else
			return mBignum.hashCode() * 257 + mBigdenom.hashCode();
	}
	
	public String toString() {
		/* fast path */
		if (mBignum == null) {
			if (mDenom == 0)
				return mNum > 0 ? "inf" : mNum == 0 ? "nan" : "-inf";
			if (mDenom == 1)
				return String.valueOf(mNum);
			return mNum + "/" + mDenom;
		} else {
			if (mBigdenom.equals(BigInteger.ONE))
				return mBignum.toString();
			return mBignum + "/" + mBigdenom;
		}
	}
	
	/**
	 * Check whether this rational represents an integral value. Both infinity
	 * values are treated as integral.
	 * @return <code>true</code> iff value is integral.
	 */
	public boolean isIntegral() {
		return (mBignum == null)
				? mDenom <= 1 : mBigdenom.equals(BigInteger.ONE);
	}
	public Rational toRational() {
		if (mBignum == null)
			return Rational.valueOf(mNum, mDenom);
		return Rational.valueOf(numerator(), denominator());
	}

	public int signum() {
		if (mBignum == null)
			return mNum < 0 ? -1 : mNum == 0 ? 0 : 1;
		return mBignum.signum();
	}
}
