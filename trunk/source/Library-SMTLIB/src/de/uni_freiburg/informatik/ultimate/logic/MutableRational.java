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
	int mnum;
	int mdenom;
	BigInteger mbignum;
	BigInteger mbigdenom;
	
	public MutableRational(int num, int denom) {
		setValue(num, denom);
	}
	
	public MutableRational(BigInteger num, BigInteger denom) {
		mbignum = num;
		mbigdenom = denom;
		normalize();
	}
	
	public MutableRational(Rational r) {
		mnum = r.mnum;
		mdenom = r.mdenom;
		if (r instanceof Rational.BigRational) {
			mbignum = r.numerator();
			mbigdenom = r.denominator();
		}
	}
	
	public MutableRational(MutableRational r) {
		mnum = r.mnum;
		mdenom = r.mdenom;
		mbignum = r.mbignum;
		mbigdenom = r.mbigdenom;
	}

	public void setValue(Rational value) {
		mnum = value.mnum;
		mdenom = value.mdenom;
		if (value instanceof Rational.BigRational) {
			mbignum = value.numerator();
			mbigdenom = value.denominator();
		} else {
			mbignum = mbigdenom = null;
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
			mnum = (int) newnum;
			mdenom = (int) newdenom;
			mbignum = mbigdenom = null;
		} else {
			mbignum = BigInteger.valueOf(newnum);
			mbigdenom = BigInteger.valueOf(newdenom);
		}
	}
	
	private void normalize() {
		if( mbignum == null ) {
			int norm = Rational.gcd(mnum, mdenom);
			if (norm != 0 && norm != 1) {
				mnum /= norm;
				mdenom /= norm;
			}
			if( mdenom < 0 ) {
				mnum = -mnum;
				mdenom = -mdenom;
			}
		} else {
			if (!mbigdenom.equals(BigInteger.ONE)) {
				BigInteger norm = Rational.gcd(mbignum, mbigdenom).abs();
				if (mbigdenom.signum() < 0)
					norm = norm.negate();
				if (!norm.equals(BigInteger.ZERO)
					&& !norm.equals(BigInteger.ONE)) {
					mbignum = mbignum.divide(norm);
					mbigdenom = mbigdenom.divide(norm);
				}
			}
			if( mbigdenom.bitLength() < 32 && mbignum.bitLength() < 32) {
				mnum = mbignum.intValue();
				mdenom = mbigdenom.intValue();
				mbignum = mbigdenom = null;
			}
		}
	}

	public MutableRational add(Rational other) {
		/* fast path */
		if (other == Rational.ZERO)
			return this;
		if (mbignum == null && !(other instanceof Rational.BigRational)) {
			if (mdenom == other.mdenom) {
				/* handle gcd = 0 correctly 
				 * two INFINITYs with same sign give INFINITY,
				 * otherwise it gives NAN.
				 */
				if (mdenom == 0) {
					if (mnum != other.mnum)
						mnum = 0;
				} else {
					/* a common, very simple case, e.g. for integers */
					setValue((long) mnum + other.mnum, mdenom);
				}
			} else {
				int gcd = Rational.gcd(mdenom, other.mdenom);
				long denomgcd = (long) (mdenom / gcd); 
				long otherdenomgcd = (long) (other.mdenom / gcd); 
				long newdenom = denomgcd * other.mdenom;
				long newnum = otherdenomgcd * mnum + denomgcd * other.mnum;
				setValue(newnum, newdenom);
			}
			return this;
		}

		if (this.mbignum == null && this.mnum == 0 && this.mdenom == 1) {
			/* This is zero; set result to other */
			mbignum = other.numerator();
			mbigdenom = other.denominator();
			return this;
		}
		
		BigInteger tdenom = denominator();
		BigInteger odenom = other.denominator();
		if (tdenom.equals(odenom)) {
			mbignum = numerator().add(other.numerator());
			mbigdenom = tdenom; 
		} else {
			BigInteger gcd = Rational.gcd(tdenom, odenom);
			BigInteger tdenomgcd = tdenom.divide(gcd);
			BigInteger odenomgcd = odenom.divide(gcd);
			mbignum = numerator().multiply(odenomgcd)
				.add(other.numerator().multiply(tdenomgcd));
			mbigdenom = tdenom.multiply(odenomgcd);
		}
		normalize();
		return this;
	}
	
	public MutableRational negate() {
		if (mbignum == null) {
			if (mnum == Integer.MIN_VALUE)
				setValue(-(long)Integer.MIN_VALUE, mdenom);
			else
				mnum = -mnum;
		} else
			mbignum = mbignum.negate();
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
		if (mbignum == null && !(other instanceof Rational.BigRational)) {
			long newnum = (long)mnum * other.mnum;
			long newdenom = (long)mdenom * other.mdenom;
			setValue(newnum, newdenom);
			return this;
		}
		
		mbignum = numerator().multiply(other.numerator());
		mbigdenom = denominator().multiply(other.denominator());
		normalize();
		return this;
	}
	
	public MutableRational div(Rational other) {
		/* fast path */
		if (other == Rational.ZERO)
			throw new ArithmeticException("Division by ZERO");
		if (mbignum == null && mnum == 0)
			return this;
		if (other == Rational.ONE)
			return this;
		if (other == Rational.MONE)
			return this.negate();
		if (mbignum == null && !(other instanceof Rational.BigRational)) {
			long newnum = (long)mnum * other.mdenom;
			long newdenom = (long)mdenom * other.mnum;
			// +-inf : -c = -+inf
			if (newdenom == 0 && other.mnum < 0)
				newnum = -newnum;
			setValue(newnum, newdenom);
			return this;
		}
		mbignum = numerator().multiply(other.denominator());
		mbigdenom = denominator().multiply(other.numerator());
		// +-inf : -c = -+inf
		if (mbigdenom.equals(BigInteger.ZERO) && 
				other.numerator().signum() == -1)
			mbignum = mbignum.negate();
		normalize();
		return this;
	}
	
	public MutableRational inverse() {
		if (mbignum == null) {
			setValue(mdenom, mnum);
		} else {
			BigInteger tmp = mbigdenom;
			if( mbignum.signum() < 0 ) {
				mbigdenom = mbignum.negate();
				mbignum = tmp.negate();
			} else {
				mbigdenom = mbignum;
				mbignum = tmp;
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
		if (mbignum == null && o.mbignum == null) {
			/* handle infinities and nan */
			if (o.mdenom == mdenom)
				return mnum < o.mnum ? -1 : mnum == o.mnum ? 0 : 1;
			long valt = (long)mnum * o.mdenom;
			long valo = (long)o.mnum * mdenom;
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
			return mbignum == null
				? !(r instanceof Rational.BigRational) && mnum == r.mnum && mdenom == r.mdenom
				: mbignum.equals(r.numerator()) && mbigdenom.equals(r.denominator());
		}
		if (o instanceof MutableRational) {
			MutableRational r = (MutableRational) o;
			// Works thanks to normalization!!!
			return mbignum == null
				? r.mbignum == null && mnum == r.mnum && mdenom == r.mdenom
				: mbignum.equals(r.mbignum) && mbigdenom.equals(r.mbigdenom);
		}
		return false;
	}
	
	public BigInteger numerator() {
		return mbignum == null ? BigInteger.valueOf(mnum) : mbignum;
	}
	public BigInteger denominator() {
		return mbigdenom == null ? BigInteger.valueOf(mdenom) : mbigdenom;
	}
	
	public int hashCode() {
		if (mbignum == null)
			return mnum * 257 + mdenom;
		else
			return mbignum.hashCode() * 257 + mbigdenom.hashCode();
	}
	
	public String toString() {
		/* fast path */
		if (mbignum == null) {
			if (mdenom == 0)
				return mnum > 0 ? "inf" : mnum == 0 ? "nan" : "-inf";
			if (mdenom == 1)
				return String.valueOf(mnum);
			return mnum + "/" + mdenom;
		} else {
			if (mbigdenom.equals(BigInteger.ONE))
				return mbignum.toString();
			return mbignum + "/" + mbigdenom;
		}
	}
	
	/**
	 * Check whether this rational represents an integral value. Both infinity
	 * values are treated as integral.
	 * @return <code>true</code> iff value is integral.
	 */
	public boolean isIntegral() {
		return (mbignum == null) ? mdenom <= 1 : mbigdenom.equals(BigInteger.ONE);
	}
	public Rational toRational() {
		if (mbignum == null)
			return Rational.valueOf(mnum, mdenom);
		return Rational.valueOf(numerator(), denominator());
	}

	public int signum() {
		if (mbignum == null)
			return mnum < 0 ? -1 : mnum == 0 ? 0 : 1;
		return mbignum.signum();
	}
}
