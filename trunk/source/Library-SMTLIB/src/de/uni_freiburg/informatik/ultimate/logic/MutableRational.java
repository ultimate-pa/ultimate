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

import de.uni_freiburg.informatik.ultimate.logic.Rational.BigRational;

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

	/**
	 * Create a new rational representing num/denom.
	 * @param num the numerator.
	 * @param denom the denominator.
	 */
	public MutableRational(int num, int denom) {
		setValue(num, denom);
	}

	/**
	 * Create a new rational representing num/denom.
	 * @param num the numerator.
	 * @param denom the denominator.
	 */
	public MutableRational(BigInteger num, BigInteger denom) {
		mBignum = num;
		mBigdenom = denom;
		normalize();
	}

	/**
	 * Create a new mutable rational from a rational.
	 * @param r the rational.
	 */
	public MutableRational(Rational r) {
		mNum = r.mNum;
		mDenom = r.mDenom;
		if (r instanceof Rational.BigRational) {
			mBignum = r.numerator();
			mBigdenom = r.denominator();
		}
	}

	/**
	 * Create a new copy of a mutable rational.
	 * @param r the original rational.
	 */
	public MutableRational(MutableRational r) {
		mNum = r.mNum;
		mDenom = r.mDenom;
		mBignum = r.mBignum;
		mBigdenom = r.mBigdenom;
	}

	/**
	 * Set the value of this rational to value.
	 * @param value the value to set to.
	 */
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

	/**
	 * Set the value of this rational to newnum/newdenom.
	 * @param newnum the new numerator.
	 * @param newdenom the new denominator.
	 */
	public void setValue(long newnum, long newdenom) {
		long gcd2 = Rational.gcd(Math.abs(newnum), Math.abs(newdenom));
		if (newdenom < 0) {
			gcd2 = -gcd2;
		}
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

	/**
	 * Normalize the rational by dividing through the gcd.  This is
	 * called after every operation.
	 */
	private void normalize() {
		if (mBignum == null) {
			final int norm = Rational.gcd(mNum, mDenom);
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
				if (mBigdenom.signum() < 0) {
					norm = norm.negate();
				}
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

	/**
	 * Add the rational other to this rational.
	 * @param other the rational to add.
	 * @return this mutable rational.
	 */
	public MutableRational add(Rational other) {
		/* fast path */
		if (other == Rational.ZERO) {
			return this;
		}
		if (mBignum == null && !(other instanceof Rational.BigRational)) {
			if (mDenom == other.mDenom) {
				/* handle gcd = 0 correctly 
				 * two INFINITYs with same sign give INFINITY,
				 * otherwise it gives NAN.
				 */
				if (mDenom == 0) {
					if (mNum != other.mNum) {
						mNum = 0;
					}
				} else {
					/* a common, very simple case, e.g. for integers */
					setValue((long) mNum + other.mNum, mDenom);
				}
			} else {
				final int gcd = Rational.gcd(mDenom, other.mDenom);
				final long denomgcd = mDenom / gcd; 
				final long otherdenomgcd = other.mDenom / gcd; 
				final long newdenom = denomgcd * other.mDenom;
				final long newnum = otherdenomgcd * mNum + denomgcd * other.mNum;
				setValue(newnum, newdenom);
			}
			return this;
		}

		if (mBignum == null && mNum == 0 && mDenom == 1) {
			/* This is zero; set result to other */
			mBignum = other.numerator();
			mBigdenom = other.denominator();
			return this;
		}

		final BigInteger tdenom = denominator();
		final BigInteger odenom = other.denominator();
		if (tdenom.equals(odenom)) {
			mBignum = numerator().add(other.numerator());
			mBigdenom = tdenom; 
		} else {
			final BigInteger gcd = Rational.gcd(tdenom, odenom);
			final BigInteger tdenomgcd = tdenom.divide(gcd);
			final BigInteger odenomgcd = odenom.divide(gcd);
			mBignum = numerator().multiply(odenomgcd)
				.add(other.numerator().multiply(tdenomgcd));
			mBigdenom = tdenom.multiply(odenomgcd);
		}
		normalize();
		return this;
	}

	/**
	 * Negate this rational, i.e., this = -this.
	 * @return this mutable rational.
	 */
	public MutableRational negate() {
		if (mBignum == null) {
			if (mNum == Integer.MIN_VALUE) {
				setValue(-(long)Integer.MIN_VALUE, mDenom);
			} else {
				mNum = -mNum;
			}
		} else {
			mBignum = mBignum.negate();
		}
		return this;
	}

	/**
	 * Subtract the other rational from this.
	 * @param other the rational to subtract.
	 * @return this mutable rational.
	 */
	public MutableRational sub(Rational other) {
		return add(other.negate());
	}

	/**
	 * Multiply this rational with other and store the result in this.
	 * @param other the rational to multiply with.
	 * @return this mutable rational.
	 */
	public MutableRational mul(Rational other) {
		/* fast path */
		if (other == Rational.ONE) {
			return this;
		}
		if (other == Rational.MONE) {
			return negate();
		}
		if (mBignum == null && !(other instanceof Rational.BigRational)) {
			final long newnum = (long)mNum * other.mNum;
			final long newdenom = (long)mDenom * other.mDenom;
			setValue(newnum, newdenom);
			return this;
		}

		mBignum = numerator().multiply(other.numerator());
		mBigdenom = denominator().multiply(other.denominator());
		normalize();
		return this;
	}

	/**
	 * Divide this rational by the other and store the result in this.
	 * @param other the divisor.
	 * @return this mutable rational.
	 */
	public MutableRational div(Rational other) {
		/* fast path */
		if (other == Rational.ZERO) {
			throw new ArithmeticException("Division by ZERO");
		}
		if (mBignum == null && mNum == 0) {
			return this;
		}
		if (other == Rational.ONE) {
			return this;
		}
		if (other == Rational.MONE) {
			return negate();
		}
		if (mBignum == null && !(other instanceof Rational.BigRational)) {
			long newnum = (long)mNum * other.mDenom;
			final long newdenom = (long)mDenom * other.mNum;
			// +-inf : -c = -+inf
			if (newdenom == 0 && other.mNum < 0) {
				newnum = -newnum;
			}
			setValue(newnum, newdenom);
			return this;
		}
		mBignum = numerator().multiply(other.denominator());
		mBigdenom = denominator().multiply(other.numerator());
		// +-inf : -c = -+inf
		if (mBigdenom.equals(BigInteger.ZERO)
				&& other.numerator().signum() == -1) {
			mBignum = mBignum.negate();
		}
		normalize();
		return this;
	}

	/**
	 * Compute the multiplicative inverse of this rational and store
	 * it in this.
	 * @return this mutable rational.
	 */
	public MutableRational inverse() {
		if (mBignum == null) {
			setValue(mDenom, mNum);
		} else {
			final BigInteger tmp = mBigdenom;
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

	/**
	 * Check if this rational is negative.
	 * @return true iff {@code this < 0}.
	 */
	public boolean isNegative() {
		return numerator().signum() < 0;
	}

	/**
	 * Computes {@code this += (fac1*fac2)}.
	 * @param fac1 one of the factors.
	 * @param fac2 the other factor.
	 * @return this mutable rational.
	 */
	public MutableRational addmul(Rational fac1,Rational fac2) {
		return add(fac1.mul(fac2));
	}

	/**
	 * Computes {@code this += (fac1*fac2)}.
	 * @param fac1 one of the factors.
	 * @param fac2 the other factor.
	 * @return this mutable rational.
	 */
	public MutableRational addmul(Rational fac1,BigInteger fac2) {
		return add(fac1.mul(fac2));
	}

	/**
	 * Computes {@code this = (this - s) / d}.
	 * @param s the rational to subtract.
	 * @param d the divisor.
	 * @return this mutable rational.
	 */
	public MutableRational subdiv(Rational s,Rational d) {
		return sub(s).div(d);
	}

	@Override
	/**
	 * Compares this mutable rational with the other.
	 * @param o the other mutable rational.
	 * @return -1, if this &lt; o; 1, if this &gt; o; 0 if they are equal.
	 */
	public int compareTo(MutableRational o) {
		/* fast path */
		if (mBignum == null && o.mBignum == null) {
			/* handle infinities and nan */
			if (o.mDenom == mDenom) {
				return mNum < o.mNum ? -1 : mNum == o.mNum ? 0 : 1;
			}
			final long valt = (long)mNum * o.mDenom;
			final long valo = (long)o.mNum * mDenom;
			return valt < valo ? -1 : valt == valo ? 0 : 1; 
		}
		final BigInteger valthis = numerator().multiply(o.denominator());
		final BigInteger valo = o.numerator().multiply(denominator());
		return valthis.compareTo(valo);
	}

	/**
	 * Compares this mutable rational with the other.
	 * @param o the other rational.
	 * @return -1, if this &lt; o; 1, if this &gt; o; 0 if they are equal.
	 */
	public int compareTo(Rational o) {
		/* fast path */
		if (mBignum == null && !(o instanceof BigRational)) {
			/* handle infinities and nan */
			if (o.mDenom == mDenom) {
				return mNum < o.mNum ? -1 : mNum == o.mNum ? 0 : 1;
			}
			final long valt = (long)mNum * o.mDenom;
			final long valo = (long)o.mNum * mDenom;
			return valt < valo ? -1 : valt == valo ? 0 : 1; 
		}
		final BigInteger valthis = numerator().multiply(o.denominator());
		final BigInteger valo = o.numerator().multiply(denominator());
		return valthis.compareTo(valo);
	}

	/**
	 * Compares this mutable rational with the other.  This works with
	 * MutableRational and Rational.
	 * @param o the other rational.
	 * @return true if this equals o, false otherwise.
	 */
	@Override
	public boolean equals(Object o) {
		if (o instanceof Rational) {
			final Rational r = (Rational) o;
			// Works thanks to normalization!!!
			return mBignum == null
				? !(r instanceof Rational.BigRational)
					&& mNum == r.mNum && mDenom == r.mDenom
				: mBignum.equals(r.numerator())
					&& mBigdenom.equals(r.denominator());
		}
		if (o instanceof MutableRational) {
			final MutableRational r = (MutableRational) o;
			// Works thanks to normalization!!!
			return mBignum == null
				? r.mBignum == null && mNum == r.mNum && mDenom == r.mDenom
				: mBignum.equals(r.mBignum) && mBigdenom.equals(r.mBigdenom);
		}
		return false;
	}

	/**
	 * Get the numerator of this rational.
	 * @return the numerator.
	 */
	public BigInteger numerator() {
		return mBignum == null ? BigInteger.valueOf(mNum) : mBignum;
	}

	/**
	 * Get the denominator of this rational.
	 * @return the denominator.
	 */
	public BigInteger denominator() {
		return mBigdenom == null ? BigInteger.valueOf(mDenom) : mBigdenom;
	}

	/**
	 * Computes a hashcode.  The hashcode is computed as 
	 * {@code 257 * numerator + denominator} if both fit into an integer and
	 * {@code 257 * numerator().hashCode() + denominator().hashCode()} if big
	 * integers are necessary.
	 * @return the hashcode.
	 */
	@Override
	public int hashCode() {
		if (mBignum == null) {
			return mNum * 257 + mDenom;
		} else {
			return mBignum.hashCode() * 257 + mBigdenom.hashCode();
		}
	}

	/**
	 * Get a string representation of this number.  This is
	 * {@code numerator()+ "/" + denominator()} except for
	 * infinity ({@code "inf"}), nan ({@code "nan"}), or minus 
	 * infinity ({@code "-inf"}).
	 * @return the string representation.
	 */
	@Override
	public String toString() {
		/* fast path */
		if (mBignum == null) {
			if (mDenom == 0) {
				return mNum > 0 ? "inf" : mNum == 0 ? "nan" : "-inf";
			}
			if (mDenom == 1) {
				return String.valueOf(mNum);
			}
			return mNum + "/" + mDenom;
		} else {
			if (mBigdenom.equals(BigInteger.ONE)) {
				return mBignum.toString();
			}
			return mBignum + "/" + mBigdenom;
		}
	}

	/**
	 * Check whether this rational represents an integral value. Both infinity
	 * values are treated as integral.
	 * @return {@code true} iff value is integral.
	 */
	public boolean isIntegral() {
		return (mBignum == null)
				? mDenom <= 1 : mBigdenom.equals(BigInteger.ONE);
	}

	/**
	 * Convert this mutable rational into a immutable rational.
	 * @return the rational.
	 */
	public Rational toRational() {
		if (mBignum == null) {
			return Rational.valueOf(mNum, mDenom);
		}
		return Rational.valueOf(numerator(), denominator());
	}

	/**
	 * Compute sign of this rational.  This is equivalent to
	 * {@code compare(Rational.ZERO)}.
	 * @return the sign of the rational, +1 for positive, 0 for 0 and
	 * -1 for negative.
	 */
	public int signum() {
		if (mBignum == null) {
			return mNum < 0 ? -1 : mNum == 0 ? 0 : 1;
		}
		return mBignum.signum();
	}
}
