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
 * Class that represents a rational number num/denom,
 * where num and denom are BigInteger.  This class also handles
 * infinity and NAN.
 *
 * Internally, the numbers are always kept in reduced form; the
 * denominator is always kept non-negative.  A zero denominator
 * with non-zero numerator indicates positive or negative infinity.
 * The number 0/0 is used to represent NAN (not a number).
 *
 * Every operation that involves NAN gives NAN as result.
 * The non-obvious rules for ZERO, INFINITY, and NAN are:
 * <pre>
 * ONE.div(NEGATIVE_INFINITY).isNegative() = false  (no negative ZERO)
 * ZERO.inverse() = POSITIVE_INFINITY
 * POSITIVE_INFINITY.add(finite number) = POSITIVE_INFINITY.
 * POSITIVE_INFINITY.add(NEGATIVE_INFINITY) = NAN
 * ZERO.mul(POSITIVE_INFINITY) = ZERO.mul(NEGATIVE_INFINITY) = NAN
 * number.div(ZERO) = POSITIVE_INFINITY.mul(number.signum())
 * NAN.isIntegral = POSITIVE_INFINITY.isIntegral = true
 * NAN.floor() = NAN;
 * POSITIVE_INFINITY.floor() = POSITIVE_INFINITY;
 * NAN.frac() = POSITIVE_INFINITY.frac() = ZERO;
 * </pre>
 *
 * This class only uses bigintegers if either numerator or
 * denominator does not fit into an int.
 * @author Juergen Christ, Jochen Hoenicke
 */
public class Rational implements Comparable<Rational> {
	/**
	 * The numerator if num and denom are in int range.
	 */
	int mNum;
	/**
	 * The denominator if num and denom are in int range.
	 */
	int mDenom;

	static class BigRational extends Rational {
		/**
		 * The numerator if num or denom is outside int range.
		 */
		BigInteger mBignum;
		/**
		 * The denominator if num or denom is outside int range.
		 */
		BigInteger mBigdenom;

		/**
		 * Construct a rational from two bigints.  The constructor
		 * is private and does not normalize.  Use the static
		 * constructor valueOf instead.
		 * @param nom   Numerator
		 * @param denom Denominator
		 */
		private BigRational(final BigInteger nom,final BigInteger denom) {
			super(nom.signum(),1);
			mBignum = nom;
			mBigdenom = denom;
		}

		/**
		 * Return a new rational representing <code>this + other</code>.
		 * @param other Rational to add.
		 * @return Sum of <code>this</code> and <code>other</code>.
		 */
		@Override
		public Rational add(final Rational other) {
			/* fast path */
			if (other == Rational.ZERO) {
				return this;
			}

			final BigInteger tdenom = denominator();
			final BigInteger odenom = other.denominator();
			if (tdenom.equals(odenom)) {
				/* another very simple case */
				return valueOf(numerator().add(other.numerator()), tdenom);
			}
			final BigInteger gcd = tdenom.gcd(odenom);
			final BigInteger tdenomgcd = tdenom.divide(gcd);
			final BigInteger odenomgcd = odenom.divide(gcd);
			final BigInteger newnum = numerator().multiply(odenomgcd)
				.add(other.numerator().multiply(tdenomgcd));
			final BigInteger newdenom = tdenom.multiply(odenomgcd);
			return valueOf(newnum, newdenom);
		}

		/**
		 * Returns a new rational equal to <code>-this</code>.
		 * @return <code>-this</code>
		 */
		@Override
		public Rational negate() {
			return Rational.valueOf(mBignum.negate(), mBigdenom);
		}

		/**
		 * Return a new rational representing <code>this * other</code>.
		 * @param other Rational to multiply.
		 * @return Product of <code>this</code> and <code>other</code>.
		 */
		@Override
		public Rational mul(final Rational other) {
			/* fast path */
			if (other == Rational.ONE) {
				return this;
			}
			if (other == Rational.ZERO) {
				return other;
			}
			if (other == Rational.MONE) {
				return negate();
			}

			final BigInteger newnum = numerator().multiply(other.numerator());
			final BigInteger newdenom = denominator().multiply(other.denominator());
			return valueOf(newnum, newdenom);
		}

		/**
		 * Return a new rational representing <code>this * other</code>.
		 * @param other big integer to multiply.
		 * @return Product of <code>this</code> and <code>other</code>.
		 */
		@Override
		public Rational mul(final BigInteger other) {
			if (other.bitLength() < 2) {
				/* fast path */
				final int oint = other.intValue();
				if (oint == 1) {
					return this;
				}
				if (oint == -1) {
					return negate();
				}
				if (oint == 0) {
					return Rational.ZERO;
				}
			}
			return valueOf(numerator().multiply(other), denominator());
		}

		/**
		 * Return a new rational representing <code>this / other</code>.
		 * @param other Rational to divide.
		 * @return Quotient of <code>this</code> and <code>other</code>.
		 */
		@Override
		public Rational div(final Rational other) {
			if (other == Rational.ONE) {
				return this;
			}
			if (other == Rational.MONE) {
				return negate();
			}
			final BigInteger denom = denominator().multiply(other.numerator());
			BigInteger nom = numerator().multiply(other.denominator());
			// +-inf : -c = -+inf
			if (denom.equals(BigInteger.ZERO)
					&& other.numerator().signum() == -1) {
				nom = nom.negate();
			}
			return valueOf(nom,denom);
		}

		/**
		 * Return a new rational representing <code>this / other</code>.
		 * @param other Rational to divide.
		 * @return Quotient of <code>this</code> and <code>other</code>.
		 */
		public Rational idiv(final Rational other) {
			BigInteger num = denominator().multiply(other.numerator());
			final BigInteger denom = numerator().multiply(other.denominator());
			// +-inf : -c = -+inf
			if (denom.equals(BigInteger.ZERO) && numerator().signum() == -1) {
				num = num.negate();
			}
			return valueOf(num,denom);
		}

		/**
		 * Returns a new rational representing the inverse of <code>this</code>.
		 * @return Inverse of <code>this</code>.
		 */
		@Override
		public Rational inverse() {
			return valueOf(mBigdenom, mBignum);
		}

		/**
		 * Compute the gcd of two rationals (this and other).  The gcd
		 * is the rational number, such that dividing this and other with
		 * the gcd will yield two co-prime integers.
		 * @param other the second rational argument.
		 * @return the gcd of this and other.
		 */
		@Override
		public Rational gcd(final Rational other) {
			if (other == Rational.ZERO) {
				return this;
			}
			final BigInteger tdenom = denominator();
			final BigInteger odenom = other.denominator();
			final BigInteger gcddenom = tdenom.gcd(odenom);
			final BigInteger denom = tdenom.divide(gcddenom).multiply(odenom);
			final BigInteger num = numerator().gcd(other.numerator());
			return Rational.valueOf(num, denom);
		}

		@Override
		public int compareTo(final Rational o) {
			final BigInteger valthis = numerator().multiply(o.denominator());
			final BigInteger valo = o.numerator().multiply(denominator());
			return valthis.compareTo(valo);
		}

		@Override
		public boolean equals(final Object o) {
			if (o instanceof BigRational) {
				final BigRational r = (BigRational) o;
				// Works thanks to normalization!!!
				return mBignum.equals(r.mBignum)
					&& mBigdenom.equals(r.mBigdenom);
			}
			if (o instanceof MutableRational) {
				return ((MutableRational) o).equals(this);
			}
			return false;
		}

		@Override
		public BigInteger numerator() {
			return mBignum;
		}
		@Override
		public BigInteger denominator() {
			return mBigdenom;
		}

		@Override
		public int hashCode() {
			return mBignum.hashCode() * 257 + mBigdenom.hashCode();
		}

		@Override
		public String toString() {
			if (mBigdenom.equals(BigInteger.ONE)) {
				return mBignum.toString();
			}
			return mBignum.toString() + "/" + mBigdenom.toString();
		}

		/**
		 * Check whether this rational represents an integral value. Both
		 * infinity values are treated as integral.
		 * @return <code>true</code> iff value is integral.
		 */
		@Override
		public boolean isIntegral() {
			return mBigdenom.equals(BigInteger.ONE);
		}
		/**
		 * Return a new rational representing the biggest integral rational not
		 * bigger than <code>this</code>.
		 * @return Next smaller integer of <code>this</code>.
		 */
		@Override
		public Rational floor() {
			if (denominator().equals(BigInteger.ONE)) {
				return this;
			}
			BigInteger div = numerator().divide(denominator());
			if (numerator().signum() < 0) {
				div = div.subtract(BigInteger.ONE);
			}
			return Rational.valueOf(div,BigInteger.ONE);
		}
		/**
		 * Returns the fractional part of the rational, i.e. the
		 * number this.sub(this.floor()).
		 * @return Next smaller integer of <code>this</code>.
		 */
		@Override
		public Rational frac() {
			if (mBigdenom.equals(BigInteger.ONE)) {
				return Rational.ZERO;
			}
			BigInteger newnum = mBignum.mod(mBigdenom);
			if (newnum.signum() < 0) {
				newnum = newnum.add(mBigdenom);
			}
			return Rational.valueOf(newnum, mBigdenom);
		}
		/**
		 * Return a new rational representing the smallest integral rational not
		 * smaller than <code>this</code>.
		 * @return Next bigger integer of <code>this</code>.
		 */
		@Override
		public Rational ceil() {
			if (denominator().equals(BigInteger.ONE)) {
				return this;
			}
			BigInteger div = numerator().divide(denominator());
			if (numerator().signum() > 0) {
				div = div.add(BigInteger.ONE);
			}
			return Rational.valueOf(div,BigInteger.ONE);
		}
		@Override
		public Rational abs() {
			return valueOf(mBignum.abs(), mBigdenom);
		}
	}

	/**
	 * Construct a rational from two ints.  The constructor
	 * is private and does not normalize.  Use the static
	 * constructor valueOf instead.
	 * @param num   The numerator.
	 * @param denom The denominator.
	 */
	private Rational(final int num, final int denom) {
		mNum = num;
		mDenom = denom;
	}

	/**
	 * Construct a rational from two bigints.  Use this method
	 * to create a rational number if the numerator or denominator
	 * may be to big to fit in an int.  This method normalizes
	 * the rational number and does partial unification.
	 *
	 * @param bignum   The numerator.
	 * @param bigdenom The denominator.
	 * @return a rational representing numerator/denominator.
	 */
	public static Rational valueOf(BigInteger bignum, BigInteger bigdenom) {
		final int cp = bigdenom.signum();
		if (cp < 0) {
			bignum = bignum.negate();
			bigdenom = bigdenom.negate();
		} else if (cp == 0) {
			return valueOf(bignum.signum(), 0);
		}
		if (!bigdenom.equals(BigInteger.ONE)) {
			final BigInteger norm = gcd(bignum, bigdenom).abs();
			if (!norm.equals(BigInteger.ONE)) {
				bignum = bignum.divide(norm);
				bigdenom = bigdenom.divide(norm);
			}
		}
		if (bigdenom.bitLength() < 32 && bignum.bitLength() < 32) {
			return valueOf(bignum.intValue(), bigdenom.intValue());
		} else {
			return new BigRational(bignum, bigdenom);
		}
	}

	/**
	 * Construct a rational from two longs.  Use this method
	 * to create a rational number.  This method normalizes
	 * the rational number and may return a previously created
	 * one.
	 * This method does not work if called with value
	 * Long.MIN_VALUE.
	 *
	 * @param newnum   The numerator.
	 * @param newdenom The denominator.
	 * @return a rational representing numerator/denominator.
	 */
	public static Rational valueOf(long newnum, long newdenom) {
		if (newdenom != 1) {
			long gcd2 = Math.abs(gcd(newnum, newdenom));
			if (gcd2 == 0) {
				return NAN;
			}
			if (newdenom < 0) {
				gcd2 = -gcd2;
			}
			newnum /= gcd2;
			newdenom /= gcd2;
		}

		if (newdenom == 1) {
			if (newnum == 0) {
				return ZERO;
			}
			if (newnum == 1) {
				return ONE;
			}
			if (newnum == -1) {
				return MONE;
			}
		} else if (newdenom == 0) {
			if (newnum == 1) {
				return POSITIVE_INFINITY;
			} else {
				return NEGATIVE_INFINITY;
			}
		}

		if (Integer.MIN_VALUE <= newnum && newnum <= Integer.MAX_VALUE
			&& newdenom <= Integer.MAX_VALUE) {
			return new Rational((int) newnum, (int) newdenom);
		}
		return new BigRational(BigInteger.valueOf(newnum),
				BigInteger.valueOf(newdenom));
	}

	/**
	 * Calculates the greatest common divisor of two numbers. Expects two
	 * nonnegative values.
	 * @param a First number
	 * @param b Second Number
	 * @return Greatest common divisor
	 */
	static int gcd(int a,int b) {
		/* This is faster for integer */
		//assert(a >= 0 && b >= 0);
		while (b != 0) {
			final int t = a % b;
			a = b;
			b = t;
		}
		return a;
	}

	/**
	 * Calculates the greatest common divisor of two numbers.
	 * @param a First number
	 * @param b Second Number
	 * @return Greatest common divisor
	 */
	static long gcd(long a,long b) {
		/* This is faster for longs on 32-bit architectures */
		if (a < 0) {
			a = -a;
		}
		if (b < 0) {
			b = -b;
		}
		if (a == 0 || b == 1) {
			return b;
		}
		if (b == 0 || a == 1) {
			return a;
		}
		final int ashift = Long.numberOfTrailingZeros(a);
		final int bshift = Long.numberOfTrailingZeros(b);
		a >>= ashift;
		b >>= bshift;
		while (a != b) {
			long t;
			if (a < b) {
				t = b - a;
				b = a;
			} else {
				if (b == 1) {
					a = b;
					break;
				}
				t = a - b;
			}
			do {
				t >>= 1;
			} while (((int) t & 1) == 0);
			a = t;
		}
		return a << Math.min(ashift, bshift);
	}

	/**
	 * Compute the gcd of two BigInteger.  This is the same
	 * as {@code i1.gcd(i2)}, but it is more efficient for small numbers.
	 * @param i1 the first big integer.
	 * @param i2 the second big integer.
	 * @return the gcd of i1 and i2.
	 */
	public static BigInteger gcd(final BigInteger i1, final BigInteger i2) {
		if (i1.equals(BigInteger.ONE) || i2.equals(BigInteger.ONE)) {
			return BigInteger.ONE;
		}
		final int l1 = i1.bitLength();
		final int l2 = i2.bitLength();
		if (l1 < 31 && l2 < 31) {
			return BigInteger.valueOf(gcd(i1.intValue(), i2.intValue()));
		} else if (l1 < 63 && l2 < 63) {
			return BigInteger.valueOf(gcd(i1.longValue(), i2.longValue()));
		} else {
			return i1.gcd(i2);
		}
	}

	/**
	 * Return a new rational representing <code>this + other</code>.
	 * @param other Rational to add.
	 * @return Sum of <code>this</code> and <code>other</code>.
	 */
	public Rational add(final Rational other) {
		/* fast path */
		if (other == Rational.ZERO) {
			return this;
		}
		if (this == Rational.ZERO) {
			return other;
		}
		if (other instanceof BigRational) {
			return other.add(this);
		} else {
			if (mDenom == other.mDenom) {
				/* handle gcd = 0 correctly
				 * two INFINITYs with same sign give INFINITY,
				 * otherwise it gives NAN.
				 */
				if (mDenom == 0) {
					return mNum == other.mNum ? this : NAN;
				}
				/* a common, very simple case, e.g. for integers */
				return valueOf((long) mNum + other.mNum, mDenom);
			}
			/* This also handles infinity/NAN + normal correctly. */
			final int gcd = gcd(mDenom, other.mDenom);
			final long denomgcd = mDenom / gcd;
			final long otherdenomgcd = other.mDenom / gcd;
			final long newdenom = denomgcd * other.mDenom;
			final long newnum = otherdenomgcd * mNum + denomgcd * other.mNum;
			return valueOf(newnum, newdenom);
		}
	}

	/**
	 * Computes {@code this + (fac1*fac2)}.
	 * @param fac1 one of the factors.
	 * @param fac2 the other factor.
	 * @return the result of the computation.
	 */
	public Rational addmul(final Rational fac1,final Rational fac2) {
		return add(fac1.mul(fac2));
	}

	/**
	 * Computes {@code (this - s) / d}.
	 * @param s the rational to subtract.
	 * @param d the divisor.
	 * @return the result of the computation.
	 */
	public Rational subdiv(final Rational s,final Rational d) {
		return sub(s).div(d);
	}
	/**
	 * Returns a new rational equal to <code>-this</code>.
	 * @return <code>-this</code>.
	 */
	public Rational negate() {
		return Rational.valueOf(-(long)mNum, mDenom);
	}
	/**
	 * Return a new rational representing <code>this - other</code>.
	 * @param other Rational to subtract.
	 * @return Difference of <code>this</code> and <code>other</code>.
	 */
	public Rational sub(final Rational other) {
		return add(other.negate());
	}
	/**
	 * Return a new rational representing <code>this * other</code>.
	 * @param other Rational to multiply.
	 * @return Product of <code>this</code> and <code>other</code>.
	 */
	public Rational mul(final Rational other) {
		/* fast path */
		if (other == Rational.ONE) {
			return this;
		}
		if (this == Rational.ONE) {
			return other;
		}
		if (other == Rational.MONE) {
			return negate();
		}
		if (this == Rational.MONE) {
			return other.negate();
		}
		if (other instanceof BigRational) {
			return other.mul(this);
		}

		final long newnum = (long)mNum * other.mNum;
		final long newdenom = (long)mDenom * other.mDenom;
		return valueOf(newnum, newdenom);
	}

	/**
	 * Return a new rational representing <code>this * other</code>.
	 * @param other big integer to multiply.
	 * @return Product of <code>this</code> and <code>other</code>.
	 */
	public Rational mul(final BigInteger other) {
		if (other.bitLength() < 32) { // NOCHECKSTYLE
			/* fast path */
			final int oint = other.intValue();
			if (oint == 1) {
				return this;
			}
			if (oint == -1) {
				return negate();
			}
			final long newnum = (long)mNum * oint;
			return valueOf(newnum, mDenom);
		}

		if (this == Rational.ONE) {
			return valueOf(other, BigInteger.ONE);
		}
		if (this == Rational.MONE) {
			return valueOf(other.negate(), BigInteger.ONE);
		}

		return valueOf(numerator().multiply(other), denominator());
	}
	/**
	 * Return a new rational representing <code>this / other</code>.
	 * @param other Rational to divide.
	 * @return Quotient of <code>this</code> and <code>other</code>.
	 */
	public Rational div(final Rational other) {
		if (other == Rational.ONE) {
			return this;
		}
		if (other == Rational.MONE) {
			return negate();
		}

		if (other instanceof BigRational) {
			return ((BigRational)other).idiv(this);
		}

		/* fast path */
		long newnum = (long)mNum * other.mDenom;
		final long newdenom = (long)mDenom * other.mNum;
		// +-inf : -c = -+inf
		if (newdenom == 0 && other.mNum < 0) {
			newnum = -newnum;
		}
		return valueOf(newnum, newdenom);
	}

	/**
	 * Compute the gcd of two rationals (this and other).  The gcd
	 * is the rational number, such that dividing this and other with
	 * the gcd will yield two co-prime integers.
	 * @param other the second rational argument.
	 * @return the gcd of this and other.
	 */
	public Rational gcd(final Rational other) {
		if (this == Rational.ZERO) {
			return other;
		}
		if (other == Rational.ZERO) {
			return this;
		}
		if (other instanceof BigRational) {
			return other.gcd(this);
		}
		/* new numerator = gcd(num, other.num) */
		/* new denominator = lcm(denom, other.denom) */
		final int gcddenom = gcd(mDenom, other.mDenom);
		final long denom = ((long) (mDenom / gcddenom)) * other.mDenom;
		final long num = gcd(mNum < 0 ? -mNum : mNum,
				other.mNum < 0 ? -other.mNum : other.mNum);
		return valueOf(num, denom);
	}
	/**
	 * Returns a new rational representing the inverse of <code>this</code>.
	 * @return Inverse of <code>this</code>.
	 */
	public Rational inverse() {
		return valueOf(mDenom, mNum);
	}

	/**
	 * Check whether this rational is negative.
	 * @return <code>true</code> iff this rational is negative.
	 */
	public boolean isNegative() {
		return mNum < 0;
	}
	/**
	 * Return the sign of this rational.  The sign will be -1, 0, or 1 if this
	 * rational is negative, zero, or positive.
	 * @return The sign of this rational.
	 */
	public int signum() {
		return mNum < 0 ? -1 : mNum == 0 ? 0 : 1;
	}

	@Override
	/**
	 * Compares this rational with the other.
	 * @param o the other rational.
	 * @return -1, if this &lt; o; 1, if this &gt; o; 0 if they are equal.
	 */
	public int compareTo(final Rational o) {
		if (o instanceof BigRational) {
			return -o.compareTo(this);
		}

		/* handle infinities and nan */
		if (o.mDenom == mDenom) {
			return mNum < o.mNum ? -1 : mNum == o.mNum ? 0 : 1;
		}
		final long valt = (long)mNum * o.mDenom;
		final long valo = (long)o.mNum * mDenom;
		return valt < valo ? -1 : valt == valo ? 0 : 1;
	}
	@Override
	/**
	 * Compares this rational with the other.  This works with
	 * Rational and MutableRational.
	 * @param o the other rational.
	 * @return true if this equals o, false otherwise.
	 */
	public boolean equals(final Object o) {
		if (o instanceof Rational) {
			if (o instanceof BigRational) {
				return false;
			}
			final Rational r = (Rational) o;
			// Works thanks to normalization!!!
			return mNum == r.mNum && mDenom == r.mDenom;
		}
		if (o instanceof MutableRational) {
			return ((MutableRational) o).equals(this);
		}
		return false;
	}

	/**
	 * Get the numerator of this rational.
	 * @return the numerator.
	 */
	public BigInteger numerator() {
		return BigInteger.valueOf(mNum);
	}

	/**
	 * Get the denominator of this rational.
	 * @return the denominator.
	 */
	public BigInteger denominator() {
		return BigInteger.valueOf(mDenom);
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
		return mNum * 257 + mDenom;
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
		if (mDenom == 0) {
			return mNum > 0 ? "inf" : mNum == 0 ? "nan" : "-inf";
		}
		if (mDenom == 1) {
			return String.valueOf(mNum);
		}
		return mNum + "/" + mDenom;
	}
	/**
	 * Check whether this rational represents an integral value. Both infinity
	 * values are treated as integral.
	 * @return <code>true</code> iff value is integral.
	 */
	public boolean isIntegral() {
		return mDenom <= 1;
	}
	/**
	 * Return a new rational representing the biggest integral rational not
	 * bigger than <code>this</code>.
	 * @return Next smaller integer of <code>this</code>.
	 */
	public Rational floor() {
		if (mDenom <= 1) {
			return this;
		}
		int div = mNum / mDenom;
		// Java rounds the wrong way for negative numbers.
		// We know that the division is not exact due to
		// normalization and mdenom != 1, so subtracting
		// one fixes the result for negative numbers.
		if (mNum < 0) {
			div--;
		}
		return valueOf(div, 1);
	}
	/**
	 * Returns the fractional part of the rational, i.e. the
	 * number this.sub(this.floor()).
	 * @return Next smaller integer of <code>this</code>.
	 */
	public Rational frac() {
		if (mDenom <= 1) {
			return Rational.ZERO;
		}
		int newnum = mNum % mDenom;
		// Java rounds the wrong way for negative numbers.
		// We know that the division is not exact due to
		// normalization and mdenom != 1, so subtracting
		// one fixes the result for negative numbers.
		if (newnum < 0) {
			newnum += mDenom;
		}
		return valueOf(newnum, mDenom);
	}
	/**
	 * Return a new rational representing the smallest integral rational not
	 * smaller than <code>this</code>.
	 * @return Next bigger integer of <code>this</code>.
	 */
	public Rational ceil() {
		if (mDenom <= 1) {
			return this;
		}
		int div = mNum / mDenom;
		// Java rounds the wrong way for positive numbers.
		// We know that the division is not exact due to
		// normalization and mdenom != 1, so adding
		// one fixes the result for positive numbers.
		if (mNum > 0) {
			div++;
		}
		return valueOf(div, 1);
	}
	/**
	 * Compute the absolute of this rational.
	 * @return Rational that is equal to the absolute value of this rational.
	 */
	public Rational abs() {
		return valueOf(Math.abs((long) mNum), mDenom);
	}

	/**
	 * Positive infinity.  Used to represent the result of 1/0.
	 */
	public final static Rational POSITIVE_INFINITY = new Rational(1,0);
	/**
	 * Not a number.  Used to represent the result of 0/0.
	 */
	public final static Rational NAN = new Rational(0,0);
	/**
	 * Negative infinity.  Used to represent the result of -1/0.
	 */
	public final static Rational NEGATIVE_INFINITY = new Rational(-1,0);
	/**
	 * The number 0.
	 */
	public final static Rational ZERO = new Rational(0,1);
	/**
	 * The number 1.
	 */
	public final static Rational ONE = new Rational(1,1);
	/**
	 * The number -1.
	 */
	public final static Rational MONE = new Rational(-1,1);
	/**
	 * The number 2.
	 */
	public static final Rational TWO = new Rational(2,1);

	/**
	 * Creates a constant term containing this rational.
	 * @param sort the sort of the constant term that should be created.
	 * @return a constant term with this rational value.
	 * @throws SMTLIBException if term is infinite or NaN, if the
	 * sort is not numeric, or if the term is not integral and the sort
	 * is Int.
	 */
	public Term toTerm(final Sort sort) {
		return sort.getTheory().constant(this, sort);
	}
	/**
	 * Convert this rational into an SMTLIB term.
	 * @param t Theory to use during conversion.
	 * @return SMTLIB term corresponding to this rational.
	 * @deprecated Use {@link #toTerm(Sort)} since this is the type-safe version
	 */
	@Deprecated
	public Term toSMTLIB(final Theory t) {
		return t.rational(numerator(), denominator());
	}
	/**
	 * Check whether this rational corresponds to a (finite) rational value.
	 * This function can be used to test for infinites and NaNs.
	 * @return true if and only if this rational is not infinite or NaN.
	 */
	public boolean isRational() {
		return mDenom != 0;
	}
}
