package local.stalin.smt.theory.linar;

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
public final class Rational implements Comparable<Rational> {
	/** 
	 * The numerator if num and denom are in int range.
	 */
	int mnum;
	/** 
	 * The denominator if num and denom are in int range.
	 */
	int mdenom;
	/** 
	 * The numerator if num or denom is outside int range.
	 */
	BigInteger mbignum;
	/** 
	 * The denominator if num or denom is outside int range.
	 */
	BigInteger mbigdenom;
	/**
	 * Construct a rational from two ints.  The constructor
	 * is private and does not normalize.  Use the static
	 * constructor valueOf instead. 
	 * @param nom   Numerator
	 * @param denom Denominator
	 */
	private Rational(int nom, int denom) {
		mnum = nom;
		mdenom = denom;
		mbignum = mbigdenom = null;
	}
	/**
	 * Construct a rational from two bigints.  The constructor
	 * is private and does not normalize.  Use the static
	 * constructor valueOf instead. 
	 * @param nom   Numerator
	 * @param denom Denominator
	 */
	private Rational(BigInteger nom,BigInteger denom) {
		mbignum = nom;
		mbigdenom = denom;
	}

	/**
	 * Construct a rational from two bigints.  Use this method
	 * to create a rational number if the numerator or denominator
	 * may be to big to fit in an int.  This method normalizes
	 * the rational number.  
	 *   
	 * @param nom   Numerator
	 * @param denom Denominator
	 */
	public static Rational valueOf(BigInteger mbignum, BigInteger mbigdenom) {
		int cp = mbigdenom.compareTo(BigInteger.ZERO);
		if( cp < 0 ) {
			mbignum = mbignum.negate();
			mbigdenom = mbigdenom.negate();
		} else if (cp == 0) {
			return valueOf(mbignum.signum(), 0); 
		}
		BigInteger norm = mbignum.gcd(mbigdenom);
		if (!norm.equals(BigInteger.ONE)) {
			mbignum = mbignum.divide(norm);
			mbigdenom = mbigdenom.divide(norm);
		}
		if( mbigdenom.bitLength() < 32 && mbignum.bitLength() < 32 )
			return valueOf(mbignum.intValue(), mbigdenom.intValue());
		else
			return new Rational(mbignum, mbigdenom);
	}
	
	/**
	 * Construct a rational from two longs.  Use this method
	 * to create a rational number.  This method normalizes
	 * the rational number and may return a previously created
	 * one.   
	 * This method does not work if called with value 
	 * Long.MIN_VALUE.
	 *   
	 * @param nom   Numerator.
	 * @param denom Denominator.
	 */
	public static Rational valueOf(long newnum, long newdenom) {
		if (newdenom != 1) {
			long gcd2 = gcd(Math.abs(newnum), Math.abs(newdenom));
			if (gcd2 == 0)
				return NAN;
			if (newdenom < 0)
				gcd2 = -gcd2;
			newnum /= gcd2;
			newdenom /= gcd2;
		}
		
		if (newdenom == 1) {
			if (newnum == 0)
				return ZERO;
			if (newnum == 1)
				return ONE;
			if (newnum == -1)
				return MONE;
		} else if (newdenom == 0) {
			if (newnum == 1)
				return POSITIVE_INFINITY;
			else
				return NEGATIVE_INFINITY;
		}
		
		if (Integer.MIN_VALUE <= newnum && newnum <= Integer.MAX_VALUE
			&& newdenom <= Integer.MAX_VALUE)
			return new Rational((int) newnum, (int) newdenom);
		return new Rational(BigInteger.valueOf(newnum), 
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
		assert(a >= 0 && b >= 0);
		while (b != 0) {
			int t = a % b;
			a = b;
			b = t;
		}
		return a;
	}
	/**
	 * Calculates the greatest common divisor of two numbers. Expects two 
	 * nonnegative values.
	 * @param a First number
	 * @param b Second Number
	 * @return Greatest common divisor
	 */
	static long gcd(long a,long b) {
		/* This is faster for longs on 32-bit architectures */
		assert(a >= 0 && b >= 0);
		if (a == 0)
			return b;
		if (b == 0)
			return a;
		int ashift = Long.numberOfTrailingZeros(a);
		int bshift = Long.numberOfTrailingZeros(b);
		a >>= ashift;
		b >>= bshift;
		while (a != b) {
			long t;
			if (a < b) {
				t = b - a;
				b = a;
			} else {
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
	 * Return a new rational representing <code>this + other</code>.
	 * @param other Rational to add.
	 * @return Sum of <code>this</code> and <code>other</code>.
	 */
	public Rational add(Rational other) {
		/* fast path */
		if (other == Rational.ZERO)
			return this;
		if (this == Rational.ZERO)
			return other;
		if (mbignum == null && other.mbignum == null) {
			if (mdenom == other.mdenom) {
				/* handle gcd = 0 correctly 
				 * two INFINITYs with same sign give INFINITY,
				 * otherwise it gives NAN.
				 */
				if (mdenom == 0)
					return mnum == other.mnum ? this : NAN;
				/* a common, very simple case, e.g. for integers */
				return valueOf((long) mnum + other.mnum, mdenom);
			}
			/* This also handles infinity/NAN + normal correctly. */
			int gcd = gcd(mdenom, other.mdenom);
			long denomgcd = (long) (mdenom / gcd); 
			long otherdenomgcd = (long) (other.mdenom / gcd); 
			long newdenom = denomgcd * other.mdenom;
			long newnum = otherdenomgcd * mnum + denomgcd * other.mnum;
			return valueOf(newnum, newdenom);
		}
		
		BigInteger tdenom = denominator();
		BigInteger odenom = other.denominator();
		if (tdenom.equals(odenom)) {
			/* another very simple case */
			return valueOf(numerator().add(other.numerator()), tdenom);
		}
		BigInteger gcd = tdenom.gcd(odenom);
		BigInteger tdenomgcd = tdenom.divide(gcd);
		BigInteger odenomgcd = odenom.divide(gcd);
		BigInteger newnum = numerator().multiply(odenomgcd)
			.add(other.numerator().multiply(tdenomgcd));
		BigInteger newdenom = tdenom.multiply(odenomgcd);
		return valueOf(newnum, newdenom);
	}
	
	/**
	 * Returns <code>this+(fac1*fac2)</code>
	 * @param fac1
	 * @param fac2
	 * @return
	 */
	public Rational addmul(Rational fac1,Rational fac2) {
		return add(fac1.mul(fac2));
	}
	/**
	 * Returns <code>(this-s)/d</code>
	 * @param s
	 * @param d
	 * @return
	 */
	public Rational subdiv(Rational s,Rational d) {
		return sub(s).div(d);
	}
	/**
	 * Returns a new rational equal to <code>-this</code>.
	 * @return <code>-this</code>
	 */
	public Rational negate() {
		/* fast path */
		if (mbignum == null)
			return Rational.valueOf(-(long)mnum, mdenom);		
		return Rational.valueOf(mbignum.negate(), mbigdenom);
	}
	/**
	 * Return a new rational representing <code>this - other</code>.
	 * @param other Rational to subtract.
	 * @return Difference of <code>this</code> and <code>other</code>.
	 */
	public Rational sub(Rational other) {
		return add(other.negate());
	}
	/**
	 * Return a new rational representing <code>this * other</code>.
	 * @param other Rational to multiply.
	 * @return Product of <code>this</code> and <code>other</code>.
	 */
	public Rational mul(Rational other) {
		/* fast path */
		if (other == Rational.ONE)
			return this;
		if (this == Rational.ONE)
			return other;
		if (other == Rational.MONE)
			return this.negate();
		if (this == Rational.MONE)
			return other.negate();
		if (mbignum == null && other.mbignum == null) {
			long newnum = (long)mnum * other.mnum;
			long newdenom = (long)mdenom * other.mdenom;
			return valueOf(newnum, newdenom);
		}

		BigInteger newnum = numerator().multiply(other.numerator());
		BigInteger newdenom = denominator().multiply(other.denominator());
		return valueOf(newnum, newdenom);
	}
	
	/**
	 * Return a new rational representing <code>this / other</code>.
	 * @param other Rational to divide.
	 * @return Quotient of <code>this</code> and <code>other</code>.
	 */
	public Rational div(Rational other) {
		assert(this != POSITIVE_INFINITY && this != NEGATIVE_INFINITY);
		assert(other != POSITIVE_INFINITY && other != NEGATIVE_INFINITY);
		if (other == Rational.ZERO)
			throw new ArithmeticException("Division by ZERO");
		if (other == Rational.ONE)
			return this;
		if (other == Rational.MONE)
			return this.negate();

		/* fast path */
		if (mbignum == null && other.mbignum == null) {
			long newnum = (long)mnum * other.mdenom;
			long newdenom = (long)mdenom * other.mnum;
			return valueOf(newnum, newdenom);
		}
		BigInteger denom = denominator().multiply(other.numerator());
		BigInteger nom = numerator().multiply(other.denominator());
		return valueOf(nom,denom);
	}
	
	/**
	 * Compute the gcd of two rationals (this and other).  The gcd
	 * is the rational number, such that dividing this and other with
	 * the gcd will yield two co-prime integers.
	 * @param other the second rational argument.
	 * @return the gcd of this and other.
	 */
	public Rational gcd(Rational other) {
		if (this == Rational.ZERO)
			return other;
		if (other == Rational.ZERO)
			return this;
		/* new numerator = gcd(num, other.num) */
		/* new denominator = lcm(denom, other.denom) */
		/* fast path */
		if (mbignum == null && other.mbignum == null) {
			int gcddenom = gcd(mdenom, other.mdenom);
			long denom = ((long) (mdenom / gcddenom)) * other.mdenom;
			long num = gcd(mnum < 0 ? -mnum : mnum,
					other.mnum < 0 ? -other.mnum : other.mnum);
			return valueOf(num, denom);
		}
		BigInteger tdenom = this.denominator();
		BigInteger odenom = other.denominator();
		BigInteger gcddenom = tdenom.gcd(odenom);
		BigInteger denom = tdenom.divide(gcddenom).multiply(odenom);
		BigInteger num = numerator().gcd(other.numerator());
		return Rational.valueOf(num, denom);
	}
	/**
	 * Returns a new rational representing the inverse of <code>this</code>.
	 * @return Inverse of <code>this</code>.
	 */
	public Rational inverse() {
		/* fast path */
		if (mbignum == null)
			return valueOf(mdenom, mnum);
		else
			return valueOf(mbigdenom, mbignum);
	}

	/**
	 * Check whether this rational is negative.
	 * @return <code>true</code> iff this rational is negative.
	 */
	public boolean isNegative() {
		if (mbignum == null)
			return mnum < 0;
		return mbignum.signum() == -1;
	}
	
	public int signum() {
		if (mbignum == null)
			return mnum < 0 ? -1 : mnum == 0 ? 0 : 1;
		return mbignum.signum();
	}

	@Override
	public int compareTo(Rational o) {
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
		// Old version
		if (o instanceof MutableRational)
			return ((MutableRational) o).equals(this);
		if( o instanceof Rational ) {
			Rational r = (Rational) o;
			// Works thanks to normalization!!!
			if (mbignum == null && r.mbignum == null)
				return mnum == r.mnum && mdenom == r.mdenom;
			return numerator().equals(r.numerator()) && denominator().equals(r.denominator());
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
		}
		if (mbigdenom.equals(BigInteger.ONE))
			return mbignum.toString();
		return mbignum.toString() +"/" + mbigdenom.toString();
	}
	/**
	 * Check whether this rational represents an integral value. Both infinity
	 * values are treated as integral.
	 * @return <code>true</code> iff value is integral.
	 */
	public boolean isIntegral() {
		return (mbignum == null) ? mdenom <= 1 : mbigdenom.equals(BigInteger.ONE);
	}
	/**
	 * Return a new rational representing the biggest integral rational not
	 * bigger than <code>this</code>.
	 * @return Next smaller integer of <code>this</code>.
	 */
	public Rational floor() {
		/* fast path */
		if (mbignum == null) {
			if (mdenom <= 1)
				return this;
			int div = mnum / mdenom;
			// Java rounds the wrong way for negative numbers.
			// We know that the division is not exact due to
			// normalization and mdenom != 1, so subtracting
			// one fixes the result for negative numbers.
			if (mnum < 0)
				div--;
			return valueOf(div, 1);
		}
		if( denominator().equals(BigInteger.ONE) )
			return this;
		BigInteger div = numerator().divide(denominator());
		if( numerator().signum() < 0)
			div = div.subtract(BigInteger.ONE);
		return Rational.valueOf(div,BigInteger.ONE);
	}
	/**
	 * Returns the fractional part of the rational, i.e. the
	 * number this.sub(this.floor()).
	 * @return Next smaller integer of <code>this</code>.
	 */
	public Rational frac() {
		/* fast path */
		if (mbignum == null) {
			if (mdenom <= 1)
				return Rational.ZERO;
			int newnum = mnum % mdenom;
			// Java rounds the wrong way for negative numbers.
			// We know that the division is not exact due to
			// normalization and mdenom != 1, so subtracting
			// one fixes the result for negative numbers.
			if (newnum < 0)
				newnum += mdenom;
			return valueOf(newnum, mdenom);
		}
		if( mbigdenom.equals(BigInteger.ONE) )
			return Rational.ZERO;
		BigInteger newnum = mbignum.mod(mbigdenom);
		if( newnum.signum() < 0)
			newnum.add(mbigdenom);
		return Rational.valueOf(newnum, mbigdenom);
	}
	/**
	 * Return a new rational representing the smallest integral rational not
	 * smaller than <code>this</code>.
	 * @return Next bigger integer of <code>this</code>.
	 */
	public Rational ceil() {
		/* fast path */
		if (mbignum == null) {
			if (mdenom <= 1)
				return this;
			int div = mnum / mdenom;
			// Java rounds the wrong way for positive numbers.
			// We know that the division is not exact due to
			// normalization and mdenom != 1, so adding
			// one fixes the result for positive numbers.
			if (mnum > 0)
				div++;
			return valueOf(div, 1);
		}
		if (denominator().equals(BigInteger.ONE))
			return this;
		BigInteger div = numerator().divide(denominator());
		if( numerator().signum() > 0)
			div = div.add(BigInteger.ONE);
		return Rational.valueOf(div,BigInteger.ONE);
	}
	public Rational abs() {
		if (mbignum == null)
			return valueOf(Math.abs((long) mnum), mdenom);
		return valueOf(mbignum.abs(), mbigdenom);
	}

	public final static Rational POSITIVE_INFINITY = new Rational(1,0);
	public final static Rational NAN = new Rational(0,0);
	public final static Rational NEGATIVE_INFINITY = new Rational(-1,0);
	public final static Rational ZERO = new Rational(0,1);
	public final static Rational ONE = new Rational(1,1);
	public final static Rational MONE = new Rational(-1,1);
}
