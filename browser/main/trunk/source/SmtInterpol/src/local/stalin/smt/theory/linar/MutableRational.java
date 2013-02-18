package local.stalin.smt.theory.linar;

import java.math.BigInteger;

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
		mbignum = r.mbignum;
		mbigdenom = r.mbigdenom;
	}
	
	public MutableRational(MutableRational r) {
		mnum = r.mnum;
		mdenom = r.mdenom;
		mbignum = r.mbignum;
		mbigdenom = r.mbigdenom;
	}

	public void setValue(long newnum, long newdenom) {
		assert (newnum != 0 || newdenom != 0);
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
			if( mdenom < 0 ) {
				mnum = -mnum;
				mdenom = -mdenom;
			}
			int norm = Rational.gcd(Math.abs(mnum),Math.abs(mdenom));
			if (norm != 0) {
				mnum /= norm;
				mdenom /= norm;
			}
		} else {
			if (mbigdenom.signum() < 0) {
				mbignum = mbignum.negate();
				mbigdenom = mbigdenom.negate();
			}
			BigInteger norm = mbignum.gcd(mbigdenom);
			if (!norm.equals(BigInteger.ZERO)) {
				mbignum = mbignum.divide(norm);
				mbigdenom = mbigdenom.divide(norm);
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
		if (mbignum == null && other.mbignum == null) {
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
			mbignum = other.mbignum;
			mbigdenom = other.mbigdenom;
			return this;
		}
		
		BigInteger tdenom = denominator();
		BigInteger odenom = other.denominator();
		BigInteger gcd = tdenom.gcd(odenom);
		BigInteger tdenomgcd = tdenom.divide(gcd);
		BigInteger odenomgcd = odenom.divide(gcd);
		mbignum = numerator().multiply(odenomgcd)
			.add(other.numerator().multiply(tdenomgcd));
		mbigdenom = tdenom.multiply(odenomgcd);
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
		if (mbignum == null && other.mbignum == null) {
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
		if (mbignum == null && other.mbignum == null) {
			long newnum = (long)mnum * other.mdenom;
			long newdenom = (long)mdenom * other.mnum;
			setValue(newnum, newdenom);
			return this;
		}
		mbignum = numerator().multiply(other.denominator());
		mbigdenom = denominator().multiply(other.numerator());
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
	 * @param fac1
	 * @param fac2
	 * @return
	 */
	public MutableRational addmul(Rational fac1,Rational fac2) {
		return add(fac1.mul(fac2));
	}
	/**
	 * Returns <code>(this-s)/d</code>
	 * @param s
	 * @param d
	 * @return
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
		if (o instanceof Rational)
			o = new MutableRational((Rational)o);
		return (o instanceof MutableRational ? compareTo((MutableRational) o) == 0 : false); 
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
}
