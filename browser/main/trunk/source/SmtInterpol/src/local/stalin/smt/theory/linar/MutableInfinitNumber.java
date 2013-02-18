package local.stalin.smt.theory.linar;

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
	MutableRational mb;
	/// --- Construction ---
	public MutableInfinitNumber() {
		this(Rational.ZERO,Rational.ZERO);
	}
	public MutableInfinitNumber(Rational a,Rational b) {
		ma = new MutableRational(a);
		mb = new MutableRational(b);
	}
	public MutableInfinitNumber(InfinitNumber other) {
		ma = new MutableRational(other.ma);
		mb = new MutableRational(other.mb);
	}
	public MutableInfinitNumber(MutableInfinitNumber other) {
		ma = new MutableRational(other.ma);
		mb = new MutableRational(other.mb);
	}
	/// --- Arithmetic ---
	/**
	 * Returns this + other.
	 */
	public MutableInfinitNumber add(InfinitNumber other) {
		ma.add(other.ma);
		mb.add(other.mb);
		return this;
	}
	/**
	 * Returns this - other.
	 */
	public MutableInfinitNumber sub(InfinitNumber other) {
		ma.sub(other.ma);
		mb.sub(other.mb);
		return this;
	}
	/**
	 * Returns c*this.
	 */
	public MutableInfinitNumber mul(Rational c) {
		ma.mul(c);
		mb.mul(c);
		return this;
	}
	/**
	 * Returns this/c.
	 */
	public MutableInfinitNumber div(Rational c) {
		ma.div(c);
		mb.div(c);
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
		mb.addmul(fac1.mb,fac2);
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
		mb.subdiv(s.mb,d);
		return this;
	}
	/// --- Comparing ---
	@Override
	public int compareTo(MutableInfinitNumber arg0) {
		int ac = ma.compareTo(arg0.ma);
		// Old Version
		/*if( ac < 0 )
			return -1;
		if( ac == 0 ) {
			int bc = mb.compareTo(arg0.mb);
			if( bc < 0 )
				return -1;
			if( bc == 0 )
				return 0;
		}
		return 1;*/
		if( ac == 0 )
			return mb.compareTo(arg0.mb);
		return ac;
	}
	public boolean equals(Object o) {
		if( o instanceof InfinitNumber )
			o = new MutableInfinitNumber((InfinitNumber)o);
		if( o instanceof MutableInfinitNumber ) {
			MutableInfinitNumber n = (MutableInfinitNumber) o;
			return ma.equals(n.ma) && mb.equals(n.mb);
		}
		return false;
	}
	/// --- Checks ---
	public boolean isInfinity() {
		return ma.equals(Rational.POSITIVE_INFINITY) || ma.equals(Rational.NEGATIVE_INFINITY);
	}
	
	public String toString() {
		if (mb.equals(Rational.ZERO))
			return ma.toString();
		String sign = "+";
		MutableRational epsPart = mb;
		if (epsPart.isNegative()) {
			sign = "-";
			epsPart = epsPart.negate();
		}
		if (epsPart.equals(Rational.ONE))
			return ma + sign + "eps";
		else
			return ma + sign + epsPart + "eps";
	}
	public InfinitNumber toInfinitNumber() {
		return new InfinitNumber(ma.toRational(),mb.toRational());
	}
}
