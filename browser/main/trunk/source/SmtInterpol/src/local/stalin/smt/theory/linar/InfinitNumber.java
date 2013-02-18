package local.stalin.smt.theory.linar;

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
	Rational ma;
	// Infinitesimal part
	Rational mb;
	/// --- Construction ---
	/**
	 * Zero constructor.
	 */
	public InfinitNumber() {
		this(Rational.ZERO,Rational.ZERO);
	}
	/**
	 * Constructor for arbitrary infinitesimal numbers.
	 * @param a Rational part of the number.
	 * @param b Infinitesimal part of the number.
	 */
	public InfinitNumber(Rational a,Rational b) {
		ma = a;
		mb = b;
	}
	public static final InfinitNumber POSITIVE_INFINITY = new InfinitNumber(Rational.POSITIVE_INFINITY,Rational.ZERO);
	public static final InfinitNumber NEGATIVE_INFINITY = new InfinitNumber(Rational.NEGATIVE_INFINITY,Rational.ZERO);
	public static final InfinitNumber ZERO = new InfinitNumber(Rational.ZERO,Rational.ZERO);
	/// --- Arithmetic ---
	/**
	 * Returns this + other.
	 */
	public InfinitNumber add(InfinitNumber other) {
		return new InfinitNumber(ma.add(other.ma),mb.add(other.mb));
	}
	/**
	 * Returns this - other.
	 */
	public InfinitNumber sub(InfinitNumber other) {
		return new InfinitNumber(ma.sub(other.ma),mb.sub(other.mb));
	}
	/**
	 * Returns c*this.
	 */
	public InfinitNumber mul(Rational c) {
		return new InfinitNumber(ma.mul(c),mb.mul(c));
	}
	/**
	 * Returns this/c.
	 */
	public InfinitNumber div(Rational c) {
		return new InfinitNumber(ma.div(c),mb.div(c));
	}
	/**
	 * Returns -this.
	 */
	public InfinitNumber negate() {
		return new InfinitNumber(ma.negate(),mb.negate());
	}
	/**
	 * Returns this+(fac1*fac2)
	 * @param fac1
	 * @param fac2
	 * @return
	 */
	public InfinitNumber addmul(InfinitNumber fac1,Rational fac2) {
		return new InfinitNumber(ma.addmul(fac1.ma,fac2),mb.addmul(fac1.mb,fac2));
	}
	/**
	 * Returns (this-s)/d
	 * @param s
	 * @param d
	 * @return
	 */
	public InfinitNumber subdiv(InfinitNumber s,Rational d) {
		return new InfinitNumber(ma.subdiv(s.ma,d),mb.subdiv(s.mb,d));
	}
	/// --- Comparing ---
	@Override
	public int compareTo(InfinitNumber arg0) {
		int ac = ma.compareTo(arg0.ma);
		// Old version
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
		if( o instanceof InfinitNumber ) {
			InfinitNumber n = (InfinitNumber) o;
			return ma.equals(n.ma) && mb.equals(n.mb);
		}
		return false;
	}
	/**
	 * Returns <code>true</code> iff this is less then other. This function is
	 * considered slightly more efficient than 
	 * <code>this.compareTo(other) < 0</code> but yields the same result. 
	 * @param other Number to compare against.
	 * @return <code>true</code> iff this is less than other.
	 */
	public boolean less(InfinitNumber other) {
		int ac = ma.compareTo(other.ma);
		return ac < 0 || (ac == 0 && mb.compareTo(other.mb) < 0);
	}
	/**
	 * Returns <code>true</code> iff this is less then or equal to other. This 
	 * function is considered slightly more efficient than 
	 * <code>this.compareTo(other) <= 0</code> but yields the same result. 
	 * @param other Number to compare against.
	 * @return <code>true</code> iff this is less than or equal to other.
	*/
	public boolean lesseq(InfinitNumber other) {
		int ac = ma.compareTo(other.ma);
		return ac < 0 || (ac == 0 && mb.compareTo(other.mb) <= 0);
	}
	/// --- Checks ---
	/**
	 * Returns true iff this represents either positive or negative infinity.
	 */
	public boolean isInfinity() {
		return ma.equals(Rational.POSITIVE_INFINITY) || ma.equals(Rational.NEGATIVE_INFINITY);
	}
	
	public String toString() {
		if (mb.equals(Rational.ZERO))
			return ma.toString();
		String sign = "+";
		Rational epsPart = mb;
		if (epsPart.isNegative()) {
			sign = "-";
			epsPart = epsPart.negate();
		}
		if (epsPart.equals(Rational.ONE))
			return ma + sign + "eps";
		else
			return ma + sign + epsPart + "eps";
	}
	/**
	 * Returns the next lower integral number. Flooring depends on the value
	 * of the infinitesimal coefficient. Note that the result will have a zero
	 * infinitesimal coefficient.
	 * @return Next lower integral number.
	 */
	public InfinitNumber floor() {
		if( !ma.isIntegral() )
			return new InfinitNumber(ma.floor(),Rational.ZERO);
		if( mb.compareTo(Rational.ZERO) >= 0 )
			return new InfinitNumber(ma,Rational.ZERO);
		return new InfinitNumber(ma.sub(Rational.ONE),Rational.ZERO);
	}
	/**
	 * Returns the next higher integral number. Ceiling depends on the value
	 * of the infinitesimal coefficient. Note that the result will have a zero
	 * infinitesimal coefficient.
	 * @return Next higher integral number.
	 */
	public InfinitNumber ceil() {
		if( !ma.isIntegral() )
			return new InfinitNumber(ma.ceil(),Rational.ZERO);
		if( mb.compareTo(Rational.ZERO) <= 0 )
			return new InfinitNumber(ma,Rational.ZERO);
		return new InfinitNumber(ma.add(Rational.ONE),Rational.ZERO);
	}
}
