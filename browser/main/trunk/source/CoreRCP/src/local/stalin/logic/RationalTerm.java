package local.stalin.logic;

import java.math.BigInteger;

public class RationalTerm extends Term {
	private static final long serialVersionUID = 701561357751579407L;
	/**
	 * The numerator of the fraction this term represents.
	 */
	private BigInteger numerator;
	/**
	 * The denominator of the fraction this term represent. Must be positive.
	 * The gcd of numerator and denominator should be one.
	 */
	private BigInteger denominator;
	private Sort sort;

	RationalTerm(BigInteger num, BigInteger denom, Sort sort) {
		assert denom.compareTo(BigInteger.ZERO) > 0;
		numerator = num;
		denominator = denom;
		this.sort = sort;
	}

	public BigInteger getNumerator() {
		return numerator;
	}

	public BigInteger getDenominator() {
		return denominator;
	}

	public boolean typeCheck() {
		return true;
	}

	public Sort getSort() {
		return sort;
	}

	public String toString() {
		String ann = getStringOfAnnotations();
		boolean isPositive = numerator.compareTo(BigInteger.ZERO) >= 0;
		String rep = numerator.abs().toString()+".0";
		if (!isPositive)
			rep = "(~ "+rep+")";
		if (!denominator.equals(BigInteger.ONE))
			rep = "(/ " + rep + " " + denominator.toString() + ".0)";
		
		if (ann != "") {
			if (!rep.startsWith("("))
				return "("+rep+ann+")";
			else
				return rep.substring(0, rep.length()-1)+ann+")";
		} else
			return rep;
	}

	@Override
	public boolean containsSubTerm(Term t) {
		return t == this;
	}
	// This function _IS_ actually used by the native z3 parser
	@SuppressWarnings("unused")
	private String pureValue() {
		return numerator.toString() + "/" + denominator.toString();
	}
}
