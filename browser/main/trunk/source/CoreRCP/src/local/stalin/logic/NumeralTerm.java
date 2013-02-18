package local.stalin.logic;

import java.math.BigInteger;

public class NumeralTerm extends Term {
	private static final long serialVersionUID = 8754997676749509285L;
	/**
	 * The numeric value of this term.
	 */
	private BigInteger numeral;
	private Sort sort;
	
	public NumeralTerm(BigInteger numeral, Sort sort) {
		this.numeral = numeral;
		this.sort = sort;
	}
	
	public BigInteger getNumeral() {
		return numeral;
	}

	public boolean typeCheck() {
		return true;
	}

	public Sort getSort() {
		return sort;
	}

	public String toString() {
		String ann = getStringOfAnnotations();
		boolean isPositive = numeral.compareTo(BigInteger.ZERO) >= 0;
		String rep = numeral.abs().toString(); 
		if (ann.equals("") && isPositive)
			return rep;
		if (!isPositive)
			rep = "~ "+rep;
		return "("+rep+ann+")";
	}

	@Override
	public boolean containsSubTerm(Term t) {
		return t == this;
	}
	
	public String pureValue() {
			return numeral.toString();
	}
}
