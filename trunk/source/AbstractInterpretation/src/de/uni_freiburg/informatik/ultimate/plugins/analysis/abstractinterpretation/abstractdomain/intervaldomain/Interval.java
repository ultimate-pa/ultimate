/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain;

import java.math.BigInteger;

/**
 * An integer interval [l, u] with l <= u
 * (-infinity, infinity), (-infinity, u], [l, infinity) are also allowed
 * l and u are stored as strings, null if at positive/negative infinity
 * 
 * @author Christopher Dillo
 */
public class Interval {	
	private String m_lower, m_upper;
	
	private boolean m_empty, m_lowerInfty, m_upperInfty;
	
	/**
	 * [lowerBound, upperBound] lowerBound <= upperBound
	 * @param lowerBound integer in string representation for the lower bound of the interval, null for negative infinity
	 * @param upperBound integer in string representation for the upper bound of the interval, null for positive infinity
	 */
	public Interval(String lowerBound, String upperBound) {
		if (lowerBound == null)
			setLowerToInfty();
		else
			setLower(lowerBound);

		if (upperBound == null)
			setUpperToInfty();
		else
			setUpper(upperBound);
		
		// check for lower <= upper. If not: Empty!
		if (!m_lowerInfty && !m_upperInfty) {
			BigInteger lower = new BigInteger(m_lower);
			BigInteger upper = new BigInteger(m_upper);
			if (lower.compareTo(upper) > 0)
				setEmpty();
		}
	}
	
	/**
	 * Creates an empty interval
	 */
	public Interval() {
		setEmpty();
	}
	
	private void setLower(String lowerBound) {
		try {
			// for real values: discard fractional part (-> floor)
			BigInteger lower = new BigInteger(lowerBound.split("\\.")[0]);
			m_lower = lower.toString();
		} catch (NumberFormatException e) {
			setLowerToInfty();
		}
	}
	
	private void setUpper(String upperBound) {
		try {
			// for real values: if fractional part isn't zero, add one! (-> ceil)
			String[] split = upperBound.split("\\.");
			String trunc = split[0];
			String frac = (split.length > 1) ? split[1] : "0";
			BigInteger upper = new BigInteger(trunc);
			BigInteger fracPart = new BigInteger(frac);
			if (!fracPart.equals(BigInteger.ZERO)) upper = upper.add(BigInteger.ONE);
			m_upper = upper.toString();
		} catch (NumberFormatException e) {
			setUpperToInfty();
		}
	}

	private void setLowerToInfty() {
		m_lower = null;
		m_lowerInfty = true;
		if (m_empty) {
			m_empty = false;
			setUpperToInfty();
		}
	}

	private void setUpperToInfty() {
		m_upper = null;
		m_upperInfty = true;
		if (m_empty) {
			m_empty = false;
			setLowerToInfty();
		}
	}

	private void setEmpty() {
		m_lower = null;
		m_upper = null;
		m_lowerInfty = false;
		m_upperInfty = false;
		m_empty = true;
	}
	
	/**
	 * @return A string representing the lower bound, null if at negative infinity
	 */
	public String getLowerBound() {
		return m_lower;
	}
	
	/**
	 * @return A string representing the upper bound, null if at positive infinity
	 */
	public String getUpperBound() {
		return m_upper;
	}
	
	/**
	 * @return True if the lower bound is at negative infinity
	 */
	public boolean lowerBoundIsNegInfty() {
		return m_lowerInfty;
	}
	
	/**
	 * @return True if the upper bound is at positive infinity
	 */
	public boolean upperBoundIsPosInfty() {
		return m_upperInfty;
	}

	/**
	 * @return True iff the interval is empty
	 */
	public boolean isEmpty() {
		return m_empty;
	}
	
	/**
	 * @return A copy of this interval in an independant object
	 */
	public Interval copy() {
		if (isEmpty()) return new Interval();
		
		return new Interval(m_lower, m_upper);
	}
	
	/**
	 * @param interval
	 * @return True if this interval and the given interval are equal
	 */
	public boolean isEqual(Interval interval) {
		if (isEmpty() && interval.isEmpty())
			return true;
		
		boolean lowerEqual, upperEqual;
		
		if (lowerBoundIsNegInfty()) {
			lowerEqual = interval.lowerBoundIsNegInfty();
		} else {
			if (interval.lowerBoundIsNegInfty())
				return false;
			
			lowerEqual = m_lower.equals(interval.getLowerBound());
		}
		
		if (upperBoundIsPosInfty()) {
			upperEqual = interval.upperBoundIsPosInfty();
		} else {
			if (interval.upperBoundIsPosInfty())
				return false;
			
			upperEqual = m_upper.equals(interval.getUpperBound());
		}
		
		return lowerEqual && upperEqual;
	}
	
	public String toString() {
		String lower = m_lowerInfty ?  "(-infinity" : "[" + m_lower;
		String upper = m_upperInfty ?  "infinity)" : m_upper + "]";
		return lower + ", " + upper;
	}
}
