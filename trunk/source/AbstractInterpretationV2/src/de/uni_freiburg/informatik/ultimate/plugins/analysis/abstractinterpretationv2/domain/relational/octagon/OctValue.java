package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.math.RoundingMode;

/**
 * Values for {@link OctMatrix}.
 * <p>
 * This is an extension of the real numbers by the symbol "+infinity".
 * <p>
 * Octagons are represented by constraints of the form "(+/-) x (+/-) y <= c" where c is a constant
 * and can be represented by objects of this class.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OctValue implements Comparable<OctValue> {
	
	public final static OctValue INFINITY = new OctValue();
	public final static OctValue ZERO = new OctValue(0);
	
	private BigDecimal mValue;
	
	/** Creates a new OctagonValue with value infinity. */
	private OctValue() {
		// mValue is already null => represents infinity
	}
	
	/**
	 * Creates a new OctagonValue with a value less than infinity.
	 * Use {@link #INFINITY} to represent infinity.
	 * @param value value less than infinity
	 */
	public OctValue(BigDecimal value) {
		if (value == null) {			
			throw new IllegalArgumentException("Use constant INFINITY to represent infinity.");
		}
		mValue = value;
	}
	
	public OctValue(int i) {
		mValue = new BigDecimal(i);
	}

	public static OctValue parse(String s) {
		if ("inf".equals(s)) {
			return INFINITY;
		}
		return new OctValue(new BigDecimal(s));
	}
	
	public boolean isInfinity() {
		return mValue == null;
	}
	
	public BigDecimal getValue() {
		return mValue;
	}

	public OctValue add(OctValue other) {
		if (mValue == null || other.mValue == null) {
			return OctValue.INFINITY;
		}
		return new OctValue(mValue.add(other.mValue));
	}
	
	public OctValue subtract(OctValue other) {
		if (other.mValue == null) {
			throw new IllegalStateException("Cannot subtract infinity.");
		} else if (mValue == null) {
			return OctValue.INFINITY;
		}
		return new OctValue(mValue.subtract(other.mValue));
	}
	
	public OctValue negate() {
		if (mValue == null) {
			throw new IllegalStateException("Cannot negate infinity.");
		}
		return new OctValue(mValue.negate());
	}

	public OctValue negateIfNotInfinity() {
		if (mValue == null) {
			return this;
		}
		return new OctValue(mValue.negate());
	}
	
	/**
	 * Returns an {@linkplain OctValue} equal to {@code this / 2}.
	 * {@code  infinity / 2 = infinity}.
	 * @return {@code this / 2}
	 */
	public OctValue half() {
		if (mValue == null) {
			return OctValue.INFINITY;
		}
		// x has a finite decimal expansion <=> x/2 has a finite decimal expansion
		// (BigDecimal requires a finite decimal expansions)
		return new OctValue(mValue.divide(new BigDecimal(2)));
	}
	
	/**
	 * Returns an {@linkplain OctValue} rounded towards {@code -infinity}.
	 * {@code infinity} is already rounded.
	 * @return floored {@linkplain OctValue}
	 */
	public OctValue floor() {
		if (mValue == null) {
			return OctValue.INFINITY;
		}
		return new OctValue(mValue.setScale(0, RoundingMode.FLOOR));
	}

	public int signum() {
		return mValue == null ? 1 : mValue.signum();
	}
	
	@Override
	public int compareTo(OctValue other) {
		if (this == other || mValue == other.mValue) {
			return 0;
		} else if (mValue == null) {			
			return 1;
		} else if (other.mValue == null) {
			return -1;
		}
		return mValue.compareTo(other.mValue);
	}

	@Override
	public String toString() {
		if (mValue == null) {
			return "inf";
		}
		return mValue.toString();
	}

	// static methods ---------------------------------------------------------
	
	public static OctValue min(OctValue a, OctValue b) {
		return a.compareTo(b) <= 0 ? a : b; 
	}
	
	public static OctValue max(OctValue a, OctValue b) {
		return a.compareTo(b) >= 0 ? a : b;
	}


}
