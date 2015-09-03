package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.math.BigDecimal;

/**
 * A value in the interval domain for abstract interpretation. This value can be of any numbered type or can be
 * infinity.
 * 
 * <p>
 * For interpreting values, one must always account for possible infinity. If {@link #isInfinity()} returns
 * <code>true</code>, the value obtained through {@link #getValue()} must be ignored as it is unsound.
 * </p>
 * 
 * @author greitsch@informatik.uni-freiburg.de
 * 
 */
public class IntervalValue implements Comparable<IntervalValue> {

	private BigDecimal mValue;

	private boolean mIsInfty;

	/**
	 * Constructor for a new {@link IntervalValue}. The value is set to infinity initially.
	 * 
	 * @param clazz
	 *            The backing field type.
	 */
	protected IntervalValue() {
		mIsInfty = true;
	}

	/**
	 * Constructor for a new {@link IntervalValue} that sets the value to a provided value.
	 * 
	 * @param val
	 *            The value to set.
	 * @param clazz
	 *            The backing field type.
	 */
	protected IntervalValue(BigDecimal val) {
		mValue = val;
		mIsInfty = false;
	}

	/**
	 * Sets the value to the given value. If the value before was infinity, the infinity flag will be revoked.
	 * 
	 * @param val
	 *            The value to set.
	 */
	protected void setValue(BigDecimal val) {
		mValue = val;
		mIsInfty = false;
	}

	/**
	 * Returns the value of this.
	 * 
	 * <p>
	 * Note that this value is unsound if {@link #isInfinity()} returns <code>true</code>.
	 * </p>
	 * 
	 * @return The value of this.
	 */
	protected BigDecimal getValue() {
		return mValue;
	}

	/**
	 * Sets the value to infinity.
	 */
	protected void setToInfinity() {
		mValue = null;
		mIsInfty = true;
	}

	/**
	 * Returns <code>true</code> if the value is corresponding to infinity, <code>false</code> otherwise.
	 * 
	 * @return <code>true</code> or <code>false</code>
	 */
	protected boolean isInfinity() {
		return mIsInfty;
	}

	@Override
	public boolean equals(Object other) {
		if (other == null) {
			return false;
		}

		if (this.getClass() != other.getClass()) {
			return false;
		}

		if (other == this) {
			return true;
		}

		final IntervalValue comparableOther = (IntervalValue) other;

		if (mIsInfty && comparableOther.mIsInfty) {
			return true;
		}

		if ((mIsInfty && !comparableOther.mIsInfty) || (!mIsInfty && comparableOther.mIsInfty)) {
			return false;
		}

		return mValue.compareTo(comparableOther.mValue) == 0 ? true : false;
	}

	@Override
	public int hashCode() {
		return mValue.hashCode();
	}

	@Override
	public int compareTo(IntervalValue other) {

		if (other == null) {
			throw new UnsupportedOperationException("Empty comparator is not allowed.");
		}

		if (mIsInfty && other.isInfinity()) {
			return 0;
		}

		if (mIsInfty && !other.isInfinity()) {
			return 1;
		}

		if (!mIsInfty && other.isInfinity()) {
			return -1;
		}

		return mValue.compareTo(other.mValue);
	}

	@Override
	public String toString() {
		if (mIsInfty) {
			return "\\infty";
		}

		return mValue.toString();
	}
}
