package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

/**
 * A value in the interval domain for abstract interpretation. This value can be of any numbered type or can be
 * infinity.
 * 
 * For interpreting values, one must always account for possible infinity. If {@link #isInfinity()} returns
 * <code>true</code>, the value obtained through {@link #getValue()} must be ignored as it is unsound.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 * @param <T>
 */
public class IntervalValue<T extends Number> implements Comparable<IntervalValue<T>> {

	private T mValue;
	private boolean mIsInfty;

	private final Class<T> mClass;

	/**
	 * Constructor for a new {@link IntervalValue}. The value is set to infinity initially.
	 * 
	 * @param clazz
	 *            The backing field type.
	 */
	public IntervalValue(Class<T> clazz) {
		mClass = clazz;
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
	public IntervalValue(T val, Class<T> clazz) {
		mClass = clazz;
		mValue = val;
		mIsInfty = false;
	}

	/**
	 * Sets the value to the given value. If the value before was infinity, the infinity flag will be revoked.
	 * 
	 * @param val
	 *            The value to set.
	 */
	public void setValue(T val) {
		mValue = val;
		mIsInfty = false;
	}

	/**
	 * Returns the value of this.<br />
	 * 
	 * Note that this value is unsound if {@link #isInfinity()} returns <code>true</code>.
	 * 
	 * @return The value of this.
	 */
	public T getValue() {
		return mValue;
	}

	/**
	 * Sets the value to infinity.
	 */
	public void setToInfinity() {
		mIsInfty = true;
	}

	/**
	 * Returns <code>true</code> if the value is corresponding to infinity, <code>false</code> otherwise.
	 * 
	 * @return <code>true</code> or <code>false</code>
	 */
	public boolean isInfinity() {
		return mIsInfty;
	}

	@Override
	public int compareTo(IntervalValue<T> o) {

		if (o == null) {
			throw new NullPointerException("Empty comparator is not allowed.");
		}

		if (!mClass.equals(o.mClass)) {
			throw new UnsupportedOperationException("The backing types of this and the other value are not equal."
			        + " Therefore, the values are not comparable.");
		}

		if (mIsInfty && o.isInfinity()) {
			return 0;
		}

		if (mIsInfty && !o.isInfinity()) {
			return 1;
		}

		if (!mIsInfty && o.isInfinity()) {
			return -1;
		}

		if (mClass.equals(Byte.class)) {
			Byte own = (Byte) mValue;
			Byte other = (Byte) o.mValue;

			return own.compareTo(other);
		} else if (mClass.equals(Double.class)) {
			Double own = (Double) mValue;
			Double other = (Double) o.mValue;

			return own.compareTo(other);
		} else if (mClass.equals(Float.class)) {
			Float own = (Float) mValue;
			Float other = (Float) o.mValue;

			return own.compareTo(other);
		} else if (mClass.equals(Integer.class)) {
			Integer own = (Integer) mValue;
			Integer other = (Integer) o.mValue;

			return own.compareTo(other);
		} else if (mClass.equals(Long.class)) {
			Long own = (Long) mValue;
			Long other = (Long) o.mValue;

			return own.compareTo(other);
		} else if (mClass.equals(Short.class)) {
			Short own = (Short) mValue;
			Short other = (Short) o.mValue;

			return own.compareTo(other);
		}

		throw new UnsupportedOperationException("The backing type " + mClass.toString() + " cannot be handled.");
	}
}
