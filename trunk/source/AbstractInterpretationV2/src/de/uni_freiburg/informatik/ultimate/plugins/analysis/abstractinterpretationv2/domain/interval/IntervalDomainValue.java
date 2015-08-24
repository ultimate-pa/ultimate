package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;

/**
 * Representation of an interval value in the interval domain.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalDomainValue implements IEvaluationResult<IntervalDomainValue>, Comparable<IntervalDomainValue> {

	private IntervalValue mLower;
	private IntervalValue mUpper;

	private boolean mIsBottom;

	/**
	 * Constructor for a new {@link IntervalDomainValue}. The interval created will be (-&infin; ; &infin;).
	 */
	protected IntervalDomainValue() {
		this(false);
	}

	/**
	 * Constructor for a new {@link IntervalDomainValue}. The interval created is dependent on the value of the
	 * parameter. If {@code isBottom} is set to <code>false</code>, the created interval will be (-&infin; ; &infin;).
	 * If {@code isBottom} is set to <code>true</code>, the created interval will be &bot;.
	 * 
	 * @param isBottom
	 *            Specifies whether the interval should be &bot; or an actual interval.
	 */
	protected IntervalDomainValue(boolean isBottom) {
		if (isBottom) {
			mLower = null;
			mUpper = null;
			mIsBottom = true;
		} else {
			mLower = new IntervalValue();
			mUpper = new IntervalValue();
			mIsBottom = false;
		}
	}

	protected IntervalDomainValue(IntervalValue lower, IntervalValue upper) {
		mLower = lower;
		mUpper = upper;

		mIsBottom = false;
	}

	/**
	 * Sets the current interval to &bot;.
	 */
	protected void setToBottom() {
		mLower = null;
		mUpper = null;

		mIsBottom = true;
	}

	/**
	 * Returns <code>true</code> if the current interval is &bot;, <code>false</code> otherwise. Note that a return
	 * value of <code>false</code> may also mean that one or both of the interval bounds is -&infin; or &infin;.
	 * 
	 * @return
	 */
	protected boolean isBottom() {
		return mIsBottom;
	}

	/**
	 * Returns the lower value of the interval.
	 * 
	 * @return
	 */
	protected IntervalValue getLower() {
		return mLower;
	}

	/**
	 * Returns the upper value of the interval.
	 * 
	 * @return
	 */
	protected IntervalValue getUpper() {
		return mUpper;
	}

	@Override
	public IntervalDomainValue getResult() {
		return this;
	}

	@Override
	public int compareTo(IntervalDomainValue o) {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public boolean equals(Object other) {
		if (other == null) {
			return false;
		}

		if (other == this) {
			return true;
		}

		if (!(other instanceof IntervalDomainValue)) {
			return false;
		}

		IntervalDomainValue castedOther = (IntervalDomainValue) other;

		if (mIsBottom || castedOther.mIsBottom) {
			return mIsBottom == castedOther.mIsBottom;
		}

		if (mLower.equals(castedOther.mLower) && mUpper.equals(castedOther.mUpper)) {
			return true;
		}

		return false;
	}

	@Override
	public String toString() {
		if (mIsBottom) {
			return "{}";
		}

		String lower = (mLower.isInfinity() ? "-\\infty" : mLower.toString());
		String upper = (mUpper.isInfinity() ? "\\infty" : mUpper.toString());

		return "[ " + lower + "; " + upper + " ]";
	}
}
