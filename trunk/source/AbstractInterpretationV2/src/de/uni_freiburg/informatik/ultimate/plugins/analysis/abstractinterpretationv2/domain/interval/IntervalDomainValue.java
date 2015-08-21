package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;

/**
 * Representation of an interval value in the interval domain.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalDomainValue<T extends Number> implements IEvaluationResult<IntervalDomainValue<T>>,
        Comparable<IntervalDomainValue<T>> {

	private IntervalValue<T> mLower;
	private IntervalValue<T> mUpper;

	/**
	 * Constructor for a new {@link IntervalDomainValue}. The interval created will be (-&infin; ; &infin;).
	 * 
	 * @param clazz
	 */
	public IntervalDomainValue(Class<T> clazz) {
		assert clazz != null;

		mLower = new IntervalValue<T>(clazz);
		mUpper = new IntervalValue<T>(clazz);
	}

	public IntervalDomainValue(IntervalValue<T> lower, IntervalValue<T> upper) {
		mLower = lower;
		mUpper = upper;
	}

	@Override
	public IntervalDomainValue<T> getResult() {
		return this;
	}

	@Override
	public int compareTo(IntervalDomainValue<T> o) {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public String toString() {
		String lower = (mLower.isInfinity() ? "-\\infty" : mLower.toString());
		String upper = (mUpper.isInfinity() ? "\\infty" : mUpper.toString());

		return "[ " + lower + "; " + upper + " ]";
	}
}
