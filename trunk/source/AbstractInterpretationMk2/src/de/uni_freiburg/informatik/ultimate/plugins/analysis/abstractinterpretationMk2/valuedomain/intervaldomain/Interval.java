/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.intervaldomain;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * An integer interval [l, u] with l <= u (-infinity, infinity), (-infinity, u],
 * [l, infinity) are also allowed l and u are stored as Rational. If l > u, the
 * interval is empty.
 * 
 * @author Christopher Dillo
 */
public class Interval {
	private Rational mLower;
	private Rational mUpper;

	/**
	 * [lowerBound, upperBound] lowerBound <= upperBound
	 * 
	 * @param lowerBound
	 *            Rational for the lower bound
	 * @param upperBound
	 *            Rational for the upper bound
	 */
	public Interval(Rational lowerBound, Rational upperBound) {
		mLower = lowerBound.floor();
		mUpper = upperBound.ceil();
	}

	/**
	 * [bound, bound]
	 * 
	 * @param bound
	 *            Rational for the lower and upper bound
	 */
	public Interval(Rational bound) {
		mLower = bound.floor();
		mUpper = bound.ceil();
	}

	/**
	 * Creates an empty interval [1, -1]
	 */
	public Interval() {
		mLower = Rational.ONE;
		mUpper = Rational.MONE;
	}

	/**
	 * @return A string representing the lower bound, null if at negative
	 *         infinity
	 */
	public Rational getLowerBound() {
		return mLower;
	}

	/**
	 * @return A string representing the upper bound, null if at positive
	 *         infinity
	 */
	public Rational getUpperBound() {
		return mUpper;
	}

	/**
	 * @return True iff the interval is empty
	 */
	public boolean isEmpty() {
		return mLower.compareTo(mUpper) > 0;
	}

	/**
	 * @return A copy of this interval in an independant object
	 */
	public Interval copy() {
		if (isEmpty())
			return new Interval();

		return new Interval(mLower, mUpper);
	}

	/**
	 * @param interval
	 * @return True if this interval and the given interval are equal
	 */
	public boolean isEqual(Interval interval) {
		return (isEmpty() && interval.isEmpty())
				|| (mLower.compareTo(interval.getLowerBound()) == 0 && mUpper
						.compareTo(interval.getUpperBound()) == 0);
	}

	/**
	 * @param interval
	 * @return True if this interval and the given interval are equal
	 */
	public boolean isEqual(Rational value) {
		return mLower.compareTo(value) == 0 && mUpper.compareTo(value) == 0;
	}

	/**
	 * @return True iff the interval is an interval [a, a] containing only a
	 *         single integer value
	 */
	public boolean isSingleValueInterval() {
		return mLower.compareTo(mUpper) == 0;
	}

	public String toString() {
		if (isEmpty())
			return "{}";
		String lower = (mLower.compareTo(Rational.NEGATIVE_INFINITY) == 0) ? "(-infinity"
				: "[" + mLower.toString();
		String upper = (mUpper.compareTo(Rational.POSITIVE_INFINITY) == 0) ? "infinity)"
				: mUpper.toString() + "]";
		return lower + ", " + upper;
	}
}
