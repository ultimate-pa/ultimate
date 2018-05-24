/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.math.BigDecimal;
import java.math.MathContext;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;

/**
 * Representation of an interval value in the interval domain.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalDomainValue implements INonrelationalValue<IntervalDomainValue> {

	private IntervalValue mLower;
	private IntervalValue mUpper;

	private boolean mIsBottom;

	/**
	 * Constructor for a new {@link IntervalDomainValue}. The interval created will be (-&infin; ; &infin;).
	 */
	public IntervalDomainValue() {
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
	public IntervalDomainValue(final boolean isBottom) {
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

	/**
	 * Constructor for a new {@link IntervalDomainValue}.
	 *
	 * @param lower
	 *            The lower value of the interval.
	 * @param upper
	 *            The upper value of the interval.
	 */
	public IntervalDomainValue(final IntervalValue lower, final IntervalValue upper) {
		if (!lower.isInfinity() && !upper.isInfinity() && lower.getValue().compareTo(upper.getValue()) > 0) {
			mIsBottom = true;
			return;
		}

		mLower = lower;
		mUpper = upper;

		mIsBottom = false;
	}

	/**
	 * Constructor for a new {@link IntervalDomainValue}.
	 *
	 * @param lower
	 *            The lower value of the interval.
	 * @param upper
	 *            The upper value of the interval.
	 */
	public IntervalDomainValue(final int lower, final int upper) {
		this(new IntervalValue(lower), new IntervalValue(upper));
	}

	/**
	 * Constructor for a new {@link IntervalDomainValue}.
	 *
	 * @param lower
	 *            The lower value of the interval.
	 * @param upper
	 *            The upper value of the interval.
	 */
	public IntervalDomainValue(final double lower, final double upper) {
		this(new IntervalValue(lower), new IntervalValue(upper));
	}

	public IntervalDomainValue(final BigDecimal dec) {
		this(new IntervalValue(dec), new IntervalValue(dec));
	}

	/**
	 * Performs a deep copy of <code>this</code>.
	 *
	 * @return A new {@link IntervalDomainValue} which is the deep copy of <code>this</code>.
	 */
	@Override
	public IntervalDomainValue copy() {
		if (mIsBottom) {
			return new IntervalDomainValue(true);
		}

		return new IntervalDomainValue(new IntervalValue(mLower), new IntervalValue(mUpper));
	}

	/**
	 * Computes the result of a greater or equal operation with another interval:
	 * <p>
	 * [a, b] &gt;= [c, d] results in [max(a, c), b]
	 * </p>
	 *
	 * @param other
	 *            The value to compare against.
	 * @return A new {@link IntervalDomainValue} that is the result of the greater or equal operation.
	 */
	@Override
	public IntervalDomainValue greaterOrEqual(final IntervalDomainValue other) {
		assert other != null;

		if (mIsBottom || other.mIsBottom) {
			return new IntervalDomainValue(true);
		}

		IntervalValue lowerMax;

		if (mLower.isInfinity() && other.mLower.isInfinity()) {
			lowerMax = new IntervalValue();
		} else {
			if (mLower.isInfinity()) {
				lowerMax = new IntervalValue(other.mLower);
			} else if (other.mLower.isInfinity()) {
				lowerMax = new IntervalValue(mLower);
			} else {
				if (mLower.getValue().compareTo(other.mLower.getValue()) > 0) {
					lowerMax = new IntervalValue(mLower);
				} else {
					lowerMax = new IntervalValue(other.mLower);
				}
			}
		}

		if (!lowerMax.isInfinity() && lowerMax.compareTo(mUpper) > 0) {
			return new IntervalDomainValue(true);
		}

		return new IntervalDomainValue(lowerMax, new IntervalValue(mUpper));
	}

	/**
	 * Computes the result of a less or equal operation with another interval:
	 * <p>
	 * [a, b] &lt;= [c, d] results in [a, min(b, d)]
	 * </p>
	 *
	 * @param other
	 *            The value to compare against.
	 * @return A new {@link IntervalDomainValue} that is the result of the less or equal operation.
	 */
	@Override
	public IntervalDomainValue lessOrEqual(final IntervalDomainValue other) {
		assert other != null;

		if (mIsBottom || other.mIsBottom) {
			return new IntervalDomainValue(true);
		}

		IntervalValue upperMin;

		if (mUpper.isInfinity()) {
			upperMin = new IntervalValue(other.mUpper);
		} else if (other.mUpper.isInfinity()) {
			upperMin = new IntervalValue(mUpper);
		} else {
			if (mUpper.getValue().compareTo(other.mUpper.getValue()) < 0) {
				upperMin = new IntervalValue(mUpper);
			} else {
				upperMin = new IntervalValue(other.mUpper);
			}
		}

		if (!mLower.isInfinity() && mLower.compareTo(upperMin) > 0) {
			return new IntervalDomainValue(true);
		}

		return new IntervalDomainValue(new IntervalValue(mLower), upperMin);
	}

	/**
	 * Compares <code>this</code> with another {@link IntervalDomainValue} for equality.
	 *
	 * @param other
	 *            The other value to compare to.
	 * @return <code>true</code> if and only if <code>this</code> and other are both bottom, or if the lower and upper
	 *         bounds are the same. <code>false</code> otherwise.
	 */
	@Override
	public boolean isEqualTo(final IntervalDomainValue other) {
		if (other == null) {
			return false;
		}

		if (other == this) {
			return true;
		}

		if (mIsBottom || other.mIsBottom) {
			return mIsBottom == other.mIsBottom;
		}

		return mLower.equals(other.mLower) && mUpper.equals(other.mUpper);
	}

	/**
	 * Compares <code>this</code> with another {@link IntervalDomainValue} and checks whether <code>this</code> is
	 * included in other, or vice versa.
	 *
	 * @param other
	 *            The other value to compare to.
	 * @return <code>true</code> if and only if either <code>this</code> is included in other, or vice versa,
	 *         <code>false</code> otherwise.
	 */
	public boolean isContainedInBoth(final IntervalDomainValue other) {
		assert other != null;

		if (isBottom() || other.isBottom()) {
			return true;
		}

		if (isInfinity() || other.isInfinity()) {
			return true;
		}

		if (mLower.isInfinity()) {
			return mUpper.compareTo(other.mUpper) >= 0;
		}

		if (other.mLower.isInfinity()) {
			return other.mUpper.compareTo(mUpper) >= 0;
		}

		return mLower.compareTo(other.mLower) <= 0 && mUpper.compareTo(other.mUpper) >= 0
				|| other.mLower.compareTo(mLower) <= 0 && other.mUpper.compareTo(mUpper) >= 0;
	}

	/**
	 * Compares <code>this</code> with another {@link IntervalDomainValue} and checks whether <code>this</code> is
	 * included in other.
	 *
	 * DD added this method to check for containment
	 *
	 * @param other
	 *            The other value to compare to.
	 * @return <code>true</code> if and only if <code>this</code> is included in other, <code>false</code> otherwise.
	 */
	@Override
	public boolean isContainedIn(final IntervalDomainValue other) {
		assert other != null;

		if (isBottom()) {
			return true;
		}
		if (other.isBottom()) {
			return false;
		}

		if (other.isInfinity()) {
			return true;
		}

		if (mLower.isInfinity() && !other.mLower.isInfinity()) {
			return false;
		}

		if (other.mLower.isInfinity()) {
			return mUpper.compareTo(other.mUpper) <= 0;
		}

		if (!mLower.isInfinity() && !other.mLower.isInfinity()) {
			return mLower.compareTo(other.mLower) >= 0 && mUpper.compareTo(other.mUpper) <= 0;
		}

		return mLower.compareTo(other.mLower) >= 0 && mUpper.compareTo(other.mUpper) <= 0;
	}

	/**
	 * @return <code>true</code> if and only if lower == upper and lower != &infin;. <code>false</code> otherwise.
	 */
	public boolean isPointInterval() {
		return !mLower.isInfinity() && mLower.compareTo(mUpper) == 0;
	}

	@Override
	public String toString() {
		if (mIsBottom) {
			return "{}";
		}

		final String lower = mLower.isInfinity() ? "-\\infty" : mLower.toString();
		final String upper = mUpper.isInfinity() ? "\\infty" : mUpper.toString();

		return new StringBuilder().append('[').append(lower).append(';').append(upper).append(']').toString();
	}

	/**
	 * Adds another {@link IntervalDomainValue} to <code>this</code> following the scheme:
	 *
	 * <p>
	 * <ul>
	 * <li>[a, b] + [c, d] = [a + c, b + d]</li>
	 * </ul>
	 * </p>
	 *
	 * @param other
	 *            The other interval.
	 * @return A new evaluation result corresponding to the addition of the two input intervals.
	 */
	@Override
	public IntervalDomainValue add(final IntervalDomainValue other) {

		assert other != null;

		if (isBottom() || other.isBottom()) {
			return new IntervalDomainValue(true);
		}

		if (isInfinity() || other.isInfinity()) {
			return new IntervalDomainValue();
		}

		final IntervalValue lowerBound = new IntervalValue();
		final IntervalValue upperBound = new IntervalValue();

		// Compute lower bound
		if (getLower().isInfinity() || other.getLower().isInfinity()) {
			lowerBound.setToInfinity();
		} else {
			lowerBound.setValue(getLower().getValue().add(other.getLower().getValue()));
		}

		// Compute upper bound
		if (getUpper().isInfinity() || other.getUpper().isInfinity()) {
			upperBound.setToInfinity();
		} else {
			upperBound.setValue(getUpper().getValue().add(other.getUpper().getValue()));
		}

		return new IntervalDomainValue(lowerBound, upperBound);
	}

	/**
	 * Returns <code>true</code> if and only if <code>0</code> is part of the interval.
	 *
	 * @return <code>true</code> if 0 is part of the interval, <code>false</code> otherwise.
	 */
	public boolean containsZero() {
		if (mIsBottom) {
			return false;
		}

		if (isInfinity()) {
			return true;
		}

		return (mLower.isInfinity() || mLower.getValue().signum() <= 0)
				&& (mUpper.isInfinity() || mUpper.getValue().signum() >= 0);
	}

	/**
	 * Returns the lower value of the interval.
	 *
	 * @return
	 */
	public IntervalValue getLower() {
		return mLower;
	}

	/**
	 * Returns the upper value of the interval.
	 *
	 * @return
	 */
	public IntervalValue getUpper() {
		return mUpper;
	}

	/**
	 * Intersects the current interval with another interval.
	 *
	 * @param other
	 *            The other interval to intersect with.
	 * @return A new {@link IntervalDomainValue} representing the result of the intersection.
	 */
	@Override
	public IntervalDomainValue intersect(final IntervalDomainValue other) {
		assert other != null;

		if (mIsBottom || other.mIsBottom) {
			return new IntervalDomainValue(true);
		}

		if (isInfinity() && other.isInfinity()) {
			return new IntervalDomainValue();
		}

		IntervalValue newLower;
		IntervalValue newUpper;

		if (mLower.compareTo(other.mLower) > 0) {
			if (mLower.isInfinity()) {
				newLower = new IntervalValue(other.mLower.getValue());
			} else {
				newLower = new IntervalValue(mLower.getValue());
			}
		} else if (mLower.compareTo(other.mLower) == 0) {
			if (mLower.isInfinity()) {
				newLower = new IntervalValue();
			} else {
				newLower = new IntervalValue(mLower.getValue());
			}
		} else {
			if (other.mLower.isInfinity()) {
				newLower = new IntervalValue(mLower.getValue());
			} else {
				newLower = new IntervalValue(other.mLower.getValue());
			}
		}

		if (mUpper.compareTo(other.mUpper) < 0) {
			newUpper = new IntervalValue(mUpper.getValue());
		} else if (mUpper.compareTo(other.mUpper) == 0) {
			if (mUpper.isInfinity()) {
				newUpper = new IntervalValue();
			} else {
				newUpper = new IntervalValue(mUpper.getValue());
			}
		} else {
			newUpper = new IntervalValue(other.mUpper.getValue());
		}

		if (!newLower.isInfinity() && newLower.compareTo(newUpper) > 0) {
			return new IntervalDomainValue(true);
		}

		if (!newUpper.isInfinity() && !newLower.isInfinity() && newUpper.compareTo(newLower) < 0) {
			return new IntervalDomainValue(true);
		}

		return new IntervalDomainValue(newLower, newUpper);
	}

	/**
	 * Computes the merger of this with another {@link IntervalDomainValue}.
	 *
	 * @param other
	 *            The other interval to merge with.
	 * @return A new interval which is the result of merging this with other.
	 */
	@Override
	public IntervalDomainValue merge(final IntervalDomainValue other) {
		assert other != null;

		final boolean thisIsBottom = isBottom();
		final boolean otherIsBottom = other.isBottom();

		if (thisIsBottom && !otherIsBottom) {
			return other.copy();
		}

		if (!thisIsBottom && otherIsBottom) {
			return copy();
		}

		if (isEqualTo(other)) {
			if (thisIsBottom) {
				return new IntervalDomainValue(true);
			} else if (isInfinity()) {
				return new IntervalDomainValue(new IntervalValue(), new IntervalValue());
			} else {
				IntervalValue newLower;
				if (mLower.isInfinity()) {
					newLower = new IntervalValue();
				} else {
					newLower = new IntervalValue(mLower.getValue());
				}

				IntervalValue newUpper;
				if (mUpper.isInfinity()) {
					newUpper = new IntervalValue();
				} else {
					newUpper = new IntervalValue(mUpper.getValue());
				}
				return new IntervalDomainValue(newLower, newUpper);
			}
		}

		IntervalValue lower;
		IntervalValue upper;

		if (mLower.isInfinity() || other.mLower.isInfinity()) {
			lower = new IntervalValue();
		} else {
			if (mLower.compareTo(other.mLower) < 0) {
				lower = new IntervalValue(mLower.getValue());
			} else {
				lower = new IntervalValue(other.mLower.getValue());
			}
		}

		if (mUpper.isInfinity() || other.mUpper.isInfinity()) {
			upper = new IntervalValue();
		} else {
			if (mUpper.compareTo(other.mUpper) < 0) {
				upper = new IntervalValue(other.mUpper.getValue());
			} else {
				upper = new IntervalValue(mUpper.getValue());
			}
		}

		return new IntervalDomainValue(lower, upper);
	}

	/**
	 * @return <code>true</code> if and only if the value is bottom, <code>false</code> otherwise.
	 */
	@Override
	public boolean isBottom() {
		return mIsBottom;
	}

	@Override
	public boolean isTop() {
		return isInfinity();
	}

	/**
	 * @return <code>true</code> if the interval is infinity, i.e. if the interval is (-&infin; ; &infin;).
	 */
	public boolean isInfinity() {
		if (mIsBottom) {
			return false;
		}
		return mLower.isInfinity() && mUpper.isInfinity();
	}

	/**
	 * Returns <code>true</code> if the interval is unbounded, i.e. if one bound of the interval is -&infin; or &infin;,
	 * respectively.
	 *
	 * @return <code>true</code> or <code>false</code>.
	 */
	public boolean isUnbounded() {
		if (mIsBottom) {
			return false;
		}
		return mLower.isInfinity() || mUpper.isInfinity();
	}

	/**
	 * Computes the result of the multiplication of another {@link IntervalDomainValue} with <code>this</code> following
	 * the scheme:
	 *
	 * <p>
	 * <ul>
	 * <li>[a, b] * [c, d] = [min(a*c, a*d, b*c, b*d), max(a*c, a*d, b*c, b*d)]</li>
	 * </ul>
	 * </p>
	 *
	 * @param other
	 *            The other interval.
	 * @return A new interval representing the result of <code>firstResult</code> * <code>secondRestult</code>.
	 */
	@Override
	public IntervalDomainValue multiply(final IntervalDomainValue other) {
		assert other != null;

		if (isBottom() || other.isBottom()) {
			return new IntervalDomainValue(true);
		}

		if (isPointInterval() && other.isPointInterval()) {
			final IntervalValue result = new IntervalValue(getLower().getValue().multiply(other.getLower().getValue()));
			return new IntervalDomainValue(result, result);
		}

		final IntervalValue lowerBound = computeMinMult(other);
		final IntervalValue upperBound = computeMaxMult(other);

		return new IntervalDomainValue(lowerBound, upperBound);
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
	 * Computes the subtraction of another {@link IntervalDomainValue} from <code>this</code> following the scheme:
	 * <p>
	 * <ul>
	 * <li>[a, b] - [c, d] = [a - d, b - c]</li>
	 * </ul>
	 * </p>
	 *
	 * @param other
	 *            The other interval.
	 * @return A new interval representing the result of <code>firstResult</code> - <code>secondResult</code>.
	 */
	@Override
	public IntervalDomainValue subtract(final IntervalDomainValue other) {
		assert other != null;

		if (isBottom() || other.isBottom()) {
			return new IntervalDomainValue(true);
		}

		if (isInfinity() || other.isInfinity()) {
			return new IntervalDomainValue();
		}

		final IntervalValue lowerBound = new IntervalValue();
		final IntervalValue upperBound = new IntervalValue();

		// Compute lower bound
		if (getLower().isInfinity() || other.getUpper().isInfinity()) {
			lowerBound.setToInfinity();
		} else {
			lowerBound.setValue(getLower().getValue().subtract(other.getUpper().getValue()));
		}

		// Compute upper bound
		if (getUpper().isInfinity() || other.getLower().isInfinity()) {
			upperBound.setToInfinity();
		} else {
			upperBound.setValue(getUpper().getValue().subtract(other.getLower().getValue()));
		}

		return new IntervalDomainValue(lowerBound, upperBound);
	}

	/**
	 * Computes the Euclidean modulo operation of two {@link IntervalDomainValue}s.
	 *
	 * @param divisor
	 *            The other value to compute the modulus for.
	 * @return A new {@link IntervalDomainValue} which corresponds to the application of the modulus operator.
	 */
	@Override
	public IntervalDomainValue modulo(final IntervalDomainValue divisor) {
		assert divisor != null;

		if (isBottom() || divisor.isBottom()) {
			return new IntervalDomainValue(true);
		}

		if (divisor.containsZero()) {
			// modulo is a total function in SMT, but (a % 0) is not specified
			// => result is an unknown but fixed value => return TOP
			return new IntervalDomainValue();
		}

		// If we are dealing with point intervals, the modulo computation is easy.
		if (isPointInterval() && divisor.isPointInterval()) {
			final BigDecimal remainder = AbsIntUtil.euclideanModulo(mLower.getValue(), divisor.mLower.getValue());
			return new IntervalDomainValue(new IntervalValue(remainder), new IntervalValue(remainder));
		}

		// The sign of the divisor does not matter for the euclidean modulo.
		final IntervalDomainValue absDivisor = divisor.abs();

		// [a; b] % [c; d] = [a; b], when (0 <= a) and (b < c)
		if (!mLower.isInfinity() && !absDivisor.mLower.isInfinity() && new IntervalValue(0).compareTo(mLower) <= 0
				&& mUpper.compareTo(absDivisor.mLower) < 0) {
			return new IntervalDomainValue(mLower, mUpper);
		}

		// Euclidean division x / y has a remainder r with 0 <= r < |y|.
		final IntervalValue min = new IntervalValue(0);
		final IntervalValue max = absDivisor.mUpper;
		if (!max.isInfinity()) {
			max.setValue(max.getValue().subtract(BigDecimal.ONE));
		}
		return new IntervalDomainValue(min, max);
	}

	/**
	 * Applies the absolute function on all values in this interval and creates a new interval from the results.
	 * <p>
	 * <table>
	 * <tr>
	 * <td>abs([a; b]) :=</td>
	 * <td>[0; max(|a|,|b|)]</td>
	 * <td>if [a; b] contains zero,</td>
	 * </tr>
	 * <tr>
	 * <td></td>
	 * <td>[min(|a|,|b|); max(|a|,|b|)]</td>
	 * <td>otherwise</td>
	 * </tr>
	 * </table>
	 * </p>
	 *
	 * @return Non-negative interval abs([a, b]).
	 */
	public IntervalDomainValue abs() {
		if (isBottom()) {
			return new IntervalDomainValue(true);
		}

		final boolean lowerIsInf = mLower.isInfinity();
		final boolean upperIsInf = mUpper.isInfinity();
		IntervalValue min;
		IntervalValue max;

		if (lowerIsInf || upperIsInf) {
			max = new IntervalValue();
			if (containsZero() || lowerIsInf && upperIsInf) {
				min = new IntervalValue(0);
			} else if (lowerIsInf) {
				// && !upperIsInf
				min = new IntervalValue(mUpper.getValue().abs());
			} else {
				// upperIsInf && !lowerIsInf
				min = new IntervalValue(mLower.getValue().abs());
			}
		} else {
			final BigDecimal a = mLower.getValue().abs();
			final BigDecimal b = mUpper.getValue().abs();
			min = new IntervalValue(containsZero() ? BigDecimal.ZERO : a.min(b));
			max = new IntervalValue(a.max(b));
		}
		return new IntervalDomainValue(min, max);
	}

	/**
	 * Negates the given interval.
	 *
	 * @param interval
	 *            The interval to negate.
	 * @return A new interval which corresponds to the negated input interval.
	 */
	@Override
	public IntervalDomainValue negate() {

		if (isBottom()) {
			return new IntervalDomainValue(true);
		}

		if (getLower().isInfinity() && getUpper().isInfinity()) {
			return new IntervalDomainValue();
		}

		if (getLower().isInfinity()) {
			return new IntervalDomainValue(new IntervalValue(getUpper().getValue().negate()), new IntervalValue());
		}

		if (getUpper().isInfinity()) {
			return new IntervalDomainValue(new IntervalValue(), new IntervalValue(getLower().getValue().negate()));
		}

		return new IntervalDomainValue(new IntervalValue(getUpper().getValue().negate()),
				new IntervalValue(getLower().getValue().negate()));
	}

	/**
	 * Returns an SMT {@link Term} of <code>this</code>.
	 *
	 * <p>
	 * Variables are expressed as var &geq; lowerBound, var &leq; upperBound. If a variable has no lower, or upper
	 * bound, no constraint is added. If a variable is &top;, <code>true</code> is used as term. If a variable is &bot;,
	 * <code>false</code> is used as term.
	 * </p>
	 *
	 * @param script
	 *            The script to use.
	 * @param sort
	 *            The sort to use.
	 * @param var
	 *            The term of the variable to use.
	 * @return A Term corresponding to the value.
	 */
	@Override
	public Term getTerm(final Script script, final Sort sort, final Term var) {
		assert sort.isNumericSort();
		if (isBottom()) {
			return script.term("false");
		} else if (mLower.isInfinity() && mUpper.isInfinity()) {
			return script.term("true");
		} else if (mLower.isInfinity()) {
			final Term value = mUpper.getTerm(sort, script);
			return script.term("<=", var, value);
		} else if (mUpper.isInfinity()) {
			final Term value = mLower.getTerm(sort, script);
			return script.term(">=", var, value);
		} else {
			final int cmp = mUpper.compareTo(mLower);
			if (cmp == 0) {
				// point-interval
				final Term value = mLower.getTerm(sort, script);
				return script.term("=", var, value);
			} else if (cmp < 0) {
				// upper less than lower, i.e. empty intervall
				return script.term("false");
			} else {
				// its a normal interval
				final Term upper = script.term("<=", var, mUpper.getTerm(sort, script));
				final Term lower = script.term(">=", var, mLower.getTerm(sort, script));
				// return SmtUtils.and(script, lower, upper);
				return script.term("and", lower, upper);
			}
		}
	}

	/**
	 * Computes the maximum value of the multiplication of two intervals:
	 *
	 * <p>
	 * [a, b] and [c, d]: max(ac, ad, bc, bd).
	 * </p>
	 *
	 * @param other
	 *            The other interval of the form [c, d].
	 * @return max(ac, ad, bc, bd).
	 */
	private IntervalValue computeMaxMult(final IntervalDomainValue other) {

		IntervalValue returnValue = new IntervalValue();
		boolean valuePresent = false;

		// If both intervals are infinite, the maximum is \infty.
		if (isInfinity() && other.isInfinity()) {
			return new IntervalValue();
		}

		// Compute a*c
		if (getLower().isInfinity()) {

			// -\infty * -\infty = \infty
			if (other.getLower().isInfinity()) {
				return new IntervalValue();
			}
			// -\infty * val = \infty, if val < 0
			if (other.getLower().getValue().signum() < 0) {
				return new IntervalValue();
			}

			// -\infty * 0 = 0
			if (other.getLower().getValue().signum() == 0) {
				returnValue = updateIfLarger(returnValue, BigDecimal.ZERO, valuePresent);
				valuePresent = true;
			}
		} else {
			if (other.getLower().isInfinity()) {
				// val * -\infty = \infty, if val < 0
				if (getLower().getValue().signum() < 0) {
					return new IntervalValue();
				}

				// 0 * -\infty = 0
				if (getLower().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfLarger(returnValue, getLower().getValue().multiply(other.getLower().getValue()),
						valuePresent);
				valuePresent = true;
			}
		}

		// Compute a*d
		if (getLower().isInfinity()) {
			if (!other.getUpper().isInfinity()) {
				// -\infty * val = \infty, if val < 0
				if (other.getUpper().getValue().signum() < 0) {
					return new IntervalValue();
				}

				// -\infty * 0 = 0
				if (other.getUpper().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			}
		} else {

			if (other.getUpper().isInfinity()) {
				// val * \infty = \infty, if val > 0
				if (getLower().getValue().signum() > 0) {
					return new IntervalValue();
				}

				// 0 * anything = 0
				if (getLower().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfLarger(returnValue, getLower().getValue().multiply(other.getUpper().getValue()),
						valuePresent);
				valuePresent = true;
			}
		}

		// Compute b*c
		if (getUpper().isInfinity()) {
			if (!other.getLower().isInfinity()) {
				// \infty * val = \infty, if val > 0
				if (other.getLower().getValue().signum() > 0) {
					return new IntervalValue();
				}

				// \infty * 0 = 0
				if (other.getLower().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			}
		} else {
			if (other.getLower().isInfinity()) {
				// val * -\infty = \infty, if val < 0
				if (getUpper().getValue().signum() < 0) {
					return new IntervalValue();
				}

				// 0 * anything = 0
				if (getUpper().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfLarger(returnValue, getUpper().getValue().multiply(other.getLower().getValue()),
						valuePresent);
				valuePresent = true;
			}
		}

		// Compute b*d
		if (getUpper().isInfinity()) {
			// \infty * \infty = \infty
			if (other.getUpper().isInfinity()) {
				return new IntervalValue();
			}
			// \infty * val = \infty, if val > 0
			if (other.getUpper().getValue().signum() > 0) {
				return new IntervalValue();
			}

			// \infty * 0 = 0
			if (other.getUpper().getValue().signum() == 0) {
				returnValue = updateIfLarger(returnValue, BigDecimal.ZERO, valuePresent);
				valuePresent = true;
			}
		} else {
			if (other.getUpper().isInfinity()) {
				// val * \infty = \infty, if val > 0
				if (getUpper().getValue().signum() > 0) {
					return new IntervalValue();
				}

				// 0 * \infty = 0
				if (getUpper().getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfLarger(returnValue, getUpper().getValue().multiply(other.getUpper().getValue()),
						valuePresent);
				valuePresent = true;
			}
		}

		assert valuePresent;
		return returnValue;
	}

	/**
	 * Computes the minimum value of the multiplication of two intervals:
	 *
	 * <p>
	 * [a, b] and [c, d]: min(ac, ad, bc, bd).
	 * </p>
	 *
	 * @param other
	 *            The other interval of the form [c, d].
	 * @return min(ac, ad, bc, bd).
	 */
	private IntervalValue computeMinMult(final IntervalDomainValue other) {

		IntervalValue returnValue = new IntervalValue();
		boolean valuePresent = false;

		// If both intervals are infinite, the minimum is \infty.
		if (isInfinity() && other.isInfinity()) {
			return new IntervalValue();
		}

		// Compute a*c
		if (getLower().isInfinity()) {
			if (!other.getLower().isInfinity()) {

				// -\infty * val = -\infty, if val > 0.
				if (other.getLower().getValue().signum() > 0) {
					return new IntervalValue();
				}

				// -\infty * val = 0, if val = 0.
				if (other.getLower().getValue().signum() == 0) {
					returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			}
		} else {

			// 0 * anything = 0.
			if (getLower().getValue().signum() == 0) {
				returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
				valuePresent = true;
			} else {
				if (other.getLower().isInfinity()) {

					// val * -\infty = -\infty, if val > 0
					if (getLower().getValue().signum() > 0) {
						return new IntervalValue();
					}
				} else {
					returnValue = updateIfSmaller(returnValue,
							getLower().getValue().multiply(other.getLower().getValue()), valuePresent);
					valuePresent = true;
				}
			}
		}

		// Compute a*d
		if (getLower().isInfinity()) {

			// -\infty * \infty = -\infty
			if (other.getUpper().isInfinity()) {
				return new IntervalValue();
			}

			// -\infty * val = -\infty, if val > 0
			if (other.getUpper().getValue().signum() > 0) {
				return new IntervalValue();
			}

			// anything * 0 = 0.
			if (other.getUpper().getValue().signum() == 0) {
				returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
				valuePresent = true;
			}
		} else {

			// 0 * anything = 0
			if (getLower().getValue().signum() == 0) {
				returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
				valuePresent = true;
			} else {
				if (other.getUpper().isInfinity()) {

					// val * \infty = -\infty, if val < 0
					if (getLower().getValue().signum() < 0) {
						return new IntervalValue();
					}
				} else {
					returnValue = updateIfSmaller(returnValue,
							getLower().getValue().multiply(other.getUpper().getValue()), valuePresent);
					valuePresent = true;
				}
			}
		}

		// Compute b*c
		if (getUpper().isInfinity()) {

			// \infty * -\infty = -\infty
			if (other.getLower().isInfinity()) {
				return new IntervalValue();
			}

			// \infty * val = -\infty, if val < 0
			if (other.getLower().getValue().signum() < 0) {
				return new IntervalValue();
			}

			// \infty * 0 = 0
			if (other.getLower().getValue().signum() == 0) {
				returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
				valuePresent = true;
			}
		} else {
			if (other.getLower().isInfinity()) {
				// val * -\infty = -\infty, if val > 0
				if (getUpper().getValue().signum() > 0) {
					return new IntervalValue();
				}

				// 0 * anything = 0
				if (getUpper().getValue().signum() == 0) {
					returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfSmaller(returnValue, getUpper().getValue().multiply(other.getLower().getValue()),
						valuePresent);
				valuePresent = true;
			}
		}

		// Compute b * d
		if (getUpper().isInfinity()) {
			if (!other.getUpper().isInfinity()) {

				// \infty * val = -\infty, if val < 0
				if (other.getUpper().getValue().signum() < 0) {
					return new IntervalValue();
				}

				if (other.getUpper().getValue().signum() == 0) {
					returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			}
		} else {
			if (other.getUpper().isInfinity()) {
				// val * \infty = -\infty, if val < 0
				if (getUpper().getValue().signum() < 0) {
					return new IntervalValue();
				}

				// 0 * \infty = 0
				if (getUpper().getValue().signum() == 0) {
					returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfSmaller(returnValue, getUpper().getValue().multiply(other.getUpper().getValue()),
						valuePresent);
				valuePresent = true;
			}
		}

		assert valuePresent;
		return returnValue;
	}

	private static IntervalValue updateIfLarger(final IntervalValue oldValue, final BigDecimal newValue,
			final boolean valuePresent) {
		if (valuePresent) {
			if (oldValue.getValue().compareTo(newValue) <= 0) {
				return new IntervalValue(newValue);
			}
			return oldValue;
		}
		return new IntervalValue(newValue);
	}

	private static IntervalValue updateIfSmaller(final IntervalValue oldValue, final BigDecimal newValue,
			final boolean valuePresent) {
		if (valuePresent) {
			if (oldValue.getValue().compareTo(newValue) >= 0) {
				return new IntervalValue(newValue);
			}
			return oldValue;
		}
		return new IntervalValue(newValue);
	}

	/**
	 * Performs the devision of <code>this</code> with the given {@link IntervalDomainValue} following the scheme:
	 *
	 * <p>
	 * [a; b] / [c; d] = [min(a / c, a / d, b / c, b / d); max(a / c, a / d, b / c, b / d)]
	 * </p>
	 *
	 * <p>
	 * If 0 is containd in [x; y], the resulting interval will always be (-&infin;; &infin;).
	 * </p>
	 *
	 * @param other
	 *            Another {@link IntervalDomainValue} of the form [x; y].
	 * @return A new {@link IntervalDomainValue} corresponding to the result of the computation of the division.
	 */
	@Override
	public IntervalDomainValue divide(final IntervalDomainValue other) {
		return divideInternally(other);
	}

	/**
	 * Performs the divison of <code>this</code> with the given {@link IntervalDomainValue}. The division is done using
	 * the euclidean method.
	 *
	 * @param other
	 *            Another {@link IntervalDomainValue} of the form [x; y].
	 * @return A new {@link IntervalDomainValue} corresponding to the result of the computation of the division.
	 */
	@Override
	public IntervalDomainValue divideInteger(final IntervalDomainValue other) {
		IntervalDomainValue result;

		if (other.containsZero()) {
			if (other.isPointInterval()) {
				return new IntervalDomainValue(true);
			}
		}

		// final IntervalDomainValue negZero = new IntervalDomainValue(other.getLower(),
		// new IntervalValue(new BigDecimal(-1)));
		// final IntervalDomainValue posZero = new IntervalDomainValue(new IntervalValue(BigDecimal.ONE),
		// other.getUpper());
		//
		// final IntervalDomainValue resultNeg = divideInternally(negZero);
		// final IntervalDomainValue resultPos = divideInternally(posZero);
		//
		// result = resultNeg.merge(resultPos);
		// } else {
		result = divideInternally(other);
		// }

		if (result.isBottom() || result.isInfinity()) {
			return result;
		}

		final IntervalValue lower = result.getLower();
		final IntervalValue upper = result.getUpper();

		IntervalValue newLower;
		IntervalValue newUpper;

		if (lower.isInfinity()) {
			newLower = lower;
		} else {
			newLower = new IntervalValue(lower.getValue().setScale(0, RoundingMode.FLOOR));
		}

		if (upper.isInfinity()) {
			newUpper = upper;
		} else {
			newUpper = new IntervalValue(upper.getValue().setScale(0, RoundingMode.CEILING));
		}

		return new IntervalDomainValue(newLower, newUpper);
	}

	private IntervalDomainValue divideInternally(final IntervalDomainValue other) {
		assert other != null;

		if (isBottom() || other.isBottom()) {
			return new IntervalDomainValue(true);
		}

		if (isPointInterval() && other.isPointInterval()) {
			if (other.getLower().getValue().signum() == 0) {
				return new IntervalDomainValue(true);
			}
			final IntervalValue result = new IntervalValue(divide(getLower().getValue(), other.getLower().getValue()));
			return new IntervalDomainValue(result, result);
		}

		if (other.containsZero()) {
			return new IntervalDomainValue();
		} // else {

		final IntervalValue lowerBound = computeMinDiv(other);
		final IntervalValue upperBound = computeMaxDiv(other);

		return new IntervalDomainValue(lowerBound, upperBound);
		// }
	}

	/**
	 * Computes the minimum value of the division of two intervals:
	 *
	 * <p>
	 * [a; b] and [c; d]: min(a / c, a / d, b / c, b / d).
	 * </p>
	 *
	 * @param other
	 *            The other interval of the form [c; d].
	 * @return min(a / c, a / d, b / c, b / d).
	 */
	private IntervalValue computeMinDiv(final IntervalDomainValue other) {
		// If both are infinity, the minimum is infinity.
		if (isInfinity() && other.isInfinity()) {
			return new IntervalValue();
		}

		IntervalValue returnValue = new IntervalValue();
		boolean valuePresent = false;

		final IntervalValue a = getLower();
		final IntervalValue b = getUpper();
		final IntervalValue c = other.getLower();
		final IntervalValue d = other.getUpper();

		// If the other interval contains infinity, we need 0 as a lower bound.
		if (c.isInfinity() || d.isInfinity()) {
			returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
			valuePresent = true;
		}

		// Compute a / c
		if (a.isInfinity()) {
			if (!c.isInfinity()) {
				// -\infty / val = -\infty, if val > 0
				if (c.getValue().signum() > 0) {
					return new IntervalValue();
				}
			}
		} else {
			// 0 / anything = 0.
			if (a.getValue().signum() == 0) {
				returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
				valuePresent = true;
			} else {
				if (c.isInfinity()) {
					// val / -\infty = -\infty, if val > 0
					if (a.getValue().signum() > 0) {
						return new IntervalValue();
					}
				} else {
					returnValue = updateIfSmaller(returnValue, divide(a.getValue(), c.getValue()), valuePresent);
					valuePresent = true;
				}
			}
		}

		// Compute a / d
		if (a.isInfinity()) {
			// -\infty / \infty = -\infty
			if (d.isInfinity()) {
				return new IntervalValue();
			}

			// -\infty / val = -\infty, if val > 0
			if (d.getValue().signum() > 0) {
				return new IntervalValue();
			}
		} else {
			// 0 / anything = 0
			if (a.getValue().signum() == 0) {
				returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
				valuePresent = true;
			} else {
				if (d.isInfinity()) {
					// val / \infty = -\infty, if val < 0
					if (a.getValue().signum() < 0) {
						return new IntervalValue();
					}
				} else {
					returnValue = updateIfSmaller(returnValue, divide(a.getValue(), d.getValue()), valuePresent);
				}
			}
		}

		// Compute b / c
		if (b.isInfinity()) {
			// \infty / -\infty = -\infty
			if (c.isInfinity()) {
				return new IntervalValue();
			}

			// \infty / val = -\infty, if val < 0
			if (c.getValue().signum() < 0) {
				return new IntervalValue();
			}
		} else {
			if (c.isInfinity()) {
				// val / -\infty = -\infty, if val > 0
				if (b.getValue().signum() > 0) {
					return new IntervalValue();
				}

				// 0 / anything = 0
				if (b.getValue().signum() == 0) {
					returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfSmaller(returnValue, divide(b.getValue(), c.getValue()), valuePresent);
				valuePresent = true;
			}
		}

		// Compute b / d
		if (b.isInfinity()) {
			if (!d.isInfinity()) {
				// \infty / val = -\infty, if val < 0
				if (d.getValue().signum() < 0) {
					return new IntervalValue();
				}
			}
		} else {
			if (d.isInfinity()) {
				// val / \infty = -\infty, if val < 0
				if (b.getValue().signum() < 0) {
					return new IntervalValue();
				}

				// 0 / anything = 0
				if (b.getValue().signum() == 0) {
					returnValue = updateIfSmaller(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfSmaller(returnValue, divide(b.getValue(), d.getValue()), valuePresent);
				valuePresent = true;
			}
		}

		assert valuePresent;
		return returnValue;
	}

	private static BigDecimal divide(final BigDecimal numerator, final BigDecimal divisor) {
		try {
			return numerator.divide(divisor);
		} catch (final ArithmeticException e) {
			return numerator.divide(divisor, MathContext.DECIMAL128);
		}
	}

	/**
	 * Computes the maximum value of the division of two interval values:
	 *
	 * <p>
	 * [a; b] and [c; d]: max(a / c, a / d, b / c, b / d).
	 * </p>
	 *
	 * @param other
	 *            The other interval of the form [c; d].
	 * @return max(a / c, a / d, b / c, b / d).
	 */
	private IntervalValue computeMaxDiv(final IntervalDomainValue other) {
		// If both are infinity, the maximum is infinity.
		if (isInfinity() && other.isInfinity()) {
			return new IntervalValue();
		}

		IntervalValue returnValue = new IntervalValue();
		boolean valuePresent = false;

		final IntervalValue a = getLower();
		final IntervalValue b = getUpper();
		final IntervalValue c = other.getLower();
		final IntervalValue d = other.getUpper();

		// If the other interval contains 0, max is a new upper bound
		if (other.containsZero()) {
			return new IntervalValue();
		}

		// Compute a / c
		if (a.isInfinity()) {
			// -\infty / -\infty = \infty
			if (c.isInfinity()) {
				return new IntervalValue();
			}
			// -\infty / val = \infty, if val < 0
			if (c.getValue().signum() < 0) {
				return new IntervalValue();
			}
		} else {
			if (c.isInfinity()) {
				// val / -\infty = \infty, if val < 0
				if (a.getValue().signum() < 0) {
					return new IntervalValue();
				}

				// 0 / -\infty = 0
				if (a.getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfLarger(returnValue, divide(a.getValue(), c.getValue()), valuePresent);
				valuePresent = true;
			}
		}

		// Compute a / d
		if (a.isInfinity()) {
			if (!d.isInfinity()) {
				// -\infty / val = \infty, if val < 0
				if (d.getValue().signum() < 0) {
					return new IntervalValue();
				}
			}
		} else {
			if (d.isInfinity()) {
				// val / \infty = \infty, if val > 0
				if (a.getValue().signum() > 0) {
					return new IntervalValue();
				}

				// 0 / anything = 0
				if (a.getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfLarger(returnValue, divide(a.getValue(), d.getValue()), valuePresent);
				valuePresent = true;
			}
		}

		// Compute b / c
		if (b.isInfinity()) {
			if (!c.isInfinity()) {
				// \infty / val = \infty, if val > 0
				if (c.getValue().signum() > 0) {
					return new IntervalValue();
				}
			}
		} else {
			if (c.isInfinity()) {
				// val / -\infty = \infty, if val < 0
				if (b.getValue().signum() < 0) {
					return new IntervalValue();
				}

				// 0 / anything = 0
				if (b.getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfLarger(returnValue, divide(b.getValue(), c.getValue()), valuePresent);
				valuePresent = true;
			}
		}

		// Compute b / d
		if (b.isInfinity()) {
			// \infty / \infty = \infty
			if (d.isInfinity()) {
				return new IntervalValue();
			}
			// \infty / val = \infty, if val > 0
			if (d.getValue().signum() > 0) {
				return new IntervalValue();
			}
		} else {
			if (d.isInfinity()) {
				// val / \infty = \infty, if val > 0
				if (b.getValue().signum() > 0) {
					return new IntervalValue();
				}

				// 0 / anything = 0
				if (b.getValue().signum() == 0) {
					returnValue = updateIfLarger(returnValue, BigDecimal.ZERO, valuePresent);
					valuePresent = true;
				}
			} else {
				returnValue = updateIfLarger(returnValue, divide(b.getValue(), d.getValue()), valuePresent);
				valuePresent = true;
			}
		}

		assert valuePresent;
		return returnValue;
	}

	@Override
	public IntervalDomainValue greaterThan(final IntervalDomainValue other) {
		return greaterOrEqual(other);
	}

	@Override
	public BooleanValue isGreaterThan(final IntervalDomainValue other) {
		return isGreaterOrEqual(other);
	}

	@Override
	public BooleanValue isGreaterOrEqual(final IntervalDomainValue other) {
		final IntervalDomainValue geq = greaterOrEqual(other);
		if (geq.isBottom() || geq.isPointInterval()) {
			return BooleanValue.TRUE;
		}
		return BooleanValue.TOP;
	}

	@Override
	public IntervalDomainValue lessThan(final IntervalDomainValue other) {
		return lessOrEqual(other);
	}

	@Override
	public BooleanValue isLessThan(final IntervalDomainValue other) {
		return isLessOrEqual(other);
	}

	@Override
	public BooleanValue isLessOrEqual(final IntervalDomainValue other) {
		final IntervalDomainValue leq = lessOrEqual(other);
		if (leq.isBottom() || leq.isPointInterval()) {
			return BooleanValue.TRUE;
		}
		return BooleanValue.TOP;
	}

	@Override
	public IntervalDomainValue inverseModulo(final IntervalDomainValue referenceValue,
			final IntervalDomainValue oldValue, final boolean isLeft) {
		return oldValue;
	}

	@Override
	public IntervalDomainValue inverseEquality(final IntervalDomainValue oldValue,
			final IntervalDomainValue referenceValue) {
		return referenceValue;
	}

	@Override
	public IntervalDomainValue inverseLessOrEqual(final IntervalDomainValue oldValue, final boolean isLeft) {
		final IntervalDomainValue newValue;
		if (isLeft) {
			newValue = new IntervalDomainValue(new IntervalValue(), getUpper());
		} else {
			newValue = new IntervalDomainValue(getLower(), new IntervalValue());
		}
		return newValue.intersect(oldValue);
	}

	@Override
	public IntervalDomainValue inverseLessThan(final IntervalDomainValue oldValue, final boolean isLeft) {
		return inverseLessOrEqual(oldValue, isLeft);
	}

	@Override
	public IntervalDomainValue inverseGreaterOrEqual(final IntervalDomainValue oldValue, final boolean isLeft) {
		final IntervalDomainValue newValue;
		if (isLeft) {
			newValue = new IntervalDomainValue(getLower(), new IntervalValue());
		} else {
			newValue = new IntervalDomainValue(new IntervalValue(), getUpper());
		}
		return newValue.intersect(oldValue);
	}

	@Override
	public IntervalDomainValue inverseGreaterThan(final IntervalDomainValue oldValue, final boolean isLeft) {
		return inverseGreaterOrEqual(oldValue, isLeft);
	}

	@Override
	public IntervalDomainValue inverseNotEqual(final IntervalDomainValue oldValue,
			final IntervalDomainValue referenceValue) {
		return referenceValue;
	}

	@Override
	public boolean canHandleReals() {
		return false;
	}

	@Override
	public boolean canHandleModulo() {
		return false;
	}

	@Override
	public BooleanValue compareEquality(final IntervalDomainValue secondOther) {
		if (isEqualTo(secondOther)) {
			return BooleanValue.TRUE;
		}
		return BooleanValue.TOP;
	}

	@Override
	public BooleanValue compareInequality(final IntervalDomainValue secondOther) {
		throw new UnsupportedOperationException(
				"Not equals expressions should have been removed during expression normalization.");
	}

	@Override
	public Collection<IntervalDomainValue> complement() {
		if (isBottom()) {
			return Collections.singleton(new IntervalDomainValue());
		}

		if (getLower().isInfinity() && getUpper().isInfinity()) {
			return Collections.singleton(new IntervalDomainValue(true));
		}

		if (getLower().isInfinity()) {
			return Collections
					.singleton(new IntervalDomainValue(new IntervalValue(getUpper().getValue()), new IntervalValue()));
		}

		if (getUpper().isInfinity()) {
			return Collections
					.singleton(new IntervalDomainValue(new IntervalValue(), new IntervalValue(getLower().getValue())));
		}

		final ArrayList<IntervalDomainValue> rtr = new ArrayList<>();
		rtr.add(new IntervalDomainValue(new IntervalValue(getUpper().getValue()), new IntervalValue()));
		rtr.add(new IntervalDomainValue(new IntervalValue(), new IntervalValue(getLower().getValue())));
		return rtr;
	}

	@Override
	public Collection<IntervalDomainValue> complementInteger() {
		if (isBottom()) {
			return Collections.singleton(new IntervalDomainValue());
		}

		if (getLower().isInfinity() && getUpper().isInfinity()) {
			return Collections.singleton(new IntervalDomainValue(true));
		}

		if (getLower().isInfinity()) {
			return Collections
					.singleton(new IntervalDomainValue(new IntervalValue(getUpper().getValue()), new IntervalValue()));
		}

		if (getUpper().isInfinity()) {
			return Collections
					.singleton(new IntervalDomainValue(new IntervalValue(), new IntervalValue(getLower().getValue())));
		}

		final ArrayList<IntervalDomainValue> rtr = new ArrayList<>();
		rtr.add(new IntervalDomainValue(new IntervalValue(getUpper().getValue().add(BigDecimal.ONE)),
				new IntervalValue()));
		rtr.add(new IntervalDomainValue(new IntervalValue(),
				new IntervalValue(getLower().getValue().subtract(BigDecimal.ONE))));
		return rtr;
	}

}
