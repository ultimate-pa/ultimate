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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.awt.dnd.InvalidDnDOperationException;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluationResult;

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
	 * Constructor for a new {@link IntervalDomainValue}. The interval created
	 * will be (-&infin; ; &infin;).
	 */
	protected IntervalDomainValue() {
		this(false);
	}

	/**
	 * Constructor for a new {@link IntervalDomainValue}. The interval created
	 * is dependent on the value of the parameter. If {@code isBottom} is set to
	 * <code>false</code>, the created interval will be (-&infin; ; &infin;). If
	 * {@code isBottom} is set to <code>true</code>, the created interval will
	 * be &bot;.
	 * 
	 * @param isBottom
	 *            Specifies whether the interval should be &bot; or an actual
	 *            interval.
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
		if (!lower.isInfinity() && !upper.isInfinity()) {
			if (lower.getValue().compareTo(upper.getValue()) > 0) {
				throw new UnsupportedOperationException(
						"The lower value must be smaller than or qual to the upper value. Lower: " + lower.getValue()
								+ ", Upper: " + upper.getValue());
			}
		}

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
	 * Note that a return value of <code>false</code> may also mean that one or
	 * both of the interval bounds is -&infin; or &infin;.
	 * 
	 * @return <code>true</code> if the current interval is &bot;,
	 *         <code>false</code> otherwise.
	 */
	protected boolean isBottom() {
		return mIsBottom;
	}

	/**
	 * Returns <code>true</code> if the interval is unbounded, i.e. if one bound
	 * of the interval is -&infin; or &infin;, respectively.
	 * 
	 * @return <code>true</code> or <code>false</code>.
	 */
	protected boolean isUnbounded() {
		if (mIsBottom) {
			return false;
		}
		return mLower.isInfinity() || mUpper.isInfinity();
	}

	/**
	 * @return <code>true</code> if the interval is infinity, i.e. if the
	 *         interval is (-&infin; ; &infin;).
	 */
	protected boolean isInfinity() {
		if (mIsBottom) {
			return false;
		}
		return mLower.isInfinity() && mUpper.isInfinity();
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

	/**
	 * Returns <code>true</code> if and only if <code>0</code> is part of the
	 * interval.
	 * 
	 * @return <code>true</code> if 0 is part of the interval,
	 *         <code>false</code> otherwise.
	 */
	protected boolean containsZero() {
		if (mIsBottom) {
			return false;
		}

		if (isInfinity()) {
			return true;
		}

		return mLower.getValue().signum() <= 0 && mUpper.getValue().signum() >= 0;
	}

	@Override
	public IntervalDomainValue getResult() {
		return this;
	}

	@Override
	public int compareTo(IntervalDomainValue o) {
		throw new InvalidDnDOperationException(
				"The compareTo operation is not defined on arbitrary intervals and can therefore not be used.");
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
