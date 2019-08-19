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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;

/**
 * A value in the interval domain for abstract interpretation. This value can be of any numbered type or can be
 * infinity.
 *
 * <p>
 * For interpreting values, one must always account for possible infinity. If {@link #isInfinity()} returns
 * <code>true</code>, the value obtained through {@link #getValue()} must be ignored as it is unsound.
 * </p>
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalValue implements Comparable<IntervalValue> {

	private static int sId;
	private final int mId;

	private final BigDecimal mValue;

	private final boolean mIsInfty;

	/**
	 * Constructor for a new {@link IntervalValue}. The value is set to infinity (&infin;) initially.
	 */
	public IntervalValue() {
		mIsInfty = true;
		mValue = null;
		sId++;
		mId = sId;
	}

	/**
	 * Constructor for a new {@link IntervalValue} that sets the value to a provided value.
	 *
	 * @param val
	 *            The value to set.
	 */
	public IntervalValue(final BigDecimal val) {
		if (val == null) {
			throw new IllegalArgumentException("val may not be null");
		}
		mValue = val;
		mIsInfty = false;
		sId++;
		mId = sId;
	}

	/**
	 * Constructor for a new {@link IntervalValue} that sets the value to a provided value.
	 *
	 * @param val
	 *            The value to set.
	 */
	public IntervalValue(final IntervalValue val) {
		mValue = val.mValue;
		mIsInfty = val.mIsInfty;
		sId++;
		mId = sId;
	}

	/**
	 * Constructor for a new {@link IntervalValue} that sets the value to the provided value.
	 *
	 * @param val
	 *            The value to set.
	 */
	public IntervalValue(final int val) {
		this(new BigDecimal(val));
	}

	/**
	 * Constructor for a new {@link IntervalValue} that sets the value to the provided value.
	 *
	 * @param val
	 *            The value to set.
	 */
	public IntervalValue(final double val) {
		this(new BigDecimal(val));
	}

	/**
	 * Constructor for a new {@link IntervalValue} that sets the value to a provided value of type string. May throw an
	 * exception if the provided string is not parsable.
	 *
	 * @param val
	 *            The value to set.
	 */
	public IntervalValue(final String val) {
		this(AbsIntUtil.sanitizeBigDecimalValue(val));
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
	public BigDecimal getValue() {
		return mValue;
	}

	/**
	 * Returns <code>true</code> if the value is corresponding to infinity, <code>false</code> otherwise.
	 *
	 * @return <code>true</code> or <code>false</code>
	 */
	public boolean isInfinity() {
		return mIsInfty;
	}

	/**
	 * Multiply two {@link IntervalValue}s.
	 *
	 * @param a
	 *            The first operand.
	 * @param b
	 *            The second operand.
	 * @return The result of a * b.
	 */
	public static IntervalValue multiply(final IntervalValue a, final IntervalValue b) {
		if (a == null || b == null) {
			throw new IllegalArgumentException("Arguments may not be null");
		}

		if (a.isInfinity() && b.isInfinity()) {
			// is infinity
			return new IntervalValue();
		}

		if (a.isInfinity()) {
			if (b.getValue().signum() == 0) {
				// infinity times 0 is 0
				return new IntervalValue(0);
			}
			// infinity times something is infinity
			return new IntervalValue();
		}

		if (b.isInfinity()) {
			if (a.getValue().signum() == 0) {
				return new IntervalValue(0);
			}
			return new IntervalValue();
		}

		// neither a nor b are infinity, thus a.getValue() has always a value
		return new IntervalValue(a.getValue().multiply(b.getValue()));
	}

	@Override
	public boolean equals(final Object other) {
		if (other == null) {
			return false;
		}

		if (!(other instanceof IntervalValue)) {
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
		return mId;
	}

	@Override
	public int compareTo(final IntervalValue other) {

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

	public Term getTerm(final Sort sort, final Script script) {
		assert !isInfinity() : "Cannot convert infinity to Term";
		assert SmtSortUtils.isNumericSort(sort) : "Sort has to be numeric";
		if (SmtSortUtils.isIntSort(sort)) {
			return SmtUtils.constructIntValue(script, mValue.toBigIntegerExact());
		}
		assert SmtSortUtils.isRealSort(sort) : "Seems that numeric sort now has something different then Int or Real";
		// has to be real
		return script.decimal(mValue);
	}

	public IntervalValue add(final IntervalValue other) {
		if (isInfinity()) {
			return this;
		}
		if (other.isInfinity()) {
			return other;
		}
		return new IntervalValue(getValue().add(other.getValue()));
	}

	public IntervalValue subtract(final IntervalValue other) {
		if (isInfinity()) {
			return this;
		}
		if (other.isInfinity()) {
			return other;
		}
		return new IntervalValue(getValue().subtract(other.getValue()));
	}
}
