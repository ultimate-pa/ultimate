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

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

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

	private static int sId = 0;
	private final int mId;

	private BigDecimal mValue;

	private boolean mIsInfty;

	/**
	 * Constructor for a new {@link IntervalValue}. The value is set to infinity (&infin;) initially.
	 */
	protected IntervalValue() {
		mIsInfty = true;
		sId++;
		mId = sId;
	}

	/**
	 * Constructor for a new {@link IntervalValue} that sets the value to a provided value.
	 * 
	 * @param val
	 *            The value to set.
	 */
	protected IntervalValue(BigDecimal val) {
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
	protected IntervalValue(IntervalValue val) {
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
	protected IntervalValue(int val) {
		this(new BigDecimal(val));
	}

	/**
	 * Constructor for a new {@link IntervalValue} that sets the value to the provided value.
	 * 
	 * @param val
	 *            The value to set.
	 */
	protected IntervalValue(double val) {
		this(new BigDecimal(val));
	}

	/**
	 * Constructor for a new {@link IntervalValue} that sets the value to a provided value of type string. May throw an
	 * exception if the provided string is not parsable.
	 * 
	 * @param val
	 *            The value to set.
	 */
	protected IntervalValue(String val) {
		this(new BigDecimal(val));
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
		return mId;
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

	public Term getTerm(final Sort sort, final Script script) {
		assert !isInfinity() : "Cannot convert infinity to Term";
		assert sort.isNumericSort() : "Sort has to be numeric";
		if (sort.getName().equals("Int")) {
			return script.numeral(mValue.toBigIntegerExact());
		} else {
			assert sort.getName()
			        .equals("Real") : "Seems that numeric sort now has something different then Int or Real";
			// has to be real
			return script.decimal(mValue);
		}
	}
}
