/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.math.RoundingMode;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;

/**
 * Values for {@link OctMatrix} entries.
 * <p>
 * This is an extension of the real numbers R by the symbol "+infinity".
 * <p>
 * Octagons are represented by constraints of the form "(+/-) x (+/-) y <= c" where c is a constant and can be
 * represented by objects of this class.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OctValue implements Comparable<OctValue> {

	public static final OctValue INFINITY = new OctValue();
	public static final OctValue ONE = new OctValue(BigDecimal.ONE);
	public static final OctValue ZERO = new OctValue(BigDecimal.ZERO);

	/** Decimal value of this OctValue. {@code null} if and only if this OctValue is infinity. */
	private BigDecimal mValue;

	/** Creates a new OctValue with value infinity. */
	private OctValue() {
		// mValue is already null => represents infinity
	}

	/**
	 * Creates a new OctValue from an {@link IntervalValue}.
	 *
	 * @param ivlValue
	 *            value
	 */
	public OctValue(final IntervalValue ivlValue) {
		mValue = ivlValue.isInfinity() ? null : ivlValue.getValue();
	}

	/**
	 * Creates a new OctValue with a value less than infinity. Use {@link #INFINITY} to represent infinity.
	 *
	 * @param value
	 *            value less than infinity
	 */
	public OctValue(final BigDecimal value) {
		assert value != null : "Use constant INFINITY to represent infinity.";
		mValue = value;
	}

	/**
	 * Creates a new OctValue from an integer value.
	 *
	 * @param i
	 *            value
	 */
	public OctValue(final int i) {
		mValue = new BigDecimal(i);
	}

	/**
	 * Creates a new OctValue by parsing a string. Any numbers (integers and decimals) parsable by {@link BigDecimal}
	 * can be parsed. Infinity is represented as {@code "inf"}.
	 *
	 * @param s
	 *            Value (integer, decimal, or infinity) in textual representation
	 * @return New OctValue
	 */
	public static OctValue parse(final String s) {
		if ("inf".equals(s)) {
			return INFINITY;
		}
		return new OctValue(AbsIntUtil.sanitizeBigDecimalValue(s));
	}

	/**
	 * Converts this OctValue into an {@link IntervalValue}.
	 *
	 * @return IntervalValue
	 */
	public IntervalValue toIvlValue() {
		return mValue == null ? new IntervalValue() : new IntervalValue(mValue);
	}

	/** @return This value is infinity */
	public boolean isInfinity() {
		return mValue == null;
	}

	/**
	 * Returns the finite value of this OctValue, if available.
	 *
	 * @return Finite value or {@code null}
	 */
	public BigDecimal getValue() {
		return mValue;
	}

	public Rational toRational() {
		if (mValue == null) {
			return Rational.POSITIVE_INFINITY;
		}
		return SmtUtils.toRational(mValue);
	}
	
	/**
	 * Calculates the sum of this and another OctValue. The sum of infinity and something other is infinity.
	 *
	 * @param other
	 *            summand
	 * @return Sum
	 */
	public OctValue add(final OctValue other) {
		if (mValue == null || other.mValue == null) {
			return OctValue.INFINITY;
		}
		return new OctValue(mValue.add(other.mValue));
	}

	/**
	 * Calculates the difference of this and another OctValue. The difference of infinity and a finite value is
	 * infinity.
	 *
	 * @param other
	 *            (finite) subtrahend
	 * @return Difference
	 * @throws IllegalArgumentException
	 *             when subtracting infinity
	 */
	public OctValue subtract(final OctValue other) {
		if (other.mValue == null) {
			throw new IllegalArgumentException("Cannot subtract infinity.");
		} else if (mValue == null) {
			return OctValue.INFINITY;
		}
		return new OctValue(mValue.subtract(other.mValue));
	}

	/**
	 * Negates this OctValue.
	 *
	 * @return Negation
	 * @throws IllegalStateException
	 *             when this OctValue is infinity
	 */
	public OctValue negate() {
		if (mValue == null) {
			throw new IllegalStateException("Cannot negate infinity.");
		}
		return new OctValue(mValue.negate());
	}

	/**
	 * Negates this OctValue only if it is not infinity.
	 *
	 * @return Negation or infinity
	 */
	public OctValue negateIfNotInfinity() {
		if (mValue == null) {
			return this;
		}
		return new OctValue(mValue.negate());
	}

	/**
	 * Returns an {@linkplain OctValue} equal to {@code this / 2}. {@code  infinity / 2 = infinity}.
	 *
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
	 * Returns an {@linkplain OctValue} rounded towards {@code -infinity}. {@code infinity} is already rounded.
	 *
	 * @return floored {@linkplain OctValue}
	 */
	public OctValue floor() {
		if (mValue == null) {
			return OctValue.INFINITY;
		}
		return new OctValue(mValue.setScale(0, RoundingMode.FLOOR));
	}

	/**
	 * @return If the OctValue is infinity, return 1. Else, return -1, 0, or 1 as the value of this OctValue is
	 *         negative, zero, or positive.
	 */
	public int signum() {
		return mValue == null ? 1 : mValue.signum();
	}

	@SuppressWarnings("squid:S1698")
	@Override
	public int compareTo(final OctValue other) {
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
	public int hashCode() {
		final int prime = 31;
		return prime + ((mValue == null) ? 0 : mValue.hashCode());
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final OctValue other = (OctValue) obj;
		if (mValue == null) {
			if (other.mValue != null) {
				return false;
			}
		} else if (!mValue.equals(other.mValue)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		if (mValue == null) {
			return "inf";
		}
		return mValue.toString();
	}

	/**
	 * Return the smaller of the two {@link OctValue}s.
	 *
	 * @param a
	 *            The first operand.
	 * @param b
	 *            The second operand.
	 * @return The smaller value of a and b, or a if they have the same value.
	 */
	public static OctValue min(final OctValue a, final OctValue b) {
		return a.compareTo(b) <= 0 ? a : b;
	}

	/**
	 * Return the larger of the two {@link OctValue}s.
	 *
	 * @param a
	 *            The first operand.
	 * @param b
	 *            The second operand.
	 * @return The larger value of a and b, or a if they have the same value.
	 */
	public static OctValue max(final OctValue a, final OctValue b) {
		return a.compareTo(b) >= 0 ? a : b;
	}

}
