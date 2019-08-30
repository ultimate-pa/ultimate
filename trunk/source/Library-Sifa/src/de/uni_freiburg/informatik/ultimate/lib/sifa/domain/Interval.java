/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.domain;

import java.util.Objects;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Interval with inclusive, rational bounds.
 * Bounds can be infinity to represent half intervals and even the whole number space
 * (known as TOP in abstract interpretation). Bounds cannot be NaN.
 * Single NaN values can be represented using the empty interval.
 * Point intervals behave like regular Rationals, even for the special values like infinity.
 * <p>
 * If not stated otherwise arithmetic methods in this class return the least over-approximation.
 * That is, for two intervals lhsInput and rhsInput and a function f
 * result = lhsInput.f(rhsInput) is the least interval such that result ⊇ {l | l ∊ lhsInput, r ∊ rhsInput, f(l,r)}.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public final class Interval {

	/**
	 * The interval containing everything.
	 * Top intervals are unified, so {@code someInterval == TOP} can be used instead of {@link #isTop()}.
	 */
	public static final Interval TOP = new Interval(Rational.NEGATIVE_INFINITY, Rational.POSITIVE_INFINITY);
	/**
	 * The empty interval containing nothing.
	 * Bottom intervals are unified, so {@code someInterval == BOTTOM} can be used instead of {@link #isBottom()}.
	 */
	public static final Interval BOTTOM = new Interval(Rational.ONE, Rational.ZERO);
	/** The point interval containing only 0. */
	public static final Interval ZERO = new Interval(Rational.ZERO);
	/** The point interval containing only 1. */
	public static final Interval ONE = new Interval(Rational.ONE);

	/** Lower bound of this interval, inclusive. */
	private final Rational mLower;
	/** Upper bound of this interval, inclusive. */
	private final Rational mUpper;

	private Interval(final Rational point) {
		this(point, point);
	}

	private Interval(final Rational lower, final Rational upper) {
		mLower = lower;
		mUpper = upper;
	}

	public static Interval point(final Rational point) {
		return Interval.of(point, point);
	}

	public static Interval of(final Rational lower, final Rational upper) {
		// filter out illegal values and unify often used intervals
		if (isNan(lower) || isNan(upper) || lower.compareTo(upper) > 0) {
			return BOTTOM;
		} else if (isNegInf(lower) && isPosInf(upper)) {
			return TOP;
		}
		return new Interval(lower, upper);
	}

	public boolean hasLower() {
		return mLower.isRational();
	}

	public boolean hasUpper() {
		return mUpper.isRational();
	}

	public Rational getLower() {
		return mLower;
	}

	public Rational getUpper() {
		return mUpper;
	}

	public boolean isBottom() {
		assert (this == BOTTOM) == (mLower.compareTo(mUpper) > 0) : "Empty interval was not unified";
		return this == BOTTOM;
	}

	public boolean isPoint() {
		return mLower.equals(mUpper);
	}

	public boolean containsZero() {
		return mLower.signum() <= 0 && mUpper.signum() >= 0;
	}

	public boolean isTop() {
		assert (this == TOP) == (isNegInf(mLower) && isPosInf(mUpper)) : "Top interval was not unified";
		return this == TOP;
	}

	public Interval negate() {
		return Interval.of(mUpper.negate(), mLower.negate());
	}

	public Interval add(final Interval rhs) {
		// [a, b] + [c, d] = [a + c, b + d]
		return Interval.of(mLower.add(rhs.mLower), mUpper.add(rhs.mUpper));
	}

	public Interval subtract(final Interval rhs) {
		// [a, b] - [c, d] = [a - d, b - c]
		return Interval.of(mLower.sub(rhs.mUpper), mUpper.sub(rhs.mLower));
	}

	public Interval multiply(final Interval rhs) {
		// [a, b] * [c, d] = [min(a*c, a*d, b*c, b*d), max(a*c, a*d, b*c, b*d)]
		return minMaxFromCartesianOp(rhs, Rational::mul);
	}

	public Interval divide(final Interval rhs) {
		// [a, b] / [c, d] = [min(a/c, a/d, b/c, b/d), max(a/c, a/d, b/c, b/d)]
		if (rhs.containsZero()) {
			return TOP;
		}
		return minMaxFromCartesianOp(rhs, Rational::div);
	}

	private Interval minMaxFromCartesianOp(final Interval rhs, final BiFunction<Rational, Rational, Rational> op) {
		final Rational ll = op.apply(mLower, rhs.mLower);
		final Rational lu = op.apply(mLower, rhs.mUpper);
		final Rational ul = op.apply(mUpper, rhs.mLower);
		final Rational uu = op.apply(mUpper, rhs.mUpper);
		return Interval.of(min(min(ll, lu), min(ul, uu)),  max(max(ll, lu), max(ul, uu)));
	}

	public SatisfyingInputs satisfyEqual(final Interval rhs) {
		return new SatisfyingInputs(intersect(rhs));
	}

	public SatisfyingInputs satisfyDistinct(final Interval rhs) {
		if (isPoint() && rhs.isPoint() && mLower.equals(rhs.mLower)) {
			return new SatisfyingInputs(BOTTOM);
		}
		return new SatisfyingInputs(this, rhs);
	}

	public SatisfyingInputs satisfyLessOrEqual(final Interval rhs) {
		return new SatisfyingInputs(
			Interval.of(mLower, min(mUpper, rhs.mUpper)),
			Interval.of(max(rhs.mLower, mLower), rhs.mUpper)
		);
	}

	public SatisfyingInputs satisfyGreaterOrEqual(final Interval rhs) {
		return rhs.satisfyLessOrEqual(this).swap();
	}

	public Interval union(final Interval rhs) {
		return Interval.of(min(mLower, rhs.mLower), max(mUpper, rhs.mUpper));
	}

	public Interval widen(final Interval rhs) {
		return Interval.of(
			rhs.mLower.compareTo(mLower) < 0 ? Rational.NEGATIVE_INFINITY : mLower,
			mUpper.compareTo(rhs.mUpper) < 0 ?  mUpper : Rational.POSITIVE_INFINITY
		);
	}

	public Interval intersect(final Interval rhs) {
		return Interval.of(max(mLower, rhs.mLower), min(mUpper, rhs.mUpper));
	}

	public Interval complement() {
		final boolean unboundLeft = isNegInf(mLower);
		final boolean unboundRight = isPosInf(mUpper);
		if (unboundLeft && !unboundRight) {
			return Interval.of(mUpper, Rational.POSITIVE_INFINITY);
		} else if (!unboundLeft && unboundRight) {
			return Interval.of(Rational.NEGATIVE_INFINITY, mLower);
		} else if (isBottom()) {
			return TOP;
		}
		return BOTTOM;
	}

	// TODO implement modulo, euclidean division and so on

	@Override
	public int hashCode() {
		return Objects.hash(mLower, mUpper);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (getClass() != obj.getClass()) {
			return false;
		}
		final Interval other = (Interval) obj;
		// this would return false for two different empty intervals (for instance [1,0] and [2,1])
		// but since BOTTOM is unified this is not a problem
		return Objects.equals(mLower, other.mLower) && Objects.equals(mUpper, other.mUpper);
	}

	@Override
	public String toString() {
		if (isBottom()) {
			return "∅";
		}
		return String.format("[%s, %s]", mLower, mUpper);
	}

	// helper methods for single Rational values.
	// TODO Consider moving these methods to SmtUtils or some other global util class

	private static boolean isNan(final Rational r) {
		final boolean result = r == Rational.NAN;
		assert result == (!r.isRational() && r.signum() == 0);
		return result;
	}
	private static boolean isPosInf(final Rational r) {
		final boolean result = r == Rational.POSITIVE_INFINITY;
		assert result == (!r.isRational() && r.signum() > 0);
		return result;
	}
	private static boolean isNegInf(final Rational r) {
		final boolean result = r == Rational.NEGATIVE_INFINITY;
		assert result == (!r.isRational() && r.signum() < 0);
		return result;
	}
	private static Rational max(final Rational r1, final Rational r2) {
		if (isNan(r1) || isNan(r2)) {
			return Rational.NAN;
		}
		return r1.compareTo(r2) > 0 ? r1 : r2;
	}
	private static Rational min(final Rational r1, final Rational r2) {
		if (isNan(r1) || isNan(r2)) {
			return Rational.NAN;
		}
		return r1.compareTo(r2) < 0 ? r1 : r2;
	}

	/**
	 * Given two intervals lhsInput and rhsInput and a relation R, represents the following two intervals.
	 * <ul>
	 * <li> lhs is the least interval such that lhs ⊇ {l | l ∊ lhsInput, r ∊ rhsInput, l R r}
	 * <li> rhs is the least interval such that rhs ⊇ {r | l ∊ lhsInput, r ∊ rhsInput, l R r}
	 * </ul>
	 *
	 * @author schaetzc@tf.uni-freiburg.de
	 */
	public static class SatisfyingInputs {
		private final Interval mLhs;
		private final Interval mRhs;
		public SatisfyingInputs(final Interval lhsAndRhs) {
			this(lhsAndRhs, lhsAndRhs);
		}
		public SatisfyingInputs(final Interval lhs, final Interval rhs) {
			mLhs = lhs;
			mRhs = rhs;
		}
		protected SatisfyingInputs swap() {
			return new SatisfyingInputs(mRhs, mLhs);
		}
		public Interval getLhs() {
			return mLhs;
		}
		public Interval getRhs() {
			return mRhs;
		}
		@Override
		public int hashCode() {
			return Objects.hash(mLhs, mRhs);
		}
		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			} else if (obj == null) {
				return false;
			} else if (getClass() != obj.getClass()) {
				return false;
			}
			final SatisfyingInputs other = (SatisfyingInputs) obj;
			return Objects.equals(mLhs, other.mLhs) && Objects.equals(mRhs, other.mRhs);
		}
		@Override
		public String toString() {
			return String.format("%s R %s", mLhs, mRhs);
		}
	}

}
