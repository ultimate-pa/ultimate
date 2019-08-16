/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.domain;

import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Interval with inclusive, rational bounds.
 * Bounds can be infinity to represent half intervals and even the whole number space
 * (known as TOP in abstract interpretation). Bounds cannot be NaN.
 * Single NaN values can be represented using the empty interval.
 * Point intervals behave like regular Rationals, even for the special values like infinity.
 *
 * TODO document that many methods (e.g. division, complement) return the least over-approximation
 * TODO test methods
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class Interval {

	public static final Interval TOP = new Interval(Rational.NEGATIVE_INFINITY, Rational.POSITIVE_INFINITY);
	public static final Interval BOTTOM = new Interval(Rational.ONE, Rational.ZERO);
	public static final Interval ZERO = new Interval(Rational.ZERO);
	public static final Interval ONE = new Interval(Rational.ONE);

	private final Rational mLower;
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
		// filter out illegal values
		if (isNan(lower) || isNan(upper)) {
			return BOTTOM;
		}
		// unify often used intervals
		if (isNegInf(lower) && isPosInf(upper)) {
			return TOP;
		}
		return new Interval(lower, upper);
	}

	public Rational getLower() {
		return mLower;
	}

	public Rational getUpper() {
		return mUpper;
	}

	public boolean isBottom() {
		return this == BOTTOM || mLower.compareTo(mUpper) > 0;
	}

	public boolean isPoint() {
		return mLower.compareTo(mUpper) == 0;
	}

	public boolean containsZero() {
		return mLower.signum() <= 0 && mUpper.signum() >= 0;
	}

	public boolean isTop() {
		return this == TOP || mLower.compareTo(Rational.NEGATIVE_INFINITY) == 0;
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

	public Interval setMinus(final Interval rhs) {
		// TODO implement if needed
		return rhs; // over-approximation
	}

	public Interval union(final Interval rhs) {
		return Interval.of(min(mLower, rhs.mLower), max(mUpper, rhs.mUpper));
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

}
