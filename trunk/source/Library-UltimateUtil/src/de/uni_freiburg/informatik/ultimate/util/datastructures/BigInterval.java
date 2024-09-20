/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.math.BigInteger;
import java.util.List;

/**
 * Represents a non-empty interval of {@link BigInteger}s.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class BigInterval {
	private final BigInteger mMinValue;
	private final BigInteger mMaxValue;

	public BigInterval(final BigInteger minValue, final BigInteger maxValue) {
		mMinValue = minValue;
		mMaxValue = maxValue;
		assert mMinValue == null || mMaxValue == null
				|| maxValue.compareTo(minValue) >= 0 : "empty interval not supported";
	}

	public static BigInterval unbounded() {
		return new BigInterval(null, null);
	}

	public static BigInterval booleanRange() {
		return new BigInterval(BigInteger.ZERO, BigInteger.ONE);
	}

	public static BigInterval singleton(final BigInteger value) {
		return new BigInterval(value, value);
	}

	/**
	 * @return the minimum value in the interval, or {@code null} is the interval is unbounded from below
	 */
	public BigInteger getMinValue() {
		return mMinValue;
	}

	/**
	 * @return the maximum value in the interval, or {@code null} is the interval is unbounded from above
	 */
	public BigInteger getMaxValue() {
		return mMaxValue;
	}

	public BigInteger length() {
		return mMinValue != null && mMaxValue != null ? mMaxValue.subtract(mMinValue).add(BigInteger.ONE) : null;
	}

	public boolean isSingleton() {
		return mMinValue != null && mMaxValue != null && mMinValue.equals(mMaxValue);
	}

	public boolean isStrictlyPositive() {
		return mMinValue != null && mMinValue.signum() == 1;
	}

	public boolean isStrictlyNegative() {
		return mMaxValue != null && mMaxValue.signum() == -1;
	}

	public boolean isStrictlyNonNegative() {
		return mMaxValue != null && mMaxValue.signum() >= 0;
	}

	public boolean isStrictlyNonPositive() {
		return mMinValue != null && mMinValue.signum() <= 0;
	}

	public boolean contains(final BigInterval subset) {
		final boolean minBoundOk =
				mMinValue == null || (subset.mMinValue != null && mMinValue.compareTo(subset.mMinValue) <= 0);
		final boolean maxBoundOk =
				mMaxValue == null || (subset.mMaxValue != null && mMaxValue.compareTo(subset.mMaxValue) >= 0);
		return minBoundOk && maxBoundOk;
	}

	public boolean contains(final BigInteger element) {
		final boolean minBoundOk = mMinValue == null || mMinValue.compareTo(element) <= 0;
		final boolean maxBoundOk = mMaxValue == null || mMaxValue.compareTo(element) >= 0;
		return minBoundOk && maxBoundOk;
	}

	public BigInterval join(final BigInterval other) {
		final var minValue = mMinValue == null || other.mMinValue == null ? null : mMinValue.min(other.mMinValue);
		final var maxValue = mMaxValue == null || other.mMaxValue == null ? null : mMaxValue.max(other.mMaxValue);
		return new BigInterval(minValue, maxValue);
	}

	public BigInterval intersect(final BigInterval other) {
		final var minValue = mMinValue == null ? other.mMinValue
				: other.mMinValue == null ? mMinValue : mMinValue.max(other.mMinValue);
		final var maxValue = mMaxValue == null ? other.mMaxValue
				: other.mMaxValue == null ? mMaxValue : mMaxValue.min(other.mMaxValue);
		if (maxValue.compareTo(mMinValue) < 0) {
			// empty interval not supported
			return null;
		}
		return new BigInterval(minValue, maxValue);
	}

	public BigInterval negate() {
		final var minValue = mMaxValue == null ? null : mMaxValue.negate();
		final var maxValue = mMinValue == null ? null : mMinValue.negate();
		return new BigInterval(minValue, maxValue);
	}

	public BigInterval abs() {
		if (mMinValue != null && mMinValue.signum() >= 0) {
			// zero-or-positive interval
			return this;
		}
		if (mMaxValue != null && mMaxValue.signum() < 0) {
			// strictly negative interval
			return new BigInterval(mMaxValue.abs(), mMinValue == null ? null : mMinValue.abs());
		}

		assert contains(BigInteger.ZERO);
		final var maxValue = mMinValue == null || mMaxValue == null ? null
				: mMinValue.abs().compareTo(mMaxValue) >= 1 ? mMinValue.abs() : mMaxValue;
		return new BigInterval(BigInteger.ZERO, maxValue);
	}

	public BigInterval add(final BigInterval other) {
		final var minValue = mMinValue == null || other.getMinValue() == null ? null : mMinValue.add(other.mMinValue);
		final var maxValue = mMaxValue == null || other.getMaxValue() == null ? null : mMaxValue.add(other.mMaxValue);
		return new BigInterval(minValue, maxValue);
	}

	public BigInterval subtract(final BigInterval subtrahend) {
		final var minValue =
				mMinValue == null || subtrahend.mMaxValue == null ? null : mMinValue.subtract(subtrahend.mMaxValue);
		final var maxValue =
				mMaxValue == null || subtrahend.mMinValue == null ? null : mMaxValue.subtract(subtrahend.mMinValue);
		return new BigInterval(minValue, maxValue);
	}

	public BigInterval multiply(final BigInterval other) {
		if (mMinValue == null || mMaxValue == null || other.mMinValue == null || other.mMaxValue == null) {
			return BigInterval.unbounded();
		}
		final List<BigInteger> results =
				List.of(mMinValue.multiply(other.mMinValue), mMinValue.multiply(other.mMaxValue),
						mMaxValue.multiply(other.mMinValue), mMaxValue.multiply(other.mMaxValue));
		final var minValue = results.stream().min(BigInteger::compareTo).get();
		final var maxValue = results.stream().max(BigInteger::compareTo).get();
		return new BigInterval(minValue, maxValue);
	}

	public BigInterval euclideanDivide(final BigInterval divisor) {
		if (divisor.contains(BigInteger.ZERO)) {
			// Division by zero is unspecified, so we assume it can yield any number.
			return unbounded();
		}
		if (divisor.isStrictlyNegative()) {
			// Use property of euclidean division for negative divisors
			// (https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/)
			return euclideanDivide(divisor.negate()).negate();
		}

		assert divisor.isStrictlyPositive();

		final BigInteger minValue;
		if (mMinValue == null) {
			// If this interval is unbounded from below, the quotient interval (with positive divisor) will be as well.
			minValue = null;
		} else if (mMinValue.signum() < 0) {
			// If the lower bound is negative, divide it by the smallest possible (positive) value to get the new bound.
			minValue = euclideanDivide(mMinValue, divisor.mMinValue);
		} else if (divisor.mMaxValue != null) {
			// If the lower bound is positive or zero, divide it by the largest possible (positive) value.
			// This requires of course that there is a largest possible value in the divisor.
			minValue = euclideanDivide(mMinValue, divisor.mMaxValue);
		} else {
			// Final case: if the divisor is unbounded from above, the quotient can be as small as zero
			// (e.g. by taking the divisor to be mMinValue+1)
			minValue = BigInteger.ZERO;
		}

		final BigInteger maxValue;
		if (mMaxValue == null) {
			// If this interval is unbounded from below, the quotient interval (with positive divisor) will be as well.
			maxValue = null;
		} else if (mMaxValue.signum() >= 0) {
			// If the upper bound is positive or zero, divide it by the smallest possible (positive) value.
			maxValue = euclideanDivide(mMaxValue, divisor.mMinValue);
		} else if (divisor.mMaxValue != null) {
			// If the upper bound is negative, divide it by the largest possible (positive) value.
			// This requires of course that there is a largest possible value in the divisor.
			maxValue = euclideanDivide(mMaxValue, divisor.mMaxValue);
		} else {
			// Final case: if the divisor is unbounded from above, the quotient can be as large as zero
			// (e.g. by taking the divisor to be |mMaxValue|+1)
			maxValue = BigInteger.ZERO;
		}

		return new BigInterval(minValue, maxValue);
	}

	private static BigInteger euclideanDivide(final BigInteger dividend, final BigInteger divisor) {
		assert !BigInteger.ZERO.equals(divisor) : "divisor ZERO not supported";

		// https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/
		final var quotient = dividend.divide(divisor);
		if (dividend.signum() >= 0) {
			return quotient;
		}
		if (quotient.signum() > 0) {
			return quotient.subtract(BigInteger.ONE);
		}
		return quotient.add(BigInteger.ONE);
	}

	public BigInterval euclideanModulo(final BigInteger divisor) {
		assert !BigInteger.ZERO.equals(divisor) : "divisor ZERO not supported";

		// For euclidean modulo, divisors D and (- D) yield the same result. So we take the absolute value.
		// (https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/)
		final var absDivisor = divisor.abs();

		final var length = length();
		if (length != null && length.compareTo(absDivisor) < 0) {
			final var lowerMod = mMinValue.mod(absDivisor);
			final var upperMod = mMaxValue.mod(absDivisor);
			if (upperMod.compareTo(lowerMod) >= 0) {
				return new BigInterval(lowerMod, upperMod);
			}
		}

		// If the interval has infinite length or finite length >= divisor, we get the entire range for modulo.
		// Alternatively, the interval might have length < divisor, but contains both a k*divisor (modulo will be 0) and
		// k*divisor-1 (modulo will be divisor-1), so the smallest interval encompassing all values is the entire range.
		return new BigInterval(BigInteger.ZERO, absDivisor.subtract(BigInteger.ONE));
	}

	// Code adapted from https://stackoverflow.com/a/56918042 (there shown for truncating remainder)
	public BigInterval euclideanModulo(final BigInterval divisor) {
		if (divisor.contains(BigInteger.ZERO)) {
			// Modulo resp. division by zero is unspecified, so we assume it can yield any number.
			return unbounded();
		}

		if (divisor.isSingleton()) {
			return euclideanModulo(divisor.mMinValue);
		}

		// For euclidean modulo, divisors D and (- D) yield the same result. So we take the absolute value.
		// (https://www.microsoft.com/en-us/research/publication/division-and-modulus-for-computer-scientists/)
		final var absDivisor = divisor.abs();

		final var length = length();
		if (length != null && absDivisor.mMaxValue != null && length.compareTo(absDivisor.mMaxValue) >= 0) {
			// If length is greater than the largest possible divisor, the interval contains all possible mod values.
			return new BigInterval(BigInteger.ZERO, absDivisor.mMaxValue.subtract(BigInteger.ONE));
		}
		if (length != null && length.compareTo(absDivisor.mMinValue) >= 0) {
			// If the length is somewhere inside the interval of possible divisors, we split into two cases:
			// all divisors up to length, and all greater divisors.
			// For divisors up to length, we know (as in the previous case) that we can get all possible mod values (for
			// the new sub-interval of divisors); for divisors greater than length, we use a recursive call.
			// (NOTE that the recursion depth should be limited to 2, as length is outside the new sub-interval.)
			final var lowerHalf = new BigInterval(BigInteger.ZERO, length.subtract(BigInteger.ONE));
			final var upperHalf = euclideanModulo(new BigInterval(length.add(BigInteger.ONE), absDivisor.mMaxValue));
			return lowerHalf.join(upperHalf);
		}
		if (absDivisor.mMinValue.compareTo(mMaxValue) > 0) {
			// trivial case: modulo is guaranteed to have no effect
			return this;
		}
		if (absDivisor.mMaxValue != null && absDivisor.mMaxValue.compareTo(mMaxValue) > 0) {
			return new BigInterval(BigInteger.ZERO, mMaxValue);
		}

		// fallback to imprecise approximation
		return new BigInterval(BigInteger.ZERO,
				absDivisor.mMaxValue == null ? null : absDivisor.mMaxValue.subtract(BigInteger.ONE));
	}
}