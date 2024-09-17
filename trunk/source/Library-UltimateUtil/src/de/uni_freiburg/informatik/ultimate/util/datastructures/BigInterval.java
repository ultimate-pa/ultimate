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
		return mMinValue != null && mMinValue.signum() >= 1;
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

	public BigInterval divide(final BigInterval divisor) {
		// TODO Dominik 2024-09-15 unsure if this is sound (when some bounds are negative)
		final var minValue =
				mMinValue == null || divisor.mMaxValue == null ? null : mMinValue.divide(divisor.mMaxValue);
		final var maxValue =
				mMaxValue == null || divisor.mMinValue == null ? null : mMaxValue.divide(divisor.mMinValue);
		return new BigInterval(minValue, maxValue);
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
}