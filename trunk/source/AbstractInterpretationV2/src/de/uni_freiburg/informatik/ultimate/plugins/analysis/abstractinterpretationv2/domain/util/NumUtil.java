/*
 * Copyright (C) 2016 Claus Schätzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Utility functions for BigDecimal calculations, i.e. Euclidean division and modulo operations
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public final class NumUtil {

	public static final BigDecimal TWO = new BigDecimal(2);

	private NumUtil() {
		// do not instantiate utility class
	}

	/**
	 * Calculates the euclidean division.euc The result {@code q} of the euclidean division {@code a / b = q} satisfies
	 * {@code a = bq + r} where {@code 0 ≤ r < |b|} and {@code b ≠ 0}.
	 * <p>
	 * The type of division only matters for non-real numbers like integers or floats with limited precision.
	 * <p>
	 * Examples:<br>
	 * <code>
	 *     +7 / +3 = +2<br>
	 *     +7 / -3 = -2<br>
	 *     -7 / +3 = -3<br>
	 *     -7 / -3 = +3
	 * </code>
	 *
	 * @param a
	 *            dividend
	 * @param b
	 *            divisor
	 * @return euclidean division {@code q = a / b}
	 *
	 * @throws ArithmeticException
	 *             if {@code b = 0}
	 */
	public static BigDecimal euclideanDivision(final BigDecimal a, final BigDecimal b) {
		final BigDecimal[] quotientAndRemainder = a.divideAndRemainder(b);
		BigDecimal quotient = quotientAndRemainder[0];
		final BigDecimal remainder = quotientAndRemainder[1];
		if (remainder.signum() != 0 && a.signum() < 0) {
			// sig(a) != 0, since "remainder != 0"
			if (b.signum() < 0) {
				// sig(b) != 0, since "a / 0" throws an exception
				quotient = quotient.add(BigDecimal.ONE);
			} else {
				quotient = quotient.subtract(BigDecimal.ONE);
			}
		}
		return quotient;
	}

	/**
	 * Calculates {@code a / b} only if {@code b} is a divisor of {@code a}.
	 *
	 * @param a
	 *            dividend
	 * @param b
	 *            true divisor of {@code a}
	 * @return exact result of {@code a / b} (always an integer)
	 *
	 * @throws ArithmeticException
	 *             if {@code b} is a not a divisor of {@code a}.
	 */
	public static BigDecimal exactDivison(final BigDecimal a, final BigDecimal b) {
		final BigDecimal[] quotientAndRemainder = a.divideAndRemainder(b);
		if (quotientAndRemainder[1].signum() == 0) {
			return quotientAndRemainder[0];
		}
		throw new ArithmeticException("Divison not exact.");
	}

	/**
	 * Checks if a number is integral.
	 *
	 * @param d
	 *            number
	 * @return {@code d} is an integer
	 */
	public static boolean isIntegral(final BigDecimal d) {
		return d.remainder(BigDecimal.ONE).signum() == 0;
	}

	/**
	 * Calculates the euclidean modulo. The result {@code r} is the remainder of the euclidean division
	 * {@code a / b = q}, satisfying {@code a = bq + r} where {@code 0 ≤ r < |b|} and {@code b ≠ 0}.
	 * <p>
	 * Examples:<br>
	 * <code>
	 *     +7 % +3 = 1<br>
	 *     +7 % -3 = 1<br>
	 *     -7 % +3 = 2<br>
	 *     -7 % -3 = 2
	 * </code>
	 *
	 * @param a
	 *            dividend
	 * @param b
	 *            divisor
	 * @return {@code r = a % b} (remainder of the euclidean division {@code a / b})
	 *
	 * @throws ArithmeticException
	 *             if {@code b = 0}
	 */
	public static BigDecimal euclideanModulo(final BigDecimal a, final BigDecimal b) {
		BigDecimal r = a.remainder(b);
		if (r.signum() < 0) {
			r = r.add(b.abs());
		}
		return r;
	}

	/**
	 * Turns a BigDecimal d into its decimal fraction d = numerator / denominator. Numerator and denominator are both
	 * integers and denominator is a positive power of 10. Trailing zeros are not removed (can be done by
	 * {@link BigDecimal#stripTrailingZeros()} in advance).
	 * <p>
	 * Examples:<br>
	 *
	 * <pre>
	 *  1.5   =  15 /   10
	 * -1.5   = -15 /   10
	 * 20.0   = 200 /   10
	 * 20     =  20 /    1
	 *  2e1   =  20 /    1
	 *  0.03  =   3 /  100
	 *  0.030 =  30 / 1000
	 *  0e9   =   0 /    1
	 * </pre>
	 *
	 * @param d
	 *            BigDecimal
	 * @return decimal fraction
	 */
	public static Pair<BigInteger, BigInteger> decimalFraction(final BigDecimal d) {
		BigInteger numerator = d.unscaledValue();
		BigInteger denominator = BigInteger.TEN.pow(Math.abs(d.scale()));
		if (d.scale() < 0) {
			numerator = numerator.multiply(denominator);
			denominator = BigInteger.ONE;
		}
		return new Pair<>(numerator, denominator);
	}
}
