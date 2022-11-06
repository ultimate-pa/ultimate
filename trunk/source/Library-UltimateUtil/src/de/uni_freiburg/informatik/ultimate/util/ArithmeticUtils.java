/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.math.BigInteger;

/**
 * This class provides static methods that implement algorithms for Java's
 * arithmetic data types.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public final class ArithmeticUtils {

	private ArithmeticUtils() {
		// do not instantiate this utility class
	}

	/**
	 * There exist several definitions the division operation and the modulo
	 * operation. The Euclidean modulo is the modulo operation whose result is
	 * always positive E.g., -8 modulo 7 is 6, because we have that -2*7+6=-8.
	 *
	 */
	public static BigInteger euclideanMod(final BigInteger dividend, final BigInteger divisor) {
		return dividend.mod(divisor.abs());
	}

	/**
	 * There exist several definitions the division operation and the modulo
	 * operation. The Euclidean division is the divison operation whose remainder is
	 * always positive E.g., -8 div 7 is -2, because we have that -2*7+6=-8.
	 */
	public static BigInteger euclideanDiv(final BigInteger dividend, final BigInteger divisor) {
		final BigInteger nonEuclideanQuotient = dividend.divide(divisor);
		final BigInteger nonEuclideanRemainder = dividend.remainder(divisor);
		final BigInteger result;
		if (nonEuclideanRemainder.signum() < 0) {
			if (divisor.signum() < 0) {
				result = nonEuclideanQuotient.add(BigInteger.ONE);
			} else {
				result = nonEuclideanQuotient.subtract(BigInteger.ONE);
			}
		} else {
			result = nonEuclideanQuotient;
		}
		assert result.multiply(divisor).add(euclideanMod(dividend, divisor)).equals(dividend)
				: "incorrect euclidean division";
		return result;
	}

	/**
	 * The input `a` is the number for which the inverse should be found the divisor
	 * is the integer which defines the field 0 <= a and a < divisor and
	 * gcd(divisor, a) = 1
	 *
	 * @param a
	 * @param divisor
	 * @return
	 */
	public static BigInteger extendedEuclidean(BigInteger a, BigInteger divisor) {
		if (a.equals(BigInteger.valueOf(0))) {
			throw new IllegalArgumentException("0 does not have a multiplicative inverse");
		}
		if (a.compareTo(divisor) >= 0) {
			BigInteger newa = a.mod(divisor);
			extendedEuclidean(newa, divisor);
		}
		// inverse of a in the field Z/divisorZ
		BigInteger inverse = BigInteger.valueOf(0);
		BigInteger remainder = divisor;
		BigInteger newInverse = BigInteger.valueOf(1);
		BigInteger newRemainder = a;
		BigInteger oldRemainder;
		BigInteger oldInverse;
		BigInteger quotient;
		while (!newRemainder.equals(BigInteger.valueOf(0))) {
			// while-loop ends if remainder = 1
			quotient = remainder.divide(newRemainder);
			// update the inverse
			oldInverse = inverse;
			inverse = newInverse;
			newInverse = oldInverse.subtract(quotient.multiply(newInverse));
			// update the remainder
			oldRemainder = remainder;
			remainder = newRemainder;
			newRemainder = oldRemainder.subtract(quotient.multiply(newRemainder));
		}
		// gcd(a, divisor) > 1
		if (remainder.compareTo(BigInteger.valueOf(1)) > 0) {
			throw new IllegalArgumentException("a has no multiplicative inverse mod divisor");
		}
		if (inverse.compareTo(BigInteger.valueOf(0)) < 0) {
			inverse = inverse.add(divisor);
		}
		// Check if result is inverse of (a mod divisor)
		assert ((inverse.multiply(a)).mod(divisor)).equals(BigInteger.valueOf(1));
		return inverse;
	}
}
