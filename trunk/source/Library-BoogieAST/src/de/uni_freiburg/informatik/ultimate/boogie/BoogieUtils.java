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
package de.uni_freiburg.informatik.ultimate.boogie;

import java.math.BigInteger;

/**
 * Static methods auxiliary methods for Boogie.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public final class BoogieUtils {

	private BoogieUtils() {
		// do not instantiate this utility class
	}
	
	public static BigInteger euclideanMod(final BigInteger dividend, final BigInteger divisor) {
		return dividend.mod(divisor.abs());
	}
	
	public static BigInteger euclideanDiv(final BigInteger dividend, final BigInteger divisor) {
		final BigInteger nonEuclideanQuotient = dividend.divide(divisor);
		final BigInteger nonEuclideanRemainder = dividend.remainder(divisor);
		final BigInteger result;
		if (nonEuclideanRemainder.signum() < 0) {
			if (nonEuclideanQuotient.signum() > 0) {
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
}
