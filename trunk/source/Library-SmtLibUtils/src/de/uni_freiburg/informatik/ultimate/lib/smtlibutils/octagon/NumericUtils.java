package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.octagon;

import java.math.BigDecimal;

public class NumericUtils {
	private NumericUtils() {
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
	 * Accounts for found problems when passing values by string directly to BigDecimal, in order to avoid
	 * NumberFormatExceptions.
	 *
	 * @param val
	 *            The value as string.
	 * @return A new {@link BigDecimal} object that contains the given value. It is also possible that an exception is
	 *         thrown when the object is created if the given value is invalid or not handled.
	 */
	public static BigDecimal sanitizeBigDecimalValue(final String val) {
		if (val.contains("/")) {
			final String[] twoParts = val.split("/");
			if (twoParts.length != 2) {
				throw new NumberFormatException("Not a valid division value: " + val);
			}
			final BigDecimal one = new BigDecimal(twoParts[0]);
			final BigDecimal two = new BigDecimal(twoParts[1]);
			return one.divide(two);
		}
		return new BigDecimal(val);
	}
}
