package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

public class Util {
	public static Long SMTDiv(final long m, final long n) {
		final Rational div = Rational.valueOf(m, n);
		if (n > 0) {
			// n > 0, (div m n) = floor(m/n)
			final Rational floorExact = div.floor();
			return floorExact.numerator().longValue() / floorExact.denominator().longValue();
		}
		// n < 0, (div m n) = ceil(m/n)
		final Rational ceilExact = div.ceil();
		return ceilExact.numerator().longValue() / ceilExact.denominator().longValue();
	}

	public static Long SMTMod(final Long m, final Long n) {
		// i == ((i / j) * j) + (i % j)
		// i % j == i - ((i / j) * j)
		final Rational div = Rational.valueOf(Util.SMTDiv(m, n), 1L);
		final Rational mSafe = Rational.valueOf(m, 1L);
		final Rational nSafe = Rational.valueOf(n, 1L);
		final Rational result = mSafe.sub(div.mul(nSafe));
		return result.numerator().longValueExact(); // should be long because all used numbers are long
	}

	public static int getBitVecLength(final Sort sort) {
		if (!sort.isBitVecSort()) {
			return -1;
		}
		return Integer.parseInt(sort.getIndices()[0]);
	}
}
