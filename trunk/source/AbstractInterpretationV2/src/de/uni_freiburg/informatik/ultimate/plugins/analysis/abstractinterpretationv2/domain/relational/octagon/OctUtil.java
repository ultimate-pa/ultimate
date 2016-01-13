package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;

public class OctUtil {

	public static BigDecimal euclideanIntegerDivision(BigDecimal a, BigDecimal b) {
		assert isIntegral(a) && isIntegral(b) : "Integer divison for reals.";
		BigDecimal[] quotientAndRemainder = a.divideAndRemainder(b);
		BigDecimal quotient = quotientAndRemainder[0];
		BigDecimal remainder = quotientAndRemainder[1];
		if (remainder.signum() != 0) {
			if (a.signum() < 0) { // sig(a) != 0, since "remainder != 0"
				if (b.signum() < 0) { // sig(b) != 0, since "a / 0" throws an exception
					quotient = quotient.add(BigDecimal.ONE);
				} else {
					quotient = quotient.subtract(BigDecimal.ONE);
				}
			}
		}
		return quotient;
	}
	
	public static BigDecimal exactIntegerDivison(BigDecimal a, BigDecimal b) {
		assert isIntegral(a) && isIntegral(b) : "Integer divison for reals.";
		BigDecimal[] quotientAndRemainder = a.divideAndRemainder(b);
		if (quotientAndRemainder[1].signum() == 0) {
			return quotientAndRemainder[0];
		}
		throw new ArithmeticException("Integer divison is not exact.");
	}
	
	public static boolean isIntegral(BigDecimal d) {
		return d.remainder(BigDecimal.ONE).signum() == 0;

		// alternative implementation (takes 4 times longer)
//		try {
//			d.setScale(0, RoundingMode.UNNECESSARY);
//			return true;
//		} catch (ArithmeticException e) {
//			return false;
//		}
	}

	public static BigDecimal euclideanModulo(BigDecimal a, BigDecimal b) {
		BigDecimal r = a.remainder(b);
		if (r.signum() < 0) {
			r = r.add(b.abs());
		}
		return r;
	}

}
