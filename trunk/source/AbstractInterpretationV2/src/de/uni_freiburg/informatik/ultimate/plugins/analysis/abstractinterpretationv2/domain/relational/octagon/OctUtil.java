package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;

public class OctUtil {

	public static BigDecimal euclideanIntegerDivision(BigDecimal a, BigDecimal b) {
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

}
