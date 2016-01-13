package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.math.BigInteger;

import org.junit.Assert;
import org.junit.Test;

public class OctUtilTest {

	@Test
	public void testIntDivModRandomized() {
		double scale = 26;
		for (int i = 0; i < 1_000_000; ++i) {
			BigDecimal a = new BigDecimal((int) (Math.random() * scale) - (scale / 2));
			BigDecimal b = new BigDecimal((int) (Math.random() * scale) - (scale / 2));
			if (b.signum() == 0) {
				continue;
			}
			BigInteger ai = a.toBigIntegerExact();
			BigInteger bi = b.toBigIntegerExact();
			BigInteger qi = OctUtil.euclideanIntegerDivision(a, b).toBigIntegerExact();
			BigInteger ri = ai.subtract(bi.multiply(qi));
			if (ai.compareTo(qi.multiply(bi).add(ri)) != 0) {
				Assert.fail("was " + a + " = " + b + " * " + qi + " R " + ri);
			}
			BigDecimal mod = OctUtil.euclideanModulo(a, b);
			if (a.compareTo(new BigDecimal(qi).multiply(b).add(mod)) != 0) {
				String msg = "expected a = (a/b)*b + a%b but was ...\n";
				msg += "a  : " + ai + "\n";
				msg += "  b: " + bi + "\n";
				msg += "a/b: " + qi + "\n";
				msg += "a%b: " + mod;
				Assert.fail(msg);
			}
		}
	}

	@Test
	public void testEuclideanIntegerDivisonManually() {
		// divisible integers
		assertIntDiv("+12", "+4", "+3");
		assertIntDiv("+12", "-4", "-3");
		assertIntDiv("-12", "+4", "-3");
		assertIntDiv("-12", "-4", "+3");

		// fractions
		assertIntDiv("+7", "+3", "+2");
		assertIntDiv("+7", "-3", "-2");
		assertIntDiv("-7", "+3", "-3");
		assertIntDiv("-7", "-3", "+3");

	}
	
	@Test
	public void testModulo() {
		assertMod("+7", "+3", "1");
		assertMod("+7", "-3", "1");
		assertMod("-7", "+3", "2");
		assertMod("-7", "-3", "2");

		assertMod("+4.2", "+1.1", "0.9");
		assertMod("+4.2", "-1.1", "0.9");
		assertMod("-4.2", "+1.1", "0.2");
		assertMod("-4.2", "-1.1", "0.2");

		assertMod("0", "5", "0");
		assertMod("0", "-5", "0");
	}

	// assert a / b = q
	private void assertIntDiv(String a, String b, String qExpected) {
		BigDecimal qActual = OctUtil.euclideanIntegerDivision(new BigDecimal(a), new BigDecimal(b));
		if (qActual.compareTo(new BigDecimal(qExpected)) != 0) {
			Assert.fail(String.format("%s %% %s: expected %s but was %s", a, b, qExpected, qActual));
		}
	}
	
	
	// assert a % b = r
	private void assertMod(String a, String b, String rExpected) {
		BigDecimal rActual = OctUtil.euclideanModulo(new BigDecimal(a), new BigDecimal(b));
		if (rActual.compareTo(new BigDecimal(rExpected)) != 0) {
			Assert.fail(String.format("%s %% %s: expected %s but was %s", a, b, rExpected, rActual));
		}
	}
}
