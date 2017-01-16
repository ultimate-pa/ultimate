package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util;

import java.math.BigDecimal;
import java.math.BigInteger;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Tests for {@link NumUtil}.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class NumUtilTest {

	@Test
	public void testIntDivModRandomized() {
		final int scale = 26;
		for (int i = 0; i < 1_000_000; ++i) {
			final BigDecimal a = new BigDecimal((int) (Math.random() * scale) - (scale / 2));
			final BigDecimal b = new BigDecimal((int) (Math.random() * scale) - (scale / 2));
			if (b.signum() == 0) {
				continue;
			}
			final BigInteger ai = a.toBigIntegerExact();
			final BigInteger bi = b.toBigIntegerExact();
			final BigInteger qi = AbsIntUtil.euclideanDivision(a, b).toBigIntegerExact();
			final BigInteger ri = ai.subtract(bi.multiply(qi));
			if (ai.compareTo(qi.multiply(bi).add(ri)) != 0) {
				Assert.fail("was " + a + " = " + b + " * " + qi + " R " + ri);
			}
			final BigDecimal mod = AbsIntUtil.euclideanModulo(a, b);
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
	public void testEuclideanDivison() {
		// divisible integers (euclidean division should equal any other division)
		assertIntDiv("+12", "+4", "+3");
		assertIntDiv("+12", "-4", "-3");
		assertIntDiv("-12", "+4", "-3");
		assertIntDiv("-12", "-4", "+3");

		// fractions
		assertIntDiv("+7", "+3", "+2");
		assertIntDiv("+7", "-3", "-2");
		assertIntDiv("-7", "+3", "-3");
		assertIntDiv("-7", "-3", "+3");

		// divisible floats
		assertIntDiv("+7.5", "+.3", "+25");
		assertIntDiv("+7.5", "-.3", "-25");
		assertIntDiv("-7.5", "+.3", "-25");
		assertIntDiv("-7.5", "-.3", "+25");

		// fractions
		assertIntDiv("+7.6", "+.3", "+25");
		assertIntDiv("+7.6", "-.3", "-25");
		assertIntDiv("-7.6", "+.3", "-26");
		assertIntDiv("-7.6", "-.3", "+26");

		try {
			AbsIntUtil.euclideanDivision(BigDecimal.ONE, BigDecimal.ZERO);
			Assert.fail("Computed 1 / 0");
		} catch (final ArithmeticException e) {}
		try {
			AbsIntUtil.euclideanDivision(BigDecimal.ZERO, BigDecimal.ZERO);
			Assert.fail("Computed 0 / 0");
		} catch (final ArithmeticException e) {}
	}
	
	@Test
	public void testEuclideanModulo() {
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

		try {
			AbsIntUtil.euclideanModulo(BigDecimal.ONE, BigDecimal.ZERO);
			Assert.fail("Computed 1 % 0");
		} catch (final ArithmeticException e) {}
		try {
			AbsIntUtil.euclideanModulo(BigDecimal.ZERO, BigDecimal.ZERO);
			Assert.fail("Computed 0 % 0");
		} catch (final ArithmeticException e) {}
	}

	@Test
	public void testDecimalFraction() {
		assertDecimalFraction( "1.5",     "15",   "10");
		assertDecimalFraction("-1.5",    "-15",   "10");
		assertDecimalFraction("20.0",    "200",   "10");
		assertDecimalFraction( "20",      "20",    "1");
		assertDecimalFraction(  "2e1",    "20",    "1");
		assertDecimalFraction(  "0.03",    "3",  "100");
		assertDecimalFraction(  "0.030",  "30", "1000");
		assertDecimalFraction( "-0.030", "-30", "1000");
		assertDecimalFraction(  "0",       "0",    "1");
		assertDecimalFraction(  "0.0",     "0",   "10");
		assertDecimalFraction(  "0e9",     "0",    "1");
	}

	// assert a / b = q
	private void assertIntDiv(String a, String b, String qExpected) {
		final BigDecimal qActual = AbsIntUtil.euclideanDivision(new BigDecimal(a), new BigDecimal(b));
		if (qActual.compareTo(new BigDecimal(qExpected)) != 0) {
			Assert.fail(String.format("%s / %s: expected %s but was %s", a, b, qExpected, qActual));
		}
	}

	// assert a % b = r
	private void assertMod(String a, String b, String rExpected) {
		final BigDecimal rActual = AbsIntUtil.euclideanModulo(new BigDecimal(a), new BigDecimal(b));
		if (rActual.compareTo(new BigDecimal(rExpected)) != 0) {
			Assert.fail(String.format("%s %% %s: expected %s but was %s", a, b, rExpected, rActual));
		}
	}

	// assert d = expectedDecimalFraction
	private void assertDecimalFraction(String d, String nomExpected, String denomExpected) {
		final Pair<BigInteger, BigInteger> fActual = AbsIntUtil.decimalFraction(new BigDecimal(d));
		final Pair<BigInteger, BigInteger> fExpected = new Pair<>(new BigInteger(nomExpected), new BigInteger(denomExpected));
		if (!fExpected.equals(fActual)) {
			Assert.fail(String.format("decimalFraction(%s): expected %s/%s but was %s/%s",
					d, nomExpected, denomExpected, fActual.getFirst(), fActual.getSecond()));
		}
	}
}
