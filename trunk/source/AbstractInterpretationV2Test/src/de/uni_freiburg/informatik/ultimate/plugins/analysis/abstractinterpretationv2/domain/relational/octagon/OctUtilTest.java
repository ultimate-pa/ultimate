package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.math.BigInteger;

import org.junit.Assert;
import org.junit.Test;

public class OctUtilTest {

	@Test
	public void testEuclideanIntegerDivisonRandomized() {
		double scale = 500;
		for (int i = 0; i < 1e6; ++i) {
			BigDecimal a = new BigDecimal((int) (Math.random() * scale) - (scale / 2));
			BigDecimal b = new BigDecimal((int) (Math.random() * scale) - (scale / 2));
			if (b.signum() == 0) {
				continue;
			}
			BigInteger ai = a.toBigIntegerExact();
			BigInteger bi = b.toBigIntegerExact();
			BigInteger q = OctUtil.euclideanIntegerDivision(a, b).toBigIntegerExact();
			BigInteger r = ai.subtract(bi.multiply(q));
			if (ai.compareTo(q.multiply(bi).add(r)) != 0) {
				Assert.fail(a + " = " + b + " * " + q + " R " + r);
			}
		}
	}

	@Test
	public void testEuclideanIntegerDivisonManually() {
		BigDecimal p7 = new BigDecimal(7);
		BigDecimal p3 = new BigDecimal(3);
		BigDecimal n7 = new BigDecimal(-7);
		BigDecimal n3 = new BigDecimal(-3);
		assertDiv(p7, p3,  2);
		assertDiv(p7, n3, -2);
		assertDiv(n7, p3, -3);
		assertDiv(n7, n3,  3);
	}
	
	// assert a / b = q
	private void assertDiv(BigDecimal a, BigDecimal b, int qExpected) {
		BigDecimal qActual = OctUtil.euclideanIntegerDivision(a, b);
		BigDecimal qExp = new BigDecimal(qExpected);
		if (qActual.compareTo(qExp) != 0) {
			Assert.fail(a + " / " + b + ": expected " + qExpected + " but was " + qActual);
		}
	}
	
	
	
}
