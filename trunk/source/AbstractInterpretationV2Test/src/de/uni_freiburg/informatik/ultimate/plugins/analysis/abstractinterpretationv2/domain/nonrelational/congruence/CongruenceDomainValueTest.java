package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.math.BigInteger;

import org.junit.Test;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */

public class CongruenceDomainValueTest {

	private static final String STR_BOT = "{}";
	private static final String STR_ZERO = "0";
	private static final String STR_1Z = "1Z";
	private static final String STR_1Z_NO_ZERO = "1Z \\ {0}";
	private static final String STR_2Z = "2Z";
	private static final String STR_2Z_NO_ZERO = "2Z \\ {0}";
	private static final String STR_4Z = "4Z";
	private static final String STR_4Z_NO_ZERO = "4Z \\ {0}";

	private static final CongruenceDomainValue BOT = CongruenceDomainValue.createBottom();
	private static final CongruenceDomainValue TOP = CongruenceDomainValue.createTop();
	private static final CongruenceDomainValue ZERO = CongruenceDomainValue.createConstant(BigInteger.ZERO);
	private static final CongruenceDomainValue MINUS_ONE = CongruenceDomainValue.createConstant(BigInteger.valueOf(-1));
	private static final CongruenceDomainValue FIVE = CongruenceDomainValue.createConstant(BigInteger.valueOf(5));

	@Test
	public void testCreate() {
		CongruenceDomainValue x = TOP;
		assertEquals(STR_1Z, x.toString());
		x = BOT;
		assertEquals(STR_BOT, x.toString());
		x = FIVE;
		assertEquals("5", x.toString());
		x = MINUS_ONE;
		assertEquals("-1", x.toString());
		x = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(-1));
		assertEquals(STR_1Z, x.toString());
		x = CongruenceDomainValue.createNonConstant(BigInteger.TEN, true);
		assertEquals("10Z \\ {0}", x.toString());
		x = CongruenceDomainValue.createNonConstant(BigInteger.ZERO, true);
		assertEquals(STR_BOT, x.toString());
		x = CongruenceDomainValue.createNonConstant(BigInteger.ZERO, false);
		assertEquals(STR_ZERO, x.toString());
	}

	@Test
	public void testMerge() {
		final CongruenceDomainValue b = BOT;
		final CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(4), true);
		final CongruenceDomainValue z2 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(2));
		final CongruenceDomainValue z3 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(3));
		final CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(BigInteger.valueOf(-6));
		final CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(BigInteger.valueOf(7));
		final CongruenceDomainValue c3 = ZERO;
		assertEquals(STR_BOT, b.merge(b).toString());
		assertEquals(STR_4Z_NO_ZERO, b.merge(z4).toString());
		assertEquals(STR_4Z_NO_ZERO, z4.merge(b).toString());
		assertEquals("-6", c1.merge(c1).toString());
		assertEquals(STR_1Z_NO_ZERO, c1.merge(c2).toString());
		assertEquals(STR_2Z, z4.merge(z2).toString());
		assertEquals(STR_1Z, z4.merge(z3).toString());
		assertEquals(STR_4Z, z4.merge(c3).toString());
	}

	@Test
	public void testIntersect() {
		final CongruenceDomainValue b = BOT;
		final CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(4), true);
		final CongruenceDomainValue z2 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(2));
		final CongruenceDomainValue z6 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(6));
		final CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(BigInteger.valueOf(-6));
		final CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(BigInteger.valueOf(7));
		final CongruenceDomainValue c3 = ZERO;
		final CongruenceDomainValue c4 = CongruenceDomainValue.createConstant(BigInteger.valueOf(8));
		assertEquals(b.intersect(z4).toString(), STR_BOT);
		assertEquals(c1.intersect(c1).toString(), "-6");
		assertEquals(c1.intersect(c2).toString(), STR_BOT);
		assertEquals(z6.intersect(z4).toString(), "12Z \\ {0}");
		assertEquals(z2.intersect(z4).toString(), STR_4Z_NO_ZERO);
		assertEquals(z2.intersect(c3).toString(), STR_ZERO);
		assertEquals(c4.intersect(z4).toString(), "8");
		assertEquals(z4.intersect(c4).toString(), "8");
		assertEquals(z4.intersect(c2).toString(), STR_BOT);
		assertEquals(c2.intersect(z4).toString(), STR_BOT);
		assertEquals(z4.intersect(c3).toString(), STR_BOT);
	}

	@Test
	public void testAddSub() {
		final CongruenceDomainValue b = BOT;
		final CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(4), true);
		final CongruenceDomainValue z2 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(2));
		final CongruenceDomainValue z3 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(3));
		final CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(BigInteger.valueOf(-6));
		final CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(BigInteger.valueOf(7));
		final CongruenceDomainValue c3 = ZERO;
		final CongruenceDomainValue c4 = CongruenceDomainValue.createConstant(BigInteger.valueOf(4));
		assertEquals(STR_4Z_NO_ZERO, c3.add(z4).toString());
		assertEquals(STR_2Z, c3.add(z2).toString());
		assertEquals(STR_BOT, b.add(z4).toString());
		assertEquals("1", c1.add(c2).toString());
		assertEquals(STR_1Z, z4.add(z3).toString());
		assertEquals("-13", c1.subtract(c2).toString());
		assertEquals(STR_2Z, z4.subtract(z2).toString());
		assertEquals(STR_4Z, c4.add(z4).toString());
		assertEquals(STR_1Z_NO_ZERO, c2.subtract(z4).toString());
	}

	@Test
	public void testMod() {
		final CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(BigInteger.valueOf(-2));
		final CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(BigInteger.valueOf(-3));
		final CongruenceDomainValue c3 = CongruenceDomainValue.createConstant(BigInteger.valueOf(3));
		final CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(4), true);
		final CongruenceDomainValue z5 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(5));
		final CongruenceDomainValue z2 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(2), true);
		assertEquals("1", c1.mod(c2).toString());
		assertEquals("3", c3.mod(z4).toString());
		assertEquals(STR_ZERO, z4.mod(c1).toString());
		assertEquals(STR_1Z, c3.mod(z5).toString());
		assertEquals(STR_1Z_NO_ZERO, c3.mod(z2).toString());
		assertEquals(STR_2Z, c1.mod(z2).toString());
		assertEquals(STR_1Z, z2.mod(c3).toString());

	}

	@Test
	public void testMult() {
		final CongruenceDomainValue b = BOT;
		final CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(4), true);
		final CongruenceDomainValue z2 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(2));
		final CongruenceDomainValue z3 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(3));
		final CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(BigInteger.valueOf(-6));
		final CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(BigInteger.valueOf(7));
		final CongruenceDomainValue c3 = ZERO;
		assertEquals(STR_BOT, b.multiply(z4).toString());
		assertEquals("-42", c1.multiply(c2).toString());
		assertEquals("18Z", c1.multiply(z3).toString());
		assertEquals("8Z", z4.multiply(z2).toString());
		assertEquals("16Z \\ {0}", z4.multiply(z4).toString());
		assertEquals(STR_ZERO, c3.multiply(z4).toString());
	}

	@Test
	public void testDiv() {
		final CongruenceDomainValue b = BOT;
		final CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(4), true);
		final CongruenceDomainValue z3 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(3));
		final CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(BigInteger.valueOf(-2));
		final CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(BigInteger.valueOf(7));
		final CongruenceDomainValue c3 = CongruenceDomainValue.createConstant(BigInteger.valueOf(3));
		final CongruenceDomainValue c4 = CongruenceDomainValue.createConstant(BigInteger.valueOf(-5));
		final CongruenceDomainValue c5 = CongruenceDomainValue.createConstant(BigInteger.valueOf(-100));
		final CongruenceDomainValue c6 = CongruenceDomainValue.createConstant(BigInteger.valueOf(-7));
		final CongruenceDomainValue c7 = ZERO;
		assertEquals(b.divideReal(z4).toString(), STR_BOT);
		assertEquals(z4.divideReal(c1).toString(), STR_2Z_NO_ZERO);
		assertEquals(z3.divideReal(c1).toString(), STR_1Z);
		assertEquals(c2.divideReal(c1).toString(), "-3");
		assertEquals(c1.divideReal(c2).toString(), "-1");
		assertEquals(c2.negate().divideReal(c1.negate()).toString(), "-4");
		assertEquals(c1.divideReal(c2.negate()).toString(), "1");
		assertEquals(c3.divideReal(z4).toString(), STR_ZERO);
		assertEquals(c4.divideReal(z3).toString(), STR_1Z);
		assertEquals(c5.divideReal(c6).toString(), "15");
		assertEquals(z3.divideReal(c7).toString(), STR_1Z);
		assertEquals(z4.divideReal(c3).toString(), STR_1Z_NO_ZERO);
		assertEquals(z3.divideReal(c1).toString(), STR_1Z);
	}

	@Test
	public void testNeg() {
		final CongruenceDomainValue b = BOT;
		final CongruenceDomainValue c = CongruenceDomainValue.createConstant(BigInteger.valueOf(-3));
		final CongruenceDomainValue z = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(3), true);
		assertEquals(b.negate().toString(), STR_BOT);
		assertEquals(c.negate().toString(), "3");
		assertEquals(z.negate().toString(), "3Z \\ {0}");
	}

	@Test
	public void testModEquals() {
		final CongruenceDomainValue zero = ZERO;
		final CongruenceDomainValue one = CongruenceDomainValue.createConstant(BigInteger.ONE);
		final CongruenceDomainValue two = CongruenceDomainValue.createConstant(BigInteger.valueOf(2));
		final CongruenceDomainValue minusTwo = CongruenceDomainValue.createConstant(BigInteger.valueOf(-2));
		final CongruenceDomainValue z3 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(3));
		final CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(4), true);
		assertEquals(z3.modEquals(zero).toString(), STR_1Z);
		assertEquals(z4.modEquals(two).toString(), STR_2Z_NO_ZERO);
		assertEquals(two.modEquals(zero).toString(), STR_2Z);
		assertEquals(minusTwo.modEquals(zero).toString(), STR_2Z);
		assertEquals(z4.modEquals(minusTwo).toString(), STR_BOT);
		assertEquals(one.modEquals(two).toString(), STR_BOT);
		assertEquals(minusTwo.modEquals(z3).toString(), STR_2Z);
		assertEquals(two.modEquals(z4).toString(), STR_BOT);
	}

	@Test
	public void testIsContainedIn() {
		final CongruenceDomainValue b = BOT;
		final CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(BigInteger.valueOf(3));
		final CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(BigInteger.valueOf(4));
		final CongruenceDomainValue c3 = ZERO;
		final CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(4));
		final CongruenceDomainValue z2 = CongruenceDomainValue.createNonConstant(BigInteger.valueOf(2), true);
		assertTrue(b.isContainedIn(b));
		assertTrue(c1.isContainedIn(c1));
		assertFalse(c2.isContainedIn(c1));
		assertFalse(z4.isContainedIn(c2));
		assertFalse(c1.isContainedIn(z4));
		assertTrue(c2.isContainedIn(z4));
		assertFalse(z4.isContainedIn(z2));
		assertFalse(c3.isContainedIn(z2));
		assertTrue(c3.isContainedIn(z4));
	}
}
