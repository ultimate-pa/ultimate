package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import static org.junit.Assert.*;
import org.junit.Test;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence.CongruenceDomainValue;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */

public class CongruenceDomainValueTest{
	@Test
	public void testCreate() {
		CongruenceDomainValue x = CongruenceDomainValue.createTop();
		assertTrue(x.toString().equals("1Z"));
		x = CongruenceDomainValue.createBottom();
		assertTrue(x.toString().equals("{}"));
		x = CongruenceDomainValue.createConstant(new BigInteger("5"));
		assertTrue(x.toString().equals("5"));
		x = CongruenceDomainValue.createConstant(new BigInteger("-1"));
		assertTrue(x.toString().equals("-1"));
		x = CongruenceDomainValue.createNonConstant(new BigInteger("-1"));
		assertTrue(x.toString().equals("1Z"));
		x = CongruenceDomainValue.createNonConstant(BigInteger.TEN, true);
		assertTrue(x.toString().equals("10Z \\ {0}"));
		x = CongruenceDomainValue.createNonConstant(BigInteger.ZERO, true);
		assertTrue(x.toString().equals("{}"));
		x = CongruenceDomainValue.createNonConstant(BigInteger.ZERO, false);
		assertTrue(x.toString().equals("0"));
	}
	
	@Test
	public void testMerge() {
		CongruenceDomainValue b = CongruenceDomainValue.createBottom();
		CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(new BigInteger("4"), true);
		CongruenceDomainValue z2 = CongruenceDomainValue.createNonConstant(new BigInteger("2"));
		CongruenceDomainValue z3 = CongruenceDomainValue.createNonConstant(new BigInteger("3"));
		CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(new BigInteger("-6"));
		CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(new BigInteger("7"));
		CongruenceDomainValue c3 = CongruenceDomainValue.createConstant(BigInteger.ZERO);
		assertTrue(b.merge(b).toString().equals("{}"));
		assertTrue(b.merge(z4).toString().equals("4Z \\ {0}"));
		assertTrue(z4.merge(b).toString().equals("4Z \\ {0}"));
		assertTrue(c1.merge(c1).toString().equals("-6"));
		assertTrue(c1.merge(c2).toString().equals("1Z \\ {0}"));
		assertTrue(z4.merge(z2).toString().equals("2Z"));
		assertTrue(z4.merge(z3).toString().equals("1Z"));
		assertTrue(z4.merge(c3).toString().equals("4Z"));
	}
	
	@Test
	public void testIntersect() {
		CongruenceDomainValue b = CongruenceDomainValue.createBottom();
		CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(new BigInteger("4"), true);
		CongruenceDomainValue z2 = CongruenceDomainValue.createNonConstant(new BigInteger("2"));
		CongruenceDomainValue z6 = CongruenceDomainValue.createNonConstant(new BigInteger("6"));
		CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(new BigInteger("-6"));
		CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(new BigInteger("7"));
		CongruenceDomainValue c3 = CongruenceDomainValue.createConstant(BigInteger.ZERO);
		CongruenceDomainValue c4 = CongruenceDomainValue.createConstant(new BigInteger("8"));
		assertTrue(b.intersect(z4).toString().equals("{}"));
		assertTrue(c1.intersect(c1).toString().equals("-6"));
		assertTrue(c1.intersect(c2).toString().equals("{}"));
		assertTrue(z6.intersect(z4).toString().equals("12Z \\ {0}"));
		assertTrue(z2.intersect(z4).toString().equals("4Z \\ {0}"));
		assertTrue(z2.intersect(c3).toString().equals("0"));
		assertTrue(c4.intersect(z4).toString().equals("8"));
		assertTrue(z4.intersect(c4).toString().equals("8"));
		assertTrue(z4.intersect(c2).toString().equals("{}"));
		assertTrue(c2.intersect(z4).toString().equals("{}"));
		assertTrue(z4.intersect(c3).toString().equals("{}"));
	}
	
	@Test
	public void testAddSub() {
		CongruenceDomainValue b = CongruenceDomainValue.createBottom();
		CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(new BigInteger("4"), true);
		CongruenceDomainValue z2 = CongruenceDomainValue.createNonConstant(new BigInteger("2"));
		CongruenceDomainValue z3 = CongruenceDomainValue.createNonConstant(new BigInteger("3"));
		CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(new BigInteger("-6"));
		CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(new BigInteger("7"));
		CongruenceDomainValue c3 = CongruenceDomainValue.createConstant(BigInteger.ZERO);
		CongruenceDomainValue c4 = CongruenceDomainValue.createConstant(new BigInteger("4"));
		assertTrue(c3.add(z4).toString().equals("4Z \\ {0}"));
		assertTrue(c3.add(z2).toString().equals("2Z"));
		assertTrue(b.add(z4).toString().equals("{}"));
		assertTrue(c1.add(c2).toString().equals("1"));
		assertTrue(z4.add(z3).toString().equals("1Z"));
		assertTrue(c1.subtract(c2).toString().equals("-13"));
		assertTrue(z4.subtract(z2).toString().equals("2Z"));
		assertTrue(c4.add(z4).toString().equals("4Z"));
		assertTrue(c2.subtract(z4).toString().equals("1Z \\ {0}"));
	}
	
	@Test
	public void testMod() {
		CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(new BigInteger("-2"));
		CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(new BigInteger("-3"));
		CongruenceDomainValue c3 = CongruenceDomainValue.createConstant(new BigInteger("3"));
		CongruenceDomainValue c4 = CongruenceDomainValue.createConstant(new BigInteger("16"));
		CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(new BigInteger("4"), true);
		CongruenceDomainValue z5 = CongruenceDomainValue.createNonConstant(new BigInteger("5"));
		CongruenceDomainValue z2 = CongruenceDomainValue.createNonConstant(new BigInteger("2"), true);
		assertTrue(c1.mod(c2).toString().equals("1"));
		assertTrue(c3.mod(z4).toString().equals("3"));
		assertTrue(z4.mod(c1).toString().equals("0"));
		assertTrue(c3.mod(z5).toString().equals("1Z"));
		assertTrue(c3.mod(z2).toString().equals("1Z \\ {0}"));
		assertTrue(c1.mod(z2).toString().equals("2Z"));
		assertTrue(z2.mod(c3).toString().equals("1Z \\ {0}"));
		assertTrue(z4.mod(c4).toString().equals("4Z"));
		
	}
	
	@Test
	public void testMult() {
		CongruenceDomainValue b = CongruenceDomainValue.createBottom();
		CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(new BigInteger("4"), true);
		CongruenceDomainValue z2 = CongruenceDomainValue.createNonConstant(new BigInteger("2"));
		CongruenceDomainValue z3 = CongruenceDomainValue.createNonConstant(new BigInteger("3"));
		CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(new BigInteger("-6"));
		CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(new BigInteger("7"));
		CongruenceDomainValue c3 = CongruenceDomainValue.createConstant(BigInteger.ZERO);
		assertTrue(b.multiply(z4).toString().equals("{}"));
		assertTrue(c1.multiply(c2).toString().equals("-42"));
		assertTrue(c1.multiply(z3).toString().equals("18Z"));
		assertTrue(z4.multiply(z2).toString().equals("8Z"));
		assertTrue(z4.multiply(z4).toString().equals("16Z \\ {0}"));
		assertTrue(c3.multiply(z4).toString().equals("0"));
	}
	
	@Test
	public void testDiv() {
		CongruenceDomainValue b = CongruenceDomainValue.createBottom();
		CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(new BigInteger("4"), true);
		CongruenceDomainValue z3 = CongruenceDomainValue.createNonConstant(new BigInteger("3"));
		CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(new BigInteger("-2"));
		CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(new BigInteger("7"));
		CongruenceDomainValue c3 = CongruenceDomainValue.createConstant(new BigInteger("3"));
		CongruenceDomainValue c4 = CongruenceDomainValue.createConstant(new BigInteger("-5"));
		CongruenceDomainValue c5 = CongruenceDomainValue.createConstant(new BigInteger("-100"));
		CongruenceDomainValue c6 = CongruenceDomainValue.createConstant(new BigInteger("-7"));
		CongruenceDomainValue c7 = CongruenceDomainValue.createConstant(BigInteger.ZERO);
		assertTrue(b.divide(z4).toString().equals("{}"));
		assertTrue(z4.divide(c1).toString().equals("2Z \\ {0}"));
		assertTrue(z3.divide(c1).toString().equals("1Z"));
		assertTrue(c2.divide(c1).toString().equals("-3"));
		assertTrue(c1.divide(c2).toString().equals("-1"));
		assertTrue(c2.negate().divide(c1.negate()).toString().equals("-4"));
		assertTrue(c1.divide(c2.negate()).toString().equals("1"));
		assertTrue(c3.divide(z4).toString().equals("0"));
		assertTrue(c4.divide(z3).toString().equals("1Z"));
		assertTrue(c5.divide(c6).toString().equals("15"));
		assertTrue(z3.divide(c7).toString().equals("1Z"));
	}
	
	@Test
	public void testNeg() {
		CongruenceDomainValue b = CongruenceDomainValue.createBottom();
		CongruenceDomainValue c = CongruenceDomainValue.createConstant(new BigInteger("-3"));
		CongruenceDomainValue z = CongruenceDomainValue.createNonConstant(new BigInteger("3"), true);
		assertTrue(b.negate().toString().equals("{}"));
		assertTrue(c.negate().toString().equals("3"));
		assertTrue(z.negate().toString().equals("3Z \\ {0}"));
	}
	
	@Test
	public void testModEquals() {
		CongruenceDomainValue zero = CongruenceDomainValue.createConstant(BigInteger.ZERO);
		CongruenceDomainValue one = CongruenceDomainValue.createConstant(BigInteger.ONE);
		CongruenceDomainValue two = CongruenceDomainValue.createConstant(new BigInteger("2"));
		CongruenceDomainValue minusTwo = CongruenceDomainValue.createConstant(new BigInteger("-2"));
		CongruenceDomainValue z3 = CongruenceDomainValue.createNonConstant(new BigInteger("3"));
		CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(new BigInteger("4"), true);
		assertTrue(z3.modEquals(zero).toString().equals("1Z"));
		assertTrue(z4.modEquals(two).toString().equals("2Z \\ {0}"));
		assertTrue(two.modEquals(zero).toString().equals("2Z"));
		assertTrue(minusTwo.modEquals(zero).toString().equals("2Z"));
		assertTrue(z4.modEquals(minusTwo).toString().equals("{}"));
		assertTrue(one.modEquals(two).toString().equals("{}"));
		assertTrue(minusTwo.modEquals(z3).toString().equals("2Z"));
	}
	
	@Test
	public void testIsContainedIn() {
		CongruenceDomainValue b = CongruenceDomainValue.createBottom();
		CongruenceDomainValue c1 = CongruenceDomainValue.createConstant(new BigInteger("3"));
		CongruenceDomainValue c2 = CongruenceDomainValue.createConstant(new BigInteger("4"));
		CongruenceDomainValue c3 = CongruenceDomainValue.createConstant(BigInteger.ZERO);
		CongruenceDomainValue z4 = CongruenceDomainValue.createNonConstant(new BigInteger("4"));
		CongruenceDomainValue z2 = CongruenceDomainValue.createNonConstant(new BigInteger("2"), true);
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