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
	public void testConstructSet() {
		CongruenceDomainValue x = new CongruenceDomainValue();
		assertTrue(x.toString().equals("1Z"));
		x = new CongruenceDomainValue(true);
		assertTrue(x.toString().equals("{}"));
		x = new CongruenceDomainValue(new BigInteger("5"), true);
		assertTrue(x.toString().equals("5"));
		x = new CongruenceDomainValue(new BigInteger("-1"), true);
		assertTrue(x.toString().equals("-1"));
		x = new CongruenceDomainValue(new BigInteger("-1"));
		assertTrue(x.toString().equals("1Z"));
		x.setToBottom();
		assertTrue(x.toString().equals("{}"));
		x.setValue(new BigInteger("-2"));
		assertTrue(x.toString().equals("2Z"));
	}
	
	@Test
	public void testMerge() {
		CongruenceDomainValue b = new CongruenceDomainValue(true);
		CongruenceDomainValue z4 = new CongruenceDomainValue(new BigInteger("4"));
		CongruenceDomainValue z2 = new CongruenceDomainValue(new BigInteger("2"));
		CongruenceDomainValue z3 = new CongruenceDomainValue(new BigInteger("3"));
		CongruenceDomainValue c1 = new CongruenceDomainValue(new BigInteger("-6"), true);
		CongruenceDomainValue c2 = new CongruenceDomainValue(new BigInteger("7"), true);
		assertTrue(b.merge(b).toString().equals("{}"));
		assertTrue(b.merge(z4).toString().equals("4Z"));
		assertTrue(z4.merge(b).toString().equals("4Z"));
		assertTrue(c1.merge(c1).toString().equals("-6"));
		assertTrue(c1.merge(c2).toString().equals("1Z"));
		assertTrue(z4.merge(z2).toString().equals("2Z"));
		assertTrue(z4.merge(z3).toString().equals("1Z"));
	}
	
	@Test
	public void testIntersect() {
		CongruenceDomainValue b = new CongruenceDomainValue(true);
		CongruenceDomainValue z4 = new CongruenceDomainValue(new BigInteger("4"));
		CongruenceDomainValue z2 = new CongruenceDomainValue(new BigInteger("2"));
		CongruenceDomainValue z6 = new CongruenceDomainValue(new BigInteger("6"));
		CongruenceDomainValue c1 = new CongruenceDomainValue(new BigInteger("-6"), true);
		CongruenceDomainValue c2 = new CongruenceDomainValue(new BigInteger("7"), true);
		CongruenceDomainValue c3 = new CongruenceDomainValue(new BigInteger("0"), true);
		CongruenceDomainValue c4 = new CongruenceDomainValue(new BigInteger("8"), true);
		assertTrue(b.intersect(z4).toString().equals("{}"));
		assertTrue(c1.intersect(c1).toString().equals("-6"));
		assertTrue(c1.intersect(c2).toString().equals("{}"));
		assertTrue(z6.intersect(z4).toString().equals("12Z"));
		assertTrue(z2.intersect(z4).toString().equals("4Z"));
		assertTrue(z2.intersect(c3).toString().equals("0"));
		assertTrue(c4.intersect(z4).toString().equals("8"));
		assertTrue(z4.intersect(c4).toString().equals("8"));
		assertTrue(z4.intersect(c2).toString().equals("{}"));
		assertTrue(c2.intersect(z4).toString().equals("{}"));
	}
	
	@Test
	public void testAddSub() {
		CongruenceDomainValue b = new CongruenceDomainValue(true);
		CongruenceDomainValue z4 = new CongruenceDomainValue(new BigInteger("4"));
		CongruenceDomainValue z2 = new CongruenceDomainValue(new BigInteger("2"));
		CongruenceDomainValue z3 = new CongruenceDomainValue(new BigInteger("3"));
		CongruenceDomainValue c1 = new CongruenceDomainValue(new BigInteger("-6"), true);
		CongruenceDomainValue c2 = new CongruenceDomainValue(new BigInteger("7"), true);
		CongruenceDomainValue c3 = new CongruenceDomainValue(new BigInteger("0"), true);
		assertTrue(c3.add(z4).toString().equals("4Z"));
		assertTrue(b.add(z4).toString().equals("{}"));
		assertTrue(c1.add(c2).toString().equals("1"));
		assertTrue(z4.add(z3).toString().equals("1Z"));
		assertTrue(c1.subtract(c2).toString().equals("-13"));
		assertTrue(z4.subtract(z2).toString().equals("2Z"));
	}
	
	@Test
	public void testMod() {
		CongruenceDomainValue c1 = new CongruenceDomainValue(new BigInteger("-2"), true);
		CongruenceDomainValue c2 = new CongruenceDomainValue(new BigInteger("-3"), true);
		CongruenceDomainValue c3 = new CongruenceDomainValue(new BigInteger("3"), true);
		CongruenceDomainValue z4 = new CongruenceDomainValue(new BigInteger("4"));
		assertTrue(c1.mod(c2).toString().equals("1"));
		assertTrue(c3.mod(z4).toString().equals("3"));
		assertTrue(z4.mod(c1).toString().equals("0"));
	}
	
	@Test
	public void testMult() {
		CongruenceDomainValue b = new CongruenceDomainValue(true);
		CongruenceDomainValue z4 = new CongruenceDomainValue(new BigInteger("4"));
		CongruenceDomainValue z2 = new CongruenceDomainValue(new BigInteger("2"));
		CongruenceDomainValue z3 = new CongruenceDomainValue(new BigInteger("3"));
		CongruenceDomainValue c1 = new CongruenceDomainValue(new BigInteger("-6"), true);
		CongruenceDomainValue c2 = new CongruenceDomainValue(new BigInteger("7"), true);
		assertTrue(b.multiply(z4).toString().equals("{}"));
		assertTrue(c1.multiply(c2).toString().equals("-42"));
		assertTrue(c1.multiply(z3).toString().equals("18Z"));
		assertTrue(z4.multiply(z2).toString().equals("8Z"));
	}
	
	@Test
	public void testDiv() {
		CongruenceDomainValue b = new CongruenceDomainValue(true);
		CongruenceDomainValue z4 = new CongruenceDomainValue(new BigInteger("4"));
		CongruenceDomainValue z3 = new CongruenceDomainValue(new BigInteger("3"));
		CongruenceDomainValue c1 = new CongruenceDomainValue(new BigInteger("-2"), true);
		CongruenceDomainValue c2 = new CongruenceDomainValue(new BigInteger("7"), true);
		CongruenceDomainValue c3 = new CongruenceDomainValue(new BigInteger("3"), true);
		CongruenceDomainValue c4 = new CongruenceDomainValue(new BigInteger("-5"), true);
		CongruenceDomainValue c5 = new CongruenceDomainValue(new BigInteger("-100"), true);
		CongruenceDomainValue c6 = new CongruenceDomainValue(new BigInteger("-7"), true);
		assertTrue(b.divide(z4).toString().equals("{}"));
		assertTrue(z4.divide(c1).toString().equals("2Z"));
		assertTrue(z3.divide(c1).toString().equals("1Z"));
		assertTrue(c2.divide(c1).toString().equals("-3"));
		assertTrue(c1.divide(c2).toString().equals("-1"));
		assertTrue(c2.negate().divide(c1.negate()).toString().equals("-4"));
		assertTrue(c1.divide(c2.negate()).toString().equals("1"));
		assertTrue(c3.divide(z4).toString().equals("0"));
		assertTrue(c4.divide(z4).toString().equals("1Z"));
		assertTrue(c5.divide(c6).toString().equals("15"));
	}
	
	@Test
	public void testNeg() {
		CongruenceDomainValue b = new CongruenceDomainValue(true);
		CongruenceDomainValue c = new CongruenceDomainValue(new BigInteger("-3"), true);
		CongruenceDomainValue z = new CongruenceDomainValue(new BigInteger("3"));
		assertTrue(b.negate().toString().equals("{}"));
		assertTrue(c.negate().toString().equals("3"));
		assertTrue(z.negate().toString().equals("3Z"));
	}
	
	@Test
	public void testModEquals() {
		CongruenceDomainValue zero = new CongruenceDomainValue(BigInteger.ZERO, true);
		CongruenceDomainValue two = new CongruenceDomainValue(new BigInteger("2"), true);
		CongruenceDomainValue minusTwo = new CongruenceDomainValue(new BigInteger("-2"), true);
		CongruenceDomainValue z2 = new CongruenceDomainValue(new BigInteger("2"));
		CongruenceDomainValue z3 = new CongruenceDomainValue(new BigInteger("3"));
		CongruenceDomainValue z4 = new CongruenceDomainValue(new BigInteger("4"));
		assertTrue(z2.modEquals(z3, zero).toString().equals("6Z"));
		assertTrue(z3.modEquals(z4, two).toString().equals("6Z"));
		assertTrue(z3.modEquals(two, zero).toString().equals("6Z"));
		assertTrue(z3.modEquals(minusTwo, zero).toString().equals("6Z"));
	}
}