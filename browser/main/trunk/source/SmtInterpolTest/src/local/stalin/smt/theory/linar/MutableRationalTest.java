package local.stalin.smt.theory.linar;

import junit.framework.TestCase;

/**
 * Test Class for Rationals.
 * 
 * @author Jochen Hoenicke
 */
public final class MutableRationalTest extends TestCase {
	Rational[] rationals = new RationalTest().rationals;

	public void testAdd() {
		for (int i = 0; i < rationals.length; i++) {
			for (int j = 0; j< rationals.length; j++) {
				MutableRational r1 = new MutableRational(rationals[i]);
				assertSame(r1, r1.add(rationals[j]));
				assertEquals(rationals[i] + " + " + rationals[j],
						rationals[i].add(rationals[j]), r1.toRational());
			}
		}
	}
	
	public void testMul() {
		for (int i = 0; i < rationals.length; i++) {
			for (int j = 0; j< rationals.length; j++) {
				MutableRational r1 = new MutableRational(rationals[i]);
				assertSame(r1, r1.mul(rationals[j]));
				assertEquals(rationals[i] + " * "+rationals[j],
						rationals[i].mul(rationals[j]), r1.toRational());
			}
		}
	}
	
	public void testDiverse() {
		for (int i = 0; i < rationals.length; i++) {
			MutableRational r1 = new MutableRational(rationals[i]);
			assertSame(r1, r1.inverse());
			assertEquals(rationals[i]+".inverse()",
					rationals[i].inverse(), r1.toRational());
			r1 = new MutableRational(rationals[i]);
			assertSame(r1, r1.negate());
			assertEquals(rationals[i]+".negate()",
					rationals[i].negate(), r1.toRational());
			r1 = new MutableRational(rationals[i]);
			assertEquals(rationals[i]+".isIntegral()",
					rationals[i].isIntegral(), r1.isIntegral());
			assertEquals(rationals[i]+".isNegative()",
					rationals[i].isNegative(), r1.isNegative());
			for (int j = 0; j < rationals.length; j++) {
				MutableRational r2 = new MutableRational(rationals[j]);
				assertEquals(rationals[i] + " <=> " + rationals[j],
						rationals[i].compareTo(rationals[j]), r1.compareTo(r2));
			}
		}
	}
}