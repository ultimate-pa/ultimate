package local.stalin.smt.theory.linar;

import java.math.BigInteger;

import junit.framework.TestCase;

/**
 * Test Class for Rationals.
 * 
 * @author Jochen Hoenicke
 */
public final class RationalTest extends TestCase {
	BigInteger large = new BigInteger("1234567890123456789012345678901234567890"); 
	Rational largeRat = Rational.valueOf(large, BigInteger.ONE);
	Rational smallRat = Rational.valueOf(BigInteger.ONE, large.divide(BigInteger.valueOf(7)));
	Rational rat = largeRat.mul(smallRat);
	Rational medium1 = Rational.valueOf(Integer.MAX_VALUE, 1);
	Rational medium2 = Rational.valueOf(1, Integer.MAX_VALUE);
	Rational medium3 = Rational.valueOf(0x789abcdf, 0x76543210);
	Rational special1 = Rational.valueOf(BigInteger.ONE, BigInteger.valueOf(Integer.MIN_VALUE));
	Rational special2 = Rational.valueOf(BigInteger.valueOf(Integer.MIN_VALUE), BigInteger.ONE);

	Rational[] rationals = {
		Rational.ONE, Rational.MONE, Rational.ZERO,
		Rational.NAN, Rational.POSITIVE_INFINITY,
		Rational.NEGATIVE_INFINITY,
		largeRat, smallRat, rat, medium1, medium2, medium3,
		special1, special2,
		largeRat.negate(), smallRat.negate(), rat.negate(), 
		medium1.negate(), medium2.negate(), medium3.negate(),
		special1.negate(), special2.negate()
	};

	public void testGCD() {
		assertEquals(0, Rational.gcd(0, 0));
		assertEquals(5, Rational.gcd(5, 0));
		assertEquals(5, Rational.gcd(0, 5));
		assertEquals(1, Rational.gcd(1, 5));
		assertEquals(1, Rational.gcd(5, 1));
		assertEquals(37, Rational.gcd(111, 37));
		assertEquals(10, Rational.gcd(150, 220));
		assertEquals(Integer.MAX_VALUE, Rational.gcd(Integer.MAX_VALUE,
				Integer.MAX_VALUE));
		assertEquals(1, Rational.gcd(Integer.MAX_VALUE, 720720));
		assertEquals(77, Rational.gcd(1309, 720720));
	}

	public void testGCDlong() {
		assertEquals(0, Rational.gcd(0l, 0l));
		assertEquals(5, Rational.gcd(5l, 0l));
		assertEquals(5, Rational.gcd(0l, 5l));
		assertEquals(1, Rational.gcd(1l, 5l));
		assertEquals(1, Rational.gcd(5l, 1l));
		assertEquals(37, Rational.gcd(111l, 37l));
		assertEquals(10, Rational.gcd(150l, 220l));
		assertEquals(Long.MAX_VALUE, Rational.gcd(Long.MAX_VALUE,
				Long.MAX_VALUE));
		assertEquals(7, Rational.gcd(Long.MAX_VALUE, 720720l));
		assertEquals(1, Rational.gcd(Long.MAX_VALUE, Long.MAX_VALUE >> 1));
		assertEquals(77, Rational.gcd(1309l, 720720l));
	}

	public void testValueOf() {
		assertSame(Rational.ZERO, Rational.valueOf(0, 5));
		assertSame(Rational.ONE, Rational.valueOf(5, 5));
		assertSame(Rational.MONE, Rational.valueOf(-5, 5));

		assertSame(Rational.ZERO, Rational.valueOf(0, Long.MAX_VALUE));
		assertSame(Rational.ONE, 
				Rational.valueOf(Long.MAX_VALUE, Long.MAX_VALUE));
		assertSame(Rational.MONE, 
				Rational.valueOf(-Long.MAX_VALUE, Long.MAX_VALUE));

		assertSame(Rational.POSITIVE_INFINITY, 
				Rational.valueOf(Long.MAX_VALUE, 0));
		assertSame(Rational.NEGATIVE_INFINITY, 
				Rational.valueOf(-Long.MAX_VALUE, 0));
		assertSame(Rational.NAN, Rational.valueOf(0, 0));

		assertEquals(Rational.valueOf(2, 1), Rational.valueOf(0x7fffffe, 0x3ffffffl));
		assertTrue(Rational.valueOf(1, -Long.MAX_VALUE).isNegative());
		assertTrue(!Rational.valueOf(1, Long.MAX_VALUE).isNegative());

		BigInteger large = new BigInteger(
				"1234567890123456789012345678901234567890");
		assertSame(Rational.ZERO, Rational.valueOf(BigInteger.ZERO,	BigInteger.ONE));
		assertSame(Rational.ZERO, Rational.valueOf(BigInteger.ZERO, large));
		assertSame(Rational.ONE, Rational.valueOf(large, large));
		assertSame(Rational.ONE, Rational.valueOf(large.negate(), large.negate()));
		assertSame(Rational.MONE, Rational.valueOf(large, large.negate()));
		assertSame(Rational.MONE, Rational.valueOf(large.negate(), large));
		assertSame(Rational.POSITIVE_INFINITY, Rational.valueOf(large, BigInteger.ZERO));
		assertSame(Rational.NEGATIVE_INFINITY, Rational.valueOf(large.negate(), BigInteger.ZERO));
		assertSame(Rational.NAN, Rational.valueOf(BigInteger.ZERO, BigInteger.ZERO));
	}

	public void testAdd() {
		for (int i = 0; i < rationals.length; i++) {
			for (int j = i + 1; j< rationals.length; j++) {
				assertFalse(rationals[i].equals(rationals[j]));
			}
		}
		for (int i = 0; i < rationals.length; i++) {
			assertSame("NAN + "+rationals[i], Rational.NAN, Rational.NAN.add(rationals[i]));
			assertSame(rationals[i]+ " + NAN", Rational.NAN, rationals[i].add(Rational.NAN));
			if (rationals[i] != Rational.NAN) {
				Rational expect = rationals[i] == Rational.NEGATIVE_INFINITY ?
							Rational.NAN : Rational.POSITIVE_INFINITY;
				assertSame(expect, rationals[i].add(Rational.POSITIVE_INFINITY));
				assertSame(expect, Rational.POSITIVE_INFINITY.add(rationals[i]));
				expect = rationals[i] == Rational.POSITIVE_INFINITY ?
							Rational.NAN : Rational.NEGATIVE_INFINITY;
				assertSame(expect, rationals[i].add(Rational.NEGATIVE_INFINITY));
				assertSame(expect, Rational.NEGATIVE_INFINITY.add(rationals[i]));
			}
		}
		
		for (int i = 0; i < rationals.length; i++) {
			for (int j = i+1; j < rationals.length; j++) {
				assertEquals(rationals[i].add(rationals[j]),
						rationals[j].add(rationals[i]));
			}
		}
	}
	
	public void testMul() {
		assertEquals(Rational.ZERO, Rational.POSITIVE_INFINITY.inverse());
		assertEquals(Rational.ZERO, Rational.NEGATIVE_INFINITY.inverse());
		assertEquals(Rational.POSITIVE_INFINITY, Rational.ZERO.inverse());
		assertEquals(Rational.NAN, Rational.ZERO.mul(Rational.POSITIVE_INFINITY));
		assertEquals(Rational.NAN, Rational.ZERO.mul(Rational.NEGATIVE_INFINITY));
		
		for (int i = 0; i < rationals.length; i++) {
			if (rationals[i] != Rational.ZERO
				&& !rationals[i].denominator().equals(BigInteger.ZERO))
				assertEquals(Rational.ONE, rationals[i].mul(rationals[i].inverse()));
			for (int j = i+1; j < rationals.length; j++) {
				assertEquals(rationals[i].mul(rationals[j]),
						rationals[j].mul(rationals[i]));
				assertEquals(rationals[i].mul(rationals[j]).signum(),
						rationals[i].signum()*rationals[j].signum());
			}
		}
	}
	public void testDiverse() {
		for (int i = 0; i < rationals.length; i++) {
			assertEquals(0, rationals[i].compareTo(rationals[i]));
			for (int j = i+1; j < rationals.length; j++) {
				if (rationals[i] != Rational.NAN
					&& rationals[j] != Rational.NAN)
					assertTrue(rationals[i]+ " =<>= "+rationals[j],
							rationals[i].compareTo(rationals[j]) != 0);
				assertEquals(rationals[i]+ " <=> "+rationals[j],
						rationals[i].compareTo(rationals[j]),
						-rationals[j].compareTo(rationals[i]));
			}
		}
		for (int i = 0; i < rationals.length; i++) {
			assertEquals(rationals[i].isNegative(),
				     rationals[i].compareTo(Rational.ZERO) < 0);
			assertEquals(rationals[i].signum(),
				     rationals[i].compareTo(Rational.ZERO));
			if (rationals[i] != Rational.NEGATIVE_INFINITY)
				assertEquals(rationals[i], rationals[i].inverse().inverse());
			assertEquals(rationals[i], rationals[i].negate().negate());
			assertEquals(rationals[i], rationals[i].floor().add(rationals[i].frac()));
			assertEquals(rationals[i], rationals[i].frac().add(rationals[i].floor()));
			assertFalse(rationals[i].frac().isNegative());
			assertTrue(rationals[i].frac().compareTo(Rational.ONE) < 0);
			assertEquals(rationals[i].isIntegral(), rationals[i].frac() == Rational.ZERO);
		}
	}
}
