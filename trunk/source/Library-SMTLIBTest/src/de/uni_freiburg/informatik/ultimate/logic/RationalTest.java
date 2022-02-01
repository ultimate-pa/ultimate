/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.logic;

import java.math.BigInteger;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

/**
 * Test Class for Rationals.
 *
 * @author Jochen Hoenicke
 */
@RunWith(JUnit4.class)
public final class RationalTest {

	final static BigInteger LARGE = new BigInteger("1234567890123456789012345678901234567890");
	final static Rational LARGE_RAT = Rational.valueOf(LARGE, BigInteger.ONE);
	static final Rational SMALL_RAT = Rational.valueOf(BigInteger.ONE, LARGE.divide(BigInteger.valueOf(7)));// NOCHECKSTYLE
	static final Rational RAT = LARGE_RAT.mul(SMALL_RAT);
	static final Rational MEDIUM1 = Rational.valueOf(Integer.MAX_VALUE, 1);
	static final Rational MEDIUM2 = Rational.valueOf(1, Integer.MAX_VALUE);
	static Rational MEDIUM3 = Rational.valueOf(0x789abcdf, 0x76543210);// NOCHECKSTYLE
	static final Rational SPECIAL1 = Rational.valueOf(BigInteger.ONE, BigInteger.valueOf(Integer.MIN_VALUE));
	static final Rational SPECIAL2 = Rational.valueOf(BigInteger.valueOf(Integer.MIN_VALUE), BigInteger.ONE);

	static final Rational[] RATIONALS = { Rational.ONE, Rational.MONE, Rational.ZERO, Rational.NAN,
			Rational.POSITIVE_INFINITY, Rational.NEGATIVE_INFINITY, LARGE_RAT, SMALL_RAT, RAT, MEDIUM1, MEDIUM2,
			MEDIUM3, SPECIAL1, SPECIAL2, LARGE_RAT.negate(), SMALL_RAT.negate(), RAT.negate(), MEDIUM1.negate(),
			MEDIUM2.negate(), MEDIUM3.negate(), SPECIAL1.negate(), SPECIAL2.negate() };

	@Test
	public void testGCD() {
		Assert.assertEquals(0, Rational.gcd(0, 0));
		Assert.assertEquals(5, Rational.gcd(5, 0));// NOCHECKSTYLE
		Assert.assertEquals(5, Rational.gcd(0, 5));// NOCHECKSTYLE
		Assert.assertEquals(1, Rational.gcd(1, 5));// NOCHECKSTYLE
		Assert.assertEquals(1, Rational.gcd(5, 1));// NOCHECKSTYLE
		Assert.assertEquals(37, Rational.gcd(111, 37));// NOCHECKSTYLE
		Assert.assertEquals(10, Rational.gcd(150, 220));// NOCHECKSTYLE
		Assert.assertEquals(Integer.MAX_VALUE, Rational.gcd(Integer.MAX_VALUE, Integer.MAX_VALUE));
		Assert.assertEquals(1, Rational.gcd(Integer.MAX_VALUE, 720720));// NOCHECKSTYLE
		Assert.assertEquals(77, Rational.gcd(1309, 720720));// NOCHECKSTYLE
	}

	@Test
	public void testGCDlong() {
		Assert.assertEquals(0, Rational.gcd(0L, 0L));
		Assert.assertEquals(5, Rational.gcd(5L, 0L));// NOCHECKSTYLE
		Assert.assertEquals(5, Rational.gcd(0L, 5L));// NOCHECKSTYLE
		Assert.assertEquals(1, Rational.gcd(1L, 5L));// NOCHECKSTYLE
		Assert.assertEquals(1, Rational.gcd(5L, 1L));// NOCHECKSTYLE
		Assert.assertEquals(37, Rational.gcd(111L, 37L));// NOCHECKSTYLE
		Assert.assertEquals(10, Rational.gcd(150L, 220L));// NOCHECKSTYLE
		Assert.assertEquals(Long.MAX_VALUE, Rational.gcd(Long.MAX_VALUE, Long.MAX_VALUE));
		Assert.assertEquals(7, Rational.gcd(Long.MAX_VALUE, 720720L));// NOCHECKSTYLE
		Assert.assertEquals(1, Rational.gcd(Long.MAX_VALUE, Long.MAX_VALUE >> 1));
		Assert.assertEquals(77, Rational.gcd(1309l, 720720L));// NOCHECKSTYLE
	}

	@Test
	public void testValueOf() {
		Assert.assertSame(Rational.ZERO, Rational.valueOf(0, 5));// NOCHECKSTYLE
		Assert.assertSame(Rational.ONE, Rational.valueOf(5, 5));// NOCHECKSTYLE
		Assert.assertSame(Rational.MONE, Rational.valueOf(-5, 5));// NOCHECKSTYLE

		Assert.assertSame(Rational.ZERO, Rational.valueOf(0, Long.MAX_VALUE));
		Assert.assertSame(Rational.ONE, Rational.valueOf(Long.MAX_VALUE, Long.MAX_VALUE));
		Assert.assertSame(Rational.MONE, Rational.valueOf(-Long.MAX_VALUE, Long.MAX_VALUE));

		Assert.assertSame(Rational.POSITIVE_INFINITY, Rational.valueOf(Long.MAX_VALUE, 0));
		Assert.assertSame(Rational.NEGATIVE_INFINITY, Rational.valueOf(-Long.MAX_VALUE, 0));
		Assert.assertSame(Rational.NAN, Rational.valueOf(0, 0));

		Assert.assertEquals(Rational.valueOf(2, 1), Rational.valueOf(0x7fffffe, 0x3ffffffl));// NOCHECKSTYLE
		Assert.assertTrue(Rational.valueOf(1, -Long.MAX_VALUE).isNegative());
		Assert.assertTrue(!Rational.valueOf(1, Long.MAX_VALUE).isNegative());

		final BigInteger large = new BigInteger("1234567890123456789012345678901234567890");
		Assert.assertSame(Rational.ZERO, Rational.valueOf(BigInteger.ZERO, BigInteger.ONE));
		Assert.assertSame(Rational.ZERO, Rational.valueOf(BigInteger.ZERO, large));
		Assert.assertSame(Rational.ONE, Rational.valueOf(large, large));
		Assert.assertSame(Rational.ONE, Rational.valueOf(large.negate(), large.negate()));
		Assert.assertSame(Rational.MONE, Rational.valueOf(large, large.negate()));
		Assert.assertSame(Rational.MONE, Rational.valueOf(large.negate(), large));
		Assert.assertSame(Rational.POSITIVE_INFINITY, Rational.valueOf(large, BigInteger.ZERO));
		Assert.assertSame(Rational.NEGATIVE_INFINITY, Rational.valueOf(large.negate(), BigInteger.ZERO));
		Assert.assertSame(Rational.NAN, Rational.valueOf(BigInteger.ZERO, BigInteger.ZERO));
	}

	@Test
	public void testAdd() {
		for (int i = 0; i < RATIONALS.length; i++) {
			for (int j = i + 1; j < RATIONALS.length; j++) {
				Assert.assertFalse(RATIONALS[i].equals(RATIONALS[j]));
				Assert.assertFalse(RATIONALS[j].equals(RATIONALS[i]));
			}
		}
		for (int i = 0; i < RATIONALS.length; i++) {
			Assert.assertSame("NAN + " + RATIONALS[i], Rational.NAN, Rational.NAN.add(RATIONALS[i]));
			Assert.assertSame(RATIONALS[i] + " + NAN", Rational.NAN, RATIONALS[i].add(Rational.NAN));
			if (RATIONALS[i] != Rational.NAN) {
				Rational expect =
						RATIONALS[i] == Rational.NEGATIVE_INFINITY ? Rational.NAN : Rational.POSITIVE_INFINITY;
				Assert.assertSame(expect, RATIONALS[i].add(Rational.POSITIVE_INFINITY));
				Assert.assertSame(expect, Rational.POSITIVE_INFINITY.add(RATIONALS[i]));
				expect = RATIONALS[i] == Rational.POSITIVE_INFINITY ? Rational.NAN : Rational.NEGATIVE_INFINITY;
				Assert.assertSame(expect, RATIONALS[i].add(Rational.NEGATIVE_INFINITY));
				Assert.assertSame(expect, Rational.NEGATIVE_INFINITY.add(RATIONALS[i]));
			}
		}

		for (int i = 0; i < RATIONALS.length; i++) {
			for (int j = i + 1; j < RATIONALS.length; j++) {
				Assert.assertEquals(RATIONALS[i].add(RATIONALS[j]), RATIONALS[j].add(RATIONALS[i]));
			}
		}
	}

	@Test
	public void testMul() {
		Assert.assertEquals(Rational.ZERO, Rational.POSITIVE_INFINITY.inverse());
		Assert.assertEquals(Rational.ZERO, Rational.NEGATIVE_INFINITY.inverse());
		Assert.assertEquals(Rational.POSITIVE_INFINITY, Rational.ZERO.inverse());
		Assert.assertEquals(Rational.NAN, Rational.ZERO.mul(Rational.POSITIVE_INFINITY));
		Assert.assertEquals(Rational.NAN, Rational.ZERO.mul(Rational.NEGATIVE_INFINITY));

		for (int i = 0; i < RATIONALS.length; i++) {
			if (RATIONALS[i] != Rational.ZERO && !RATIONALS[i].denominator().equals(BigInteger.ZERO)) {
				Assert.assertEquals(Rational.ONE, RATIONALS[i].mul(RATIONALS[i].inverse()));
			}
			for (int j = i + 1; j < RATIONALS.length; j++) {
				Assert.assertEquals(RATIONALS[i].mul(RATIONALS[j]), RATIONALS[j].mul(RATIONALS[i]));
				Assert.assertEquals(RATIONALS[i].mul(RATIONALS[j]).signum(),
						RATIONALS[i].signum() * RATIONALS[j].signum());
			}
		}
	}

	@Test
	public void testDiverse() {
		for (int i = 0; i < RATIONALS.length; i++) {
			Assert.assertEquals(0, RATIONALS[i].compareTo(RATIONALS[i]));
			for (int j = i + 1; j < RATIONALS.length; j++) {
				if (RATIONALS[i] != Rational.NAN && RATIONALS[j] != Rational.NAN) {
					Assert.assertTrue(RATIONALS[i] + " =<>= " + RATIONALS[j],
							RATIONALS[i].compareTo(RATIONALS[j]) != 0);
				}
				Assert.assertEquals(RATIONALS[i] + " <=> " + RATIONALS[j], RATIONALS[i].compareTo(RATIONALS[j]),
						-RATIONALS[j].compareTo(RATIONALS[i]));
			}
		}
		for (int i = 0; i < RATIONALS.length; i++) {
			Assert.assertEquals(RATIONALS[i].isNegative(), RATIONALS[i].compareTo(Rational.ZERO) < 0);
			Assert.assertEquals(RATIONALS[i].signum(), RATIONALS[i].compareTo(Rational.ZERO));
			if (RATIONALS[i] != Rational.NEGATIVE_INFINITY) {
				Assert.assertEquals(RATIONALS[i], RATIONALS[i].inverse().inverse());
			}
			Assert.assertEquals(RATIONALS[i], RATIONALS[i].negate().negate());
			Assert.assertEquals(RATIONALS[i], RATIONALS[i].floor().add(RATIONALS[i].frac()));
			Assert.assertEquals(RATIONALS[i], RATIONALS[i].frac().add(RATIONALS[i].floor()));
			Assert.assertFalse(RATIONALS[i].frac().isNegative());
			Assert.assertTrue(RATIONALS[i].frac().compareTo(Rational.ONE) < 0);
			Assert.assertEquals(RATIONALS[i].isIntegral(), RATIONALS[i].frac() == Rational.ZERO);
		}
	}

	@Test
	public void testDiv() {
		Assert.assertSame(Rational.POSITIVE_INFINITY, SMALL_RAT.div(Rational.ZERO));
		Assert.assertSame(Rational.NEGATIVE_INFINITY, SMALL_RAT.negate().div(Rational.ZERO));
		Assert.assertSame(Rational.POSITIVE_INFINITY, LARGE_RAT.div(Rational.ZERO));
		Assert.assertSame(Rational.NEGATIVE_INFINITY, LARGE_RAT.negate().div(Rational.ZERO));
		Assert.assertSame(Rational.POSITIVE_INFINITY, Rational.POSITIVE_INFINITY.div(Rational.ZERO));
		Assert.assertSame(Rational.NEGATIVE_INFINITY, Rational.NEGATIVE_INFINITY.div(Rational.ZERO));
		Assert.assertSame(Rational.NAN, Rational.NAN.div(Rational.ZERO));
		Assert.assertSame(Rational.NAN, Rational.POSITIVE_INFINITY.div(Rational.POSITIVE_INFINITY));
		Assert.assertSame(Rational.NAN, Rational.POSITIVE_INFINITY.div(Rational.NEGATIVE_INFINITY));
		Assert.assertSame(Rational.NAN, Rational.NEGATIVE_INFINITY.div(Rational.POSITIVE_INFINITY));
		Assert.assertSame(Rational.NAN, Rational.NEGATIVE_INFINITY.div(Rational.NEGATIVE_INFINITY));
		Assert.assertSame(Rational.ZERO, Rational.ONE.div(Rational.POSITIVE_INFINITY));
		Assert.assertSame(Rational.ZERO, Rational.ONE.div(Rational.NEGATIVE_INFINITY));
		Assert.assertSame(Rational.ZERO, LARGE_RAT.div(Rational.POSITIVE_INFINITY));
		Assert.assertSame(Rational.ZERO, LARGE_RAT.div(Rational.NEGATIVE_INFINITY));
		Assert.assertSame(Rational.NAN, Rational.POSITIVE_INFINITY.add(Rational.NEGATIVE_INFINITY));
		Assert.assertSame(Rational.NAN, Rational.NEGATIVE_INFINITY.add(Rational.POSITIVE_INFINITY));
		Assert.assertSame(Rational.NAN, Rational.POSITIVE_INFINITY.sub(Rational.POSITIVE_INFINITY));
		Assert.assertSame(Rational.NAN, Rational.NEGATIVE_INFINITY.sub(Rational.NEGATIVE_INFINITY));
	}
}
