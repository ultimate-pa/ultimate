/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.math.BigInteger;

import org.junit.Assert;
import org.junit.Test;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Katharina Wagner
 *
 */
public class ArithmeticUtilsTest {

	/**
	 * Tests for the case where the divisior is not divisible by the divident.
	 */
	@Test
	public void euclideanDivAndMod1() {
		Assert.assertTrue(ArithmeticUtils.euclideanDiv(toBigInteger(16), toBigInteger(10)).equals(toBigInteger(1)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(toBigInteger(16), toBigInteger(10)).equals(toBigInteger(6)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(toBigInteger(16), toBigInteger(-10)).equals(toBigInteger(-1)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(toBigInteger(16), toBigInteger(-10)).equals(toBigInteger(6)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(toBigInteger(-16), toBigInteger(10)).equals(toBigInteger(-2)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(toBigInteger(-16), toBigInteger(10)).equals(toBigInteger(4)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(toBigInteger(-16), toBigInteger(-10)).equals(toBigInteger(2)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(toBigInteger(-16), toBigInteger(-10)).equals(toBigInteger(4)));
	}

	/**
	 * Tests for the special case where the divisior is not divisible by the
	 * divident and the result of the Java division is 0.
	 */
	@Test
	public void euclideanDivAndMod2() {
		Assert.assertTrue(ArithmeticUtils.euclideanDiv(toBigInteger(1), toBigInteger(256)).equals(toBigInteger(0)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(toBigInteger(1), toBigInteger(256)).equals(toBigInteger(1)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(toBigInteger(1), toBigInteger(-256)).equals(toBigInteger(0)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(toBigInteger(1), toBigInteger(-256)).equals(toBigInteger(1)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(toBigInteger(-1), toBigInteger(256)).equals(toBigInteger(-1)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(toBigInteger(-1), toBigInteger(256)).equals(toBigInteger(255)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(toBigInteger(-1), toBigInteger(-256)).equals(toBigInteger(1)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(toBigInteger(-1), toBigInteger(-256)).equals(toBigInteger(255)));
	}

	/**
	 * Tests for the case where the divisior is divisible by the divident.
	 */
	@Test
	public void euclideanDivAndMod3() {
		Assert.assertTrue(ArithmeticUtils.euclideanDiv(toBigInteger(20), toBigInteger(10)).equals(toBigInteger(2)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(toBigInteger(20), toBigInteger(10)).equals(toBigInteger(0)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(toBigInteger(20), toBigInteger(-10)).equals(toBigInteger(-2)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(toBigInteger(20), toBigInteger(-10)).equals(toBigInteger(0)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(toBigInteger(-20), toBigInteger(10)).equals(toBigInteger(-2)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(toBigInteger(-20), toBigInteger(10)).equals(toBigInteger(0)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(toBigInteger(-20), toBigInteger(-10)).equals(toBigInteger(2)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(toBigInteger(-20), toBigInteger(-10)).equals(toBigInteger(0)));
	}

	private static BigInteger toBigInteger(final int i) {
		return BigInteger.valueOf(i);
	}

	@Test
	public void multiplicativeInverse01() {
		final BigInteger res1 = ArithmeticUtils.multiplicativeInverse(BigInteger.valueOf(3), BigInteger.valueOf(256));
		Assert.assertTrue(res1.equals(BigInteger.valueOf(171)));
		final BigInteger res2 = ArithmeticUtils.multiplicativeInverse(BigInteger.valueOf(-3), BigInteger.valueOf(256));
		Assert.assertTrue(res2.equals(BigInteger.valueOf(85)));
		final BigInteger res3 = ArithmeticUtils.multiplicativeInverse(BigInteger.valueOf(5), BigInteger.valueOf(128));
		Assert.assertTrue(res3.equals(BigInteger.valueOf(77)));
		final BigInteger res4 = ArithmeticUtils.multiplicativeInverse(BigInteger.valueOf(17), BigInteger.valueOf(11));
		Assert.assertTrue(res4.equals(BigInteger.valueOf(2)));
		final BigInteger res5 = ArithmeticUtils.multiplicativeInverse(BigInteger.valueOf(1), BigInteger.valueOf(256));
		Assert.assertTrue(res5.equals(BigInteger.valueOf(1)));
	}

	@Test(expected = IllegalArgumentException.class)
	public void multiplicativeInverse02() {
		ArithmeticUtils.multiplicativeInverse(BigInteger.valueOf(7), BigInteger.valueOf(1));
	}

	@Test(expected = IllegalArgumentException.class)
	public void multiplicativeInverse03() {
		ArithmeticUtils.multiplicativeInverse(BigInteger.valueOf(2), BigInteger.valueOf(4));
	}


}
