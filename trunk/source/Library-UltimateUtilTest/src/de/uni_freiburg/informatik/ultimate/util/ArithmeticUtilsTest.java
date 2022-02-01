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
 *
 */
public class ArithmeticUtilsTest {

	/**
	 * Tests for the case where the divisior is not divisible by the divident.
	 */
	@Test
	public void euclideanDivAndMod1() {
		Assert.assertTrue(ArithmeticUtils.euclideanDiv(bi(16), bi(10)).equals(bi(1)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(bi(16), bi(10)).equals(bi(6)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(bi(16), bi(-10)).equals(bi(-1)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(bi(16), bi(-10)).equals(bi(6)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(bi(-16), bi(10)).equals(bi(-2)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(bi(-16), bi(10)).equals(bi(4)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(bi(-16), bi(-10)).equals(bi(2)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(bi(-16), bi(-10)).equals(bi(4)));
	}

	/**
	 * Tests for the special case where the divisior is not divisible by the
	 * divident and the result of the Java division is 0.
	 */
	@Test
	public void euclideanDivAndMod2() {
		Assert.assertTrue(ArithmeticUtils.euclideanDiv(bi(1), bi(256)).equals(bi(0)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(bi(1), bi(256)).equals(bi(1)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(bi(1), bi(-256)).equals(bi(0)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(bi(1), bi(-256)).equals(bi(1)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(bi(-1), bi(256)).equals(bi(-1)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(bi(-1), bi(256)).equals(bi(255)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(bi(-1), bi(-256)).equals(bi(1)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(bi(-1), bi(-256)).equals(bi(255)));
	}

	/**
	 * Tests for the case where the divisior is divisible by the divident.
	 */
	@Test
	public void euclideanDivAndMod3() {
		Assert.assertTrue(ArithmeticUtils.euclideanDiv(bi(20), bi(10)).equals(bi(2)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(bi(20), bi(10)).equals(bi(0)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(bi(20), bi(-10)).equals(bi(-2)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(bi(20), bi(-10)).equals(bi(0)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(bi(-20), bi(10)).equals(bi(-2)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(bi(-20), bi(10)).equals(bi(0)));

		Assert.assertTrue(ArithmeticUtils.euclideanDiv(bi(-20), bi(-10)).equals(bi(2)));
		Assert.assertTrue(ArithmeticUtils.euclideanMod(bi(-20), bi(-10)).equals(bi(0)));
	}

	private static BigInteger bi(final int i) {
		return BigInteger.valueOf(i);
	}

}
