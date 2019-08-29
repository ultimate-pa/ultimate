/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import java.math.BigInteger;
import java.util.function.BiFunction;

import org.junit.Assert;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.Interval;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.Interval.SatisfyingInputs;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class IntervalTest {

	// TODO test arithmetic operations like +, -, ... in detail

	@Test
	public void testUnification() {
		Assert.assertSame(Interval.TOP, interval("-inf, inf"));
		Assert.assertSame(Interval.BOTTOM, interval("-4, -5"));
		Assert.assertSame(Interval.BOTTOM, interval("456/7, 455/7"));
	}

	@Test
	public void testNegate() {
		Assert.assertEquals(interval("-10/3, -3"), interval("3, 10/3").negate());
		Assert.assertEquals(interval("-5, 2"), interval("-2, 5").negate());
		Assert.assertEquals(Interval.TOP, Interval.TOP.negate());
	}

	@Test
	public void testAdd() {
		Assert.assertEquals(interval("-3, 7"), interval("-2, 5").add(interval("-1, 2")));
	}

	@Test
	public void testSubtract() {
		Assert.assertEquals(interval("-5/6, 35/3"), interval("7/6, 10").subtract(interval("-5/3, 2")));
	}

	@Test
	public void testMultiply() {
		Assert.assertEquals(interval("0, 4"), interval("-4, 0").multiply(interval("-1")));
		Assert.assertEquals(interval("-4, 4"), interval("-4, 0").multiply(interval("-1, 1")));
		Assert.assertEquals(interval("-18/5, 51/2"), interval("3, 9/2").multiply(interval("-4/5, 17/3")));
	}

	@Test
	public void testDivide() {
		Assert.assertEquals(interval("-6, -3/2"), interval("3, 6").divide(interval("-2, -1")));
		Assert.assertEquals(interval("-2, 3"), interval("-2, 3").divide(interval("1, 4")));
		Assert.assertEquals(interval("-inf, inf"), interval("4, 6").divide(interval("-3, 2")));
	}

	@Test
	public void testSatEqual() {
		checkRelationPredefinedInputs(Interval::satisfyEqual,
				"2,3", "2,3",
				"2,3", "2,3",
				"2,3", "2,3",
				"2,3", "2,3",
				"∅", "∅",
				"∅", "∅");
	}

	@Test
	public void testSatDistinct() {
		checkRelationPredefinedInputs(Interval::satisfyDistinct,
				"1,3", "2,4",
				"2,4", "1,3",
				"2,3", "1,4",
				"1,4", "2,3",
				"1,2", "3,4",
				"3,4", "1,2");
	}

	@Test
	public void testSatLessOrEqual() {
		checkRelationPredefinedInputs(Interval::satisfyLessOrEqual,
				"1,3", "2,4",
				"2,3", "2,3",
				"2,3", "2,4",
				"1,3", "2,3",
				"1,2", "3,4",
				"∅", "∅");
	}

	@Test
	public void testSatGreaterOrEqual() {
		checkRelationPredefinedInputs(Interval::satisfyGreaterOrEqual,
				"2,3", "2,3",
				"2,4", "1,3",
				"2,3", "1,3",
				"2,4", "2,3",
				"∅", "∅",
				"3,4", "1,2");
	}

	private void checkRelationPredefinedInputs(final BiFunction<Interval, Interval, SatisfyingInputs> relFun,
			final String lhsOverlapLeft, final String rhsOverlapLeft,
			final String lhsOverlapRight, final String rhsOverlapRight,
			final String lhsSubset, final String rhsSubset,
			final String lhsSuperset, final String rhsSuperset,
			final String lhsDisjointLeft, final String rhsDisjointLeft,
			final String lhsDisjointRight, final String rhsDisjointRight) {

		checkRelation("1,3", "2,4", relFun, lhsOverlapLeft, rhsOverlapLeft);
		checkRelation("2,4", "1,3", relFun, lhsOverlapRight, rhsOverlapRight);
		checkRelation("2,3", "1,4", relFun, lhsSubset, rhsSubset);
		checkRelation("1,4", "2,3", relFun, lhsSuperset, rhsSuperset);
		checkRelation("1,2", "3,4", relFun, lhsDisjointLeft, rhsDisjointLeft);
		checkRelation("3,4", "1,2", relFun, lhsDisjointRight, rhsDisjointRight);
	}

	private static void checkRelation(final String lhsInput, final String rhsInput,
			final BiFunction<Interval, Interval, SatisfyingInputs> relFun,
			final String expectedLhs, final String expectedRhs) {
		Assert.assertEquals(
				new SatisfyingInputs(interval(expectedLhs), interval(expectedRhs)),
				relFun.apply(interval(lhsInput), interval(rhsInput)));
	}

	private static Interval interval(final String interval) {
		if ("∅".equals(interval)) {
			return Interval.BOTTOM;
		}
		final String[] lowAndHighBound = interval.split(", *");
		if (lowAndHighBound.length < 1 || 2 < lowAndHighBound.length) {
			throw new IllegalArgumentException("Cannot parse rational: " + interval);
		}
		final Rational lowBound = rational(lowAndHighBound[0]);
		if (lowAndHighBound.length == 1) {
			return Interval.point(lowBound);
		}
		return Interval.of(lowBound, rational(lowAndHighBound[1]));
	}

	private static Rational rational(final String rational) {
		if ("inf".equals(rational) || "+inf".equals(rational)) {
			return Rational.POSITIVE_INFINITY;
		} else if ("-inf".equals(rational)) {
			return Rational.NEGATIVE_INFINITY;
		}
		final String[] numAndDenom = rational.split("/");
		if (numAndDenom.length < 1 || 2 < numAndDenom.length) {
			throw new IllegalArgumentException("Cannot parse rational: " + rational);
		}
		final BigInteger numerator = new BigInteger(numAndDenom[0]);
		if (numAndDenom.length == 1) {
			return Rational.valueOf(numerator, BigInteger.ONE);
		}
		return Rational.valueOf(numerator, new BigInteger(numAndDenom[1]));
	}
}
