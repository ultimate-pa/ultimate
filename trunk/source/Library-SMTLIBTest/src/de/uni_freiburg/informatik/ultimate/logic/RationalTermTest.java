/*
 * Copyright (C) 2021 University of Freiburg
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

import java.math.BigDecimal;
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
public final class RationalTermTest {

	/**
	 * Check that rational.toTerm(intSort) produces the same term as parsing the
	 * corresponding normalized form.
	 *
	 * @param script a script used for parsing.
	 */
	private void internalTestInputInt(final Script script) {
		final Sort intSort = script.sort("Int");

		Term term;
		Rational rat;
		term = script.numeral(BigInteger.valueOf(1));
		rat = Rational.valueOf(1, 1);
		Assert.assertSame(term, rat.toTerm(intSort));
		term = script.term("-", script.numeral(BigInteger.valueOf(2)));
		rat = Rational.valueOf(-2, 1);
		Assert.assertSame(term, rat.toTerm(intSort));
		term = script.numeral(BigInteger.valueOf(2));
		rat = Rational.valueOf(10, 5);
		Assert.assertSame(term, rat.toTerm(intSort));
		term = script.numeral(BigInteger.valueOf(0));
		rat = Rational.valueOf(0, 2);
		Assert.assertSame(term, rat.toTerm(intSort));

		// check that non-normalized decimals are preserved
		term = script.term("-", script.numeral("0"));
		Assert.assertEquals(term.toString(), "(- 0)");
		term = script.term("-", script.term("-", script.numeral("2")));
		Assert.assertEquals(term.toString(), "(- (- 2))");
	}

	/**
	 * Check that rational.toTerm(realSort) produces the same term as parsing the
	 * corresponding normalized form.
	 *
	 * @param script a script used for parsing.
	 */
	private void internalTestInputReal(final Script script) {
		final Sort realSort = script.sort("Real");

		Term term;
		Rational rat;
		term = script.decimal("1.0");
		rat = Rational.valueOf(1, 1);
		Assert.assertSame(term, rat.toTerm(realSort));
		term = script.term("-", script.decimal("2.0"));
		rat = Rational.valueOf(-2, 1);
		Assert.assertSame(term, rat.toTerm(realSort));
		term = script.decimal("2.0");
		rat = Rational.valueOf(10, 5);
		Assert.assertSame(term, rat.toTerm(realSort));
		term = script.decimal("0.0");
		rat = Rational.valueOf(0, 2);
		Assert.assertSame(term, rat.toTerm(realSort));

		term = script.term("/", script.decimal("1.0"), script.decimal("2.0"));
		rat = Rational.valueOf(1, 2);
		Assert.assertSame(term, rat.toTerm(realSort));
		term = script.term("/", script.term("-", script.decimal("1.0")), script.decimal("2.0"));
		rat = Rational.valueOf(-1, 2);
		Assert.assertSame(term, rat.toTerm(realSort));
		term = script.term("/", script.decimal("7.0"), script.decimal("5.0"));
		rat = Rational.valueOf(7, 5);
		Assert.assertSame(term, rat.toTerm(realSort));
		term = script.term("/", script.term("-", script.decimal("41.0")), script.decimal("107.0"));
		rat = Rational.valueOf(123, -321);
		Assert.assertSame(term, rat.toTerm(realSort));

		// check that non-normalized ratios are preserved
		term = script.term("-", script.numeral("0"));
		Assert.assertEquals(term.toString(), "(- 0)");
		term = script.term("-", script.decimal("0.0"));
		Assert.assertEquals(term.toString(), "(- 0.0)");
		term = script.term("-", script.numeral("2"));
		Assert.assertEquals(term.toString(), "(- 2)");
		term = script.term("/", script.numeral("1"), script.numeral("2"));
		Assert.assertEquals(term.toString(), "(/ 1 2)");
		term = script.term("/", script.term("-", script.numeral("1")), script.numeral("2"));
		Assert.assertEquals(term.toString(), "(/ (- 1) 2)");
		term = script.term("/", script.numeral("1"), script.term("-", script.numeral("2")));
		Assert.assertEquals(term.toString(), "(/ 1 (- 2))");
		term = script.term("/", script.numeral("3"), script.numeral("9"));
		Assert.assertEquals(term.toString(), "(/ 3 9)");
		term = script.term("/", script.numeral("7"), script.numeral("5"));
		Assert.assertEquals(term.toString(), "(/ 7 5)");
		term = script.term("/", script.numeral("7"), script.numeral("1"));
		Assert.assertEquals(term.toString(), "(/ 7 1)");
		term = script.term("/", script.numeral("0"), script.numeral("0"));
		Assert.assertEquals(term.toString(), "(/ 0 0)");
		term = script.term("/", script.numeral("0"), script.numeral("1"));
		Assert.assertEquals(term.toString(), "(/ 0 1)");
		term = script.term("/", script.numeral("0"), script.numeral("2"));
		Assert.assertEquals(term.toString(), "(/ 0 2)");
		term = script.term("/", script.numeral("1"), script.numeral("0"));
		Assert.assertEquals(term.toString(), "(/ 1 0)");
		term = script.term("/", script.numeral("2"), script.numeral("0"));
		Assert.assertEquals(term.toString(), "(/ 2 0)");
		term = script.term("/", script.term("-", script.numeral("123")), script.numeral("321"));
		Assert.assertEquals(term.toString(), "(/ (- 123) 321)");
		term = script.term("/", script.decimal("1.0"), script.decimal("2.0"));
		Assert.assertEquals(term.toString(), "(/ 1.0 2.0)");
		term = script.term("/", script.numeral("1"), script.decimal("2.0"));
		Assert.assertEquals(term.toString(), "(/ 1 2.0)");
		term = script.term("/", script.decimal("1.0"), script.numeral("2"));
		Assert.assertEquals(term.toString(), "(/ 1.0 2)");
		term = script.term("-", script.term("/", script.numeral("7"), script.numeral("5")));
		Assert.assertEquals(term.toString(), "(- (/ 7 5))");

		// check that non-normalized decimals are preserved
		term = script.term("-", script.numeral("0"));
		Assert.assertEquals(term.toString(), "(- 0)");
		term = script.term("-", script.term("-", script.numeral("2")));
		Assert.assertEquals(term.toString(), "(- (- 2))");
		term = script.term("-", script.decimal("0.0"));
		Assert.assertEquals(term.toString(), "(- 0.0)");
		term = script.decimal("0.00");
		Assert.assertEquals(term.toString(), "0.00");
		term = script.term("-", script.decimal("0.00"));
		Assert.assertEquals(term.toString(), "(- 0.00)");
		term = script.decimal("100.00");
		Assert.assertEquals(term.toString(), "100.00");
		term = script.term("-", script.decimal("100.00"));
		Assert.assertEquals(term.toString(), "(- 100.00)");
		term = script.decimal("0.1");
		Assert.assertEquals(term.toString(), "0.1");
		term = script.term("-", script.decimal("0.1"));
		Assert.assertEquals(term.toString(), "(- 0.1)");
		term = script.term("-", script.term("-", script.decimal("0.1")));
		Assert.assertEquals(term.toString(), "(- (- 0.1))");
	}

	/**
	 * Check the output of rational.toTerm(intSort).
	 *
	 * @param script a script used for creating terms/sorts.
	 */
	private void internalTestOutputInt(final Script script) {
		final Sort intSort = script.sort("Int");

		Rational rat;
		rat = Rational.valueOf(1, 1);
		Assert.assertEquals(rat.toTerm(intSort).toString(), "1");
		rat = Rational.valueOf(-2, 1);
		Assert.assertEquals(rat.toTerm(intSort).toString(), "(- 2)");
		rat = Rational.valueOf(10, 5);
		Assert.assertEquals(rat.toTerm(intSort).toString(), "2");
		rat = Rational.valueOf(0, 2);
		Assert.assertEquals(rat.toTerm(intSort).toString(), "0");
	}

	/**
	 * Check the output of rational.toTerm(realSort).
	 *
	 * @param script a script used for creating terms/sorts.
	 */
	private void internalTestOutputReal(final Script script) {
		final Sort realSort = script.sort("Real");

		Rational rat;
		rat = Rational.valueOf(1, 1);
		Assert.assertEquals(rat.toTerm(realSort).toString(), "1.0");
		rat = Rational.valueOf(-2, 1);
		Assert.assertEquals(rat.toTerm(realSort).toString(), "(- 2.0)");
		rat = Rational.valueOf(10, 5);
		Assert.assertEquals(rat.toTerm(realSort).toString(), "2.0");
		rat = Rational.valueOf(0, 2);
		Assert.assertEquals(rat.toTerm(realSort).toString(), "0.0");

		rat = Rational.valueOf(1, 2);
		Assert.assertEquals(rat.toTerm(realSort).toString(), "(/ 1.0 2.0)");
		rat = Rational.valueOf(-1, 2);
		Assert.assertEquals(rat.toTerm(realSort).toString(), "(/ (- 1.0) 2.0)");
		rat = Rational.valueOf(1, -2);
		Assert.assertEquals(rat.toTerm(realSort).toString(), "(/ (- 1.0) 2.0)");
		rat = Rational.valueOf(3, -9);
		Assert.assertEquals(rat.toTerm(realSort).toString(), "(/ (- 1.0) 3.0)");
		rat = Rational.valueOf(7, 5);
		Assert.assertEquals(rat.toTerm(realSort).toString(), "(/ 7.0 5.0)");
		rat = Rational.valueOf(123, -321);
		Assert.assertEquals(rat.toTerm(realSort).toString(), "(/ (- 41.0) 107.0)");
	}

	/**
	 * Check that various ways to create terms yield the same result.
	 *
	 * @param script an SMT script to create terms.
	 */
	private void internalTestNormalizedNumeral(final Script script) {
		Term term = script.numeral("0");
		Assert.assertSame(term, script.numeral(BigInteger.ZERO));
		Assert.assertSame(term, script.numeral(new BigInteger("-0")));
		Assert.assertSame(term, script.numeral(new BigInteger("0").negate()));
		Assert.assertEquals(term.toString(), "0");

		term = script.term("-", script.numeral("1"));
		Assert.assertSame(term, script.numeral(BigInteger.ONE.negate()));
		Assert.assertSame(term, script.numeral(new BigInteger("-1")));
		Assert.assertEquals(term.toString(), "(- 1)");
	}

	/**
	 * Check that various ways to create terms yield the same result.
	 *
	 * @param script an SMT script to create terms.
	 */
	private void internalTestNormalizedDecimal(final Script script) {
		Term term = script.decimal("100.0");
		Assert.assertSame(term, script.decimal(new BigDecimal(BigInteger.ONE, -2)));
		Assert.assertSame(term, script.decimal(new BigDecimal(BigInteger.valueOf(100), 0)));
		Assert.assertSame(term, script.decimal(new BigDecimal(BigInteger.valueOf(1000), 1)));
		Assert.assertSame(term, Rational.valueOf(100, 1).toTerm(script.sort("Real")));

		term = script.decimal("0.1");
		Assert.assertSame(term, script.decimal(new BigDecimal(BigInteger.ONE, 1)));
		Assert.assertSame(term, script.decimal(new BigDecimal("0.1")));

		term = script.term("-", script.decimal("0.1"));
		Assert.assertSame(term, script.decimal(new BigDecimal(BigInteger.ONE, 1).negate()));
		Assert.assertSame(term, script.decimal(new BigDecimal("-0.1")));

		term = script.decimal("100.00");
		Assert.assertSame(term, script.decimal(new BigDecimal(BigInteger.valueOf(10000), 2)));
		Assert.assertSame(term, script.decimal(new BigDecimal("100.00")));
	}

	@Test
	public void testLIA() {
		final Script script = new NoopScript();
		script.setLogic(Logics.QF_LIA);

		internalTestInputInt(script);
		internalTestOutputInt(script);
		internalTestNormalizedNumeral(script);
	}

	@Test
	public void testLRA() {
		final Script script = new NoopScript();
		script.setLogic(Logics.QF_LRA);

		internalTestInputReal(script);
		internalTestOutputReal(script);
		internalTestNormalizedNumeral(script);
		internalTestNormalizedDecimal(script);
	}

	@Test
	public void testLIRA() {
		final Script script = new NoopScript();
		script.setLogic(Logics.QF_LIRA);

		internalTestInputInt(script);
		internalTestInputReal(script);
		internalTestOutputInt(script);
		internalTestOutputReal(script);
		internalTestNormalizedNumeral(script);
		internalTestNormalizedDecimal(script);
	}
}
