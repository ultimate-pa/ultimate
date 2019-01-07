/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.explicit;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ExplicitValueDomainTest {

	private static final String STR_BOT = "BOT";
	private static final String STR_TOP = "TOP";
	private static final String STR_ZERO = "0";
	private static final String STR_ONE = "1";
	private static final String STR_MONE = "-1";

	private static final BaseExplicitValueValue BOT = ExplicitValueBottom.DEFAULT;
	private static final BaseExplicitValueValue TOP = ExplicitValueTop.DEFAULT;
	private static final BaseExplicitValueValue ZERO = new ExplicitValueValue(Rational.ZERO);
	private static final BaseExplicitValueValue ONE = new ExplicitValueValue(Rational.ONE);
	private static final BaseExplicitValueValue MONE = new ExplicitValueValue(Rational.MONE);
	private static final BaseExplicitValueValue FIVE = new ExplicitValueValue(Rational.valueOf(5, 1));

	@Test
	public void testCreate() {
		BaseExplicitValueValue x = TOP;
		assertEquals(STR_TOP, x.toString());
		x = BOT;
		assertEquals(STR_BOT, x.toString());
		x = FIVE;
		assertEquals("5", x.toString());
		x = MONE;
		assertEquals("-1", x.toString());
		x = ZERO;
		assertEquals(STR_ZERO, x.toString());
	}

	@Test
	public void testMerge() {
		assertEquals(STR_BOT, BOT.merge(BOT).toString());
		assertEquals(STR_TOP, BOT.merge(TOP).toString());
		assertEquals(STR_TOP, TOP.merge(TOP).toString());
		assertEquals(STR_ONE, ONE.merge(ONE).toString());
		assertEquals(STR_TOP, ONE.merge(FIVE).toString());
	}

	@Test
	public void testIntersect() {
		assertEquals(STR_BOT, BOT.intersect(BOT).toString());
		assertEquals(STR_BOT, BOT.intersect(TOP).toString());
		assertEquals(STR_TOP, TOP.intersect(TOP).toString());
		assertEquals(STR_ONE, ONE.intersect(ONE).toString());
		assertEquals(STR_BOT, ONE.intersect(FIVE).toString());
	}

	@Test
	public void testAddSub() {
		assertEquals(STR_BOT, BOT.add(BOT).toString());
		assertEquals(STR_BOT, BOT.add(TOP).toString());
		assertEquals(STR_TOP, TOP.add(TOP).toString());
		assertEquals("2", ONE.add(ONE).toString());
		assertEquals("6", ONE.add(FIVE).toString());

		assertEquals(STR_BOT, BOT.subtract(BOT).toString());
		assertEquals(STR_BOT, BOT.subtract(TOP).toString());
		assertEquals(STR_TOP, TOP.subtract(TOP).toString());
		assertEquals(STR_ZERO, ONE.subtract(ONE).toString());
		assertEquals("-4", ONE.subtract(FIVE).toString());
	}

	@Test
	public void testMod() {
		assertEquals(STR_BOT, BOT.modulo(BOT).toString());
		assertEquals(STR_BOT, BOT.modulo(TOP).toString());
		assertEquals(STR_TOP, TOP.modulo(TOP).toString());
		assertEquals("0", ONE.modulo(ONE).toString());
		assertEquals("0", ZERO.modulo(ONE).toString());
		assertEquals("0", FIVE.modulo(ONE).toString());
		assertEquals("1", ONE.modulo(FIVE).toString());

	}

	@Test
	public void testMult() {
		assertEquals(STR_BOT, BOT.multiply(BOT).toString());
		assertEquals(STR_BOT, BOT.multiply(TOP).toString());
		assertEquals(STR_TOP, TOP.multiply(TOP).toString());
		assertEquals("1", ONE.multiply(ONE).toString());
		assertEquals("0", ZERO.multiply(ONE).toString());
		assertEquals("5", FIVE.multiply(ONE).toString());
		assertEquals("5", ONE.multiply(FIVE).toString());
		assertEquals("25", FIVE.multiply(FIVE).toString());
		assertEquals("-5", MONE.multiply(FIVE).toString());
	}

	@Test
	public void testDiv() {
		assertEquals(STR_BOT, BOT.divideInteger(BOT).toString());
		assertEquals(STR_BOT, BOT.divideInteger(TOP).toString());
		assertEquals(STR_TOP, TOP.divideInteger(TOP).toString());
		assertEquals("1", ONE.divideInteger(ONE).toString());
		assertEquals("0", ZERO.divideInteger(ONE).toString());
		assertEquals("5", FIVE.divideInteger(ONE).toString());
		assertEquals("0", ONE.divideInteger(FIVE).toString());
		assertEquals("1", FIVE.divideInteger(FIVE).toString());
		assertEquals("-1", MONE.divideInteger(FIVE).toString());

		assertEquals(STR_BOT, BOT.divideReal(BOT).toString());
		assertEquals(STR_BOT, BOT.divideReal(TOP).toString());
		assertEquals(STR_TOP, TOP.divideReal(TOP).toString());
		assertEquals("1", ONE.divideReal(ONE).toString());
		assertEquals("0", ZERO.divideReal(ONE).toString());
		assertEquals("5", FIVE.divideReal(ONE).toString());
		assertEquals("1/5", ONE.divideReal(FIVE).toString());
		assertEquals("1", FIVE.divideReal(FIVE).toString());
		assertEquals("-1/5", MONE.divideReal(FIVE).toString());
	}

	@Test
	public void testNeg() {
		assertEquals(STR_BOT, BOT.negate().toString());
		assertEquals(STR_BOT, BOT.negate().toString());
		assertEquals(STR_TOP, TOP.negate().toString());
		assertEquals("-1", ONE.negate().toString());
		assertEquals("0", ZERO.negate().toString());
		assertEquals("-5", FIVE.negate().toString());
		assertEquals("1", MONE.negate().toString());
	}

	@Test
	public void testGreaterThan() {
		assertEquals(STR_BOT, BOT.greaterThan(BOT).toString());
		assertEquals(STR_BOT, BOT.greaterThan(TOP).toString());
		assertEquals(STR_BOT, TOP.greaterThan(BOT).toString());
		assertEquals(STR_TOP, TOP.greaterThan(TOP).toString());
		assertEquals(STR_BOT, ONE.greaterThan(ONE).toString());
		assertEquals(STR_BOT, ZERO.greaterThan(ONE).toString());
		assertEquals("5", FIVE.greaterThan(ONE).toString());
		assertEquals(STR_BOT, ONE.greaterThan(FIVE).toString());
		assertEquals(STR_BOT, FIVE.greaterThan(FIVE).toString());
		assertEquals(STR_BOT, MONE.greaterThan(FIVE).toString());
	}

	@Test
	public void testGreaterOrEqual() {
		assertEquals(STR_BOT, BOT.greaterOrEqual(BOT).toString());
		assertEquals(STR_BOT, BOT.greaterOrEqual(TOP).toString());
		assertEquals(STR_BOT, TOP.greaterOrEqual(BOT).toString());
		assertEquals(STR_TOP, TOP.greaterOrEqual(TOP).toString());
		assertEquals(STR_ONE, ONE.greaterOrEqual(ONE).toString());
		assertEquals(STR_BOT, ZERO.greaterOrEqual(ONE).toString());
		assertEquals("5", FIVE.greaterOrEqual(ONE).toString());
		assertEquals(STR_BOT, ONE.greaterOrEqual(FIVE).toString());
		assertEquals("5", FIVE.greaterOrEqual(FIVE).toString());
		assertEquals(STR_BOT, MONE.greaterOrEqual(FIVE).toString());
	}

	@Test
	public void testLessThan() {
		assertEquals(STR_BOT, BOT.lessThan(BOT).toString());
		assertEquals(STR_BOT, BOT.lessThan(TOP).toString());
		assertEquals(STR_BOT, TOP.lessThan(BOT).toString());
		assertEquals(STR_TOP, TOP.lessThan(TOP).toString());
		assertEquals(STR_BOT, ONE.lessThan(ONE).toString());
		assertEquals(STR_ZERO, ZERO.lessThan(ONE).toString());
		assertEquals(STR_BOT, FIVE.lessThan(ONE).toString());
		assertEquals(STR_ONE, ONE.lessThan(FIVE).toString());
		assertEquals(STR_BOT, FIVE.lessThan(FIVE).toString());
		assertEquals(STR_MONE, MONE.lessThan(FIVE).toString());
	}

	@Test
	public void testLessOrEqual() {
		assertEquals(STR_BOT, BOT.lessOrEqual(BOT).toString());
		assertEquals(STR_BOT, BOT.lessOrEqual(TOP).toString());
		assertEquals(STR_BOT, TOP.lessOrEqual(BOT).toString());
		assertEquals(STR_TOP, TOP.lessOrEqual(TOP).toString());
		assertEquals(STR_ONE, ONE.lessOrEqual(ONE).toString());
		assertEquals(STR_ZERO, ZERO.lessOrEqual(ONE).toString());
		assertEquals(STR_BOT, FIVE.lessOrEqual(ONE).toString());
		assertEquals(STR_ONE, ONE.lessOrEqual(FIVE).toString());
		assertEquals("5", FIVE.lessOrEqual(FIVE).toString());
		assertEquals(STR_MONE, MONE.lessOrEqual(FIVE).toString());
	}

}
