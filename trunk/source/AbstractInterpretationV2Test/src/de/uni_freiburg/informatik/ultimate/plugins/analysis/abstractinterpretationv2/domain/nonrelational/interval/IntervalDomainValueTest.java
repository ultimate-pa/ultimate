/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import static org.junit.Assert.*;

import java.math.BigDecimal;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalValue;

/**
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public class IntervalDomainValueTest {

	@Test
	public void testInfiniteIntervalValue() {

		IntervalValue infiniteValue = new IntervalValue();
		assertTrue(infiniteValue.getValue() == null);
		assertTrue(infiniteValue.isInfinity());
	}

	@Test
	public void testBoundedIntervalValue() {
		IntervalValue intv = new IntervalValue(new BigDecimal(0));

		assertTrue(intv.getValue().equals(new BigDecimal(0)));
		assertFalse(intv.isInfinity());

		IntervalValue intvNeg = new IntervalValue(new BigDecimal(-1));
		assertTrue(intvNeg.getValue().equals(new BigDecimal(-1)));
		assertFalse(intvNeg.isInfinity());

		IntervalValue intvPos = new IntervalValue(new BigDecimal(1));
		assertTrue(intvPos.getValue().equals(new BigDecimal(1)));
		assertFalse(intvPos.isInfinity());
	}

	@Test
	public void testInfiniteInterval() {
		IntervalDomainValue intv = new IntervalDomainValue();

		assertTrue(intv.getUpper().equals(new IntervalValue()));
		assertTrue(intv.getUpper().isInfinity());
		assertTrue(intv.getLower().equals(new IntervalValue()));
		assertTrue(intv.getLower().isInfinity());
	}

	@Test
	public void testBoundedInterval() {
		IntervalDomainValue intvUpperOpen = new IntervalDomainValue(new IntervalValue(new BigDecimal(0)),
		        new IntervalValue());

		assertFalse(intvUpperOpen.getLower().isInfinity());
		assertTrue(intvUpperOpen.getUpper().isInfinity());

		IntervalDomainValue intvLowerOpen = new IntervalDomainValue(new IntervalValue(),
		        new IntervalValue(new BigDecimal(100)));

		assertTrue(intvLowerOpen.getLower().isInfinity());
		assertFalse(intvLowerOpen.getUpper().isInfinity());
	}

	@Test
	public void testBottomIntervals() {
		IntervalDomainValue bottomInterval = new IntervalDomainValue(true);
		assertTrue(bottomInterval.isBottom());
		assertTrue(bottomInterval.getLower() == null);
		assertTrue(bottomInterval.getUpper() == null);
	}

	@Test
	public void testAbs() {
		
		// bottom
		assertAbs("1", "-1", "1", "-1");

		// intervals containing zero
		assertAbs("inf", "inf", "0", "inf");
		assertAbs("-1", "inf", "0", "inf");
		assertAbs("inf", "1", "0", "inf");
		assertAbs("-2", "3", "0", "3");
		assertAbs("-3", "2", "0", "3");

		// negative intervals
		assertAbs("inf", "-1", "1", "inf");
		assertAbs("-2", "-1", "1", "2");

		// positive intervals
		assertAbs("1", "inf", "1", "inf");
		assertAbs("1", "2", "1", "2");
	}

	private void assertAbs(String a, String b, String c, String d) {
		IntervalDomainValue ab, cd, result;
		ab = parseInterval(a, b);
		cd = parseInterval(c, d);
		result = ab.abs();
		assertTrue("expected " + cd + ", was " + result, result.isEqualTo(cd));
	}
	
	@Test
	public void testModulo() {
		// TODO Test is incomplete. Test all cases!

		assertMod( "7",  "3", true, "1");
		assertMod( "7", "-3", true, "1");
		assertMod("-7",  "3", true, "2");
		assertMod("-7", "-3", true, "2");

		assertMod("4", "23", "25", "25", false, "4", "23");
		assertMod("4", "23", "-25", "-25", true, "4", "23");
		assertMod("-99", "23", "-25", "-25", false, "0", "25");
		assertMod("-99", "23", "25", "25", true, "0", "24");

		assertMod("4", "20", "-25", "-22", false, "4", "20");
		assertMod("4", "20", "-25", "-22", true, "4", "20");
		assertMod("-99", "20", "-25", "-22", false, "0", "25");
		assertMod("-99", "20", "-25", "-22", true, "0", "24");

		assertMod("1", "1", "0", "0", false, "inf", "inf");
		assertMod("1", "1", "-4", "5", false, "inf", "inf");
	}

	private void assertMod(String ab, String cd, boolean intDiv, String ef) {
		IntervalDomainValue iab, icd, ief, result;
		iab = parseInterval(ab, ab);
		icd = parseInterval(cd, cd);
		ief = parseInterval(ef, ef);
		result = iab.modulo(icd, intDiv);
		assertTrue("expected " + ief + ", was " + result, result.isEqualTo(ief));
	}
	
	private void assertMod(String a, String b, String c, String d, boolean intDiv, String e, String f) {
		IntervalDomainValue ab, cd, ef, result;
		ab = parseInterval(a, b);
		cd = parseInterval(c, d);
		ef = parseInterval(e, f);
		result = ab.modulo(cd, intDiv);
		assertTrue("expected " + ef + ", was " + result, result.isEqualTo(ef));
	}
	
	private IntervalDomainValue parseInterval(String min, String max) {
		return new IntervalDomainValue(parseIntervalValue(min), parseIntervalValue(max));
	}
	
	private IntervalValue parseIntervalValue(String v) {
		if ("inf".equals(v)) {
			return new IntervalValue();
		}
		return new IntervalValue(v);
	}
}
