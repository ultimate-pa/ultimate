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

		IntervalDomainValue intvLowerOpen = new IntervalDomainValue(new IntervalValue(), new IntervalValue(
		        new BigDecimal(100)));

		assertTrue(intvLowerOpen.getLower().isInfinity());
		assertFalse(intvLowerOpen.getUpper().isInfinity());
	}

	@Test
	public void testBottomIntervals() {
		IntervalDomainValue bottomInterval = new IntervalDomainValue(true);
		assertTrue(bottomInterval.isBottom());
		assertTrue(bottomInterval.getLower() == null);
		assertTrue(bottomInterval.getUpper() == null);

		IntervalDomainValue normalInterval = new IntervalDomainValue(new IntervalValue(new BigDecimal(1)),
		        new IntervalValue(new BigDecimal(10)));
	}
}
