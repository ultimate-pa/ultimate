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

public class IntervalContainmentChecks {

	@Test
	public void testContainmentClosedPositive() {
		// Create Interval [2;3]
		IntervalDomainValue int1 = HelperFunctions.createInterval(2, 3);

		// Create Interval [0;10]
		IntervalDomainValue int2 = HelperFunctions.createInterval(0, 10);

		// Expected result: true
		assertTrue(HelperFunctions.checkInclusion(int1, int2));
		assertTrue(HelperFunctions.checkInclusion(int2, int1));
	}

	@Test
	public void testUnContainmentClosedPositive() {
		// Create Interval [0;3]
		IntervalDomainValue int1 = HelperFunctions.createInterval(0, 3);

		// Create Interval [2;10]
		IntervalDomainValue int2 = HelperFunctions.createInterval(2, 10);

		// Expected result: true
		assertFalse(HelperFunctions.checkInclusion(int1, int2));
		assertFalse(HelperFunctions.checkInclusion(int2, int1));
	}

	@Test
	public void testContainmentClosedNegative() {
		// Create Interval [-3;-2]
		IntervalDomainValue int1 = HelperFunctions.createInterval(-3, -2);

		// Create Interval [-10;0]
		IntervalDomainValue int2 = HelperFunctions.createInterval(-10, 0);

		// Expected result: true
		assertTrue(HelperFunctions.checkInclusion(int1, int2));
		assertTrue(HelperFunctions.checkInclusion(int2, int1));
	}

	@Test
	public void testUnContainmentClosedNegative() {
		// Create Interval [-3;0]
		IntervalDomainValue int1 = HelperFunctions.createInterval(-3, 0);

		// Create Interval [-10;-2]
		IntervalDomainValue int2 = HelperFunctions.createInterval(-10, -2);

		// Expected result: true
		assertFalse(HelperFunctions.checkInclusion(int1, int2));
		assertFalse(HelperFunctions.checkInclusion(int2, int1));
	}

	@Test
	public void testContainmentClosedMixed() {
		// Create Interval [-2;3]
		IntervalDomainValue int1 = HelperFunctions.createInterval(-2, 3);

		// Create Interval [-10;10]
		IntervalDomainValue int2 = HelperFunctions.createInterval(-10, 10);

		// Expected result: true
		assertTrue(HelperFunctions.checkInclusion(int1, int2));
		assertTrue(HelperFunctions.checkInclusion(int2, int1));
	}

	@Test
	public void testUnContainmentClosedMixed() {
		// Create Interval [-10;3]
		IntervalDomainValue int1 = HelperFunctions.createInterval(-10, 3);

		// Create Interval [-2;10]
		IntervalDomainValue int2 = HelperFunctions.createInterval(-2, 10);

		// Expected result: true
		assertFalse(HelperFunctions.checkInclusion(int1, int2));
		assertFalse(HelperFunctions.checkInclusion(int2, int1));
	}

	@Test
	public void testContainmentOpenPositive() {
		// Create Interval [2; \infty]
		IntervalDomainValue int1 = new IntervalDomainValue(new IntervalValue(new BigDecimal(2)), new IntervalValue());

		// Create Interval [0; \infty]
		IntervalDomainValue int2 = new IntervalDomainValue(new IntervalValue(new BigDecimal(0)), new IntervalValue());

		// Expected result: true
		assertTrue(HelperFunctions.checkInclusion(int1, int2));
		assertTrue(HelperFunctions.checkInclusion(int2, int1));
	}

	@Test
	public void testUnContainmentOpenPositive() {
		// Create Interval [2; \infty]
		IntervalDomainValue int1 = new IntervalDomainValue(new IntervalValue(new BigDecimal(2)), new IntervalValue());

		// Create Interval [0; \infty]
		IntervalDomainValue int2 = new IntervalDomainValue(new IntervalValue(new BigDecimal(0)), new IntervalValue());

		// Expected result: true
		assertFalse(HelperFunctions.checkInclusion(int1, int2));
		assertFalse(HelperFunctions.checkInclusion(int2, int1));
	}
}
