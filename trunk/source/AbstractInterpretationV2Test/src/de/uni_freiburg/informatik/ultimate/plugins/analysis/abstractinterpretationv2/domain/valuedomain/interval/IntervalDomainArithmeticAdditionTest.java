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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.interval;

import static org.junit.Assert.*;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.interval.IntervalDomainValue;

public class IntervalDomainArithmeticAdditionTest {

	@Test
	public void testIntervalAddition() {

		// Interval [1;10]
		IntervalDomainValue interval1 = HelperFunctions.createInterval(1, 10);

		// Interval [15;20]
		IntervalDomainValue interval2 = HelperFunctions.createInterval(15, 20);

		// Result should be [16;30]
		IntervalDomainValue expectedResult = HelperFunctions.createInterval(16, 30);

		assertTrue(HelperFunctions.computeAdditionResult(interval1, interval2, expectedResult));
	}

	@Test
	public void testInfiniteIntervalAddition() {
		// Interval [1, \infty]
		IntervalDomainValue interval1 = HelperFunctions.createInterval(1, 1);
		interval1.getUpper().setToInfinity();

		assertTrue(interval1.isUnbounded());
		assertFalse(interval1.isInfinity());

		// Interval [1,2]
		IntervalDomainValue interval2 = HelperFunctions.createInterval(1, 2);

		// Result should be [2, \infty]
		IntervalDomainValue expectedResult1 = HelperFunctions.createInterval(2, 2);
		expectedResult1.getUpper().setToInfinity();

		assertTrue(HelperFunctions.computeAdditionResult(interval1, interval2, expectedResult1));

		// Interval [1, \infty]
		IntervalDomainValue interval3 = HelperFunctions.createInterval(-1, -1);
		interval3.getUpper().setToInfinity();

		// Result should be [0, \infty]
		IntervalDomainValue expectedResult2 = HelperFunctions.createInterval(0, 0);
		expectedResult2.getUpper().setToInfinity();

		assertTrue(HelperFunctions.computeAdditionResult(interval3, interval2, expectedResult2));

		// Interval [-\infty, 0]
		IntervalDomainValue interval4 = HelperFunctions.createInterval(0, 0);
		interval4.getLower().setToInfinity();
		assertTrue(interval4.isUnbounded());
		assertFalse(interval4.isInfinity());

		// Result should be [-\infty, 2]
		IntervalDomainValue expectedResult3 = HelperFunctions.createInterval(0, 2);
		expectedResult3.getLower().setToInfinity();

		assertTrue(HelperFunctions.computeAdditionResult(interval4, interval2, expectedResult3));

		// Interval [\-infty, \infty]
		IntervalDomainValue infinite = new IntervalDomainValue();
		assertTrue(infinite.isInfinity());
		assertFalse(infinite.isBottom());
		assertTrue(infinite.getLower().isInfinity());
		assertTrue(infinite.getUpper().isInfinity());
		assertTrue(infinite.isUnbounded());

		assertTrue(HelperFunctions.computeAdditionResult(infinite, infinite, infinite));
	}

	@Test
	public void testNegativeIntervalAddition() {

		// Interval [-30;-20]
		IntervalDomainValue interval1 = HelperFunctions.createInterval(-30, -20);

		// Interval [-5;-1]
		IntervalDomainValue interval2 = HelperFunctions.createInterval(-5, -1);

		// Result should be [-35;-21]
		IntervalDomainValue expectedResult = HelperFunctions.createInterval(-35, -21);

		assertTrue(HelperFunctions.computeAdditionResult(interval1, interval2, expectedResult));
	}

	@Test
	public void testMixedNegativeIntervalAddition() {
		// Interval [-30; -20]
		IntervalDomainValue interval1 = HelperFunctions.createInterval(-30, -20);

		// Interval [5; 10]
		IntervalDomainValue interval2 = HelperFunctions.createInterval(5, 10);

		// Result should be [-25;-10]
		IntervalDomainValue expectedResult = HelperFunctions.createInterval(-25, -10);

		assertTrue(HelperFunctions.computeAdditionResult(interval1, interval2, expectedResult));

		// Interval [-10; 5]
		IntervalDomainValue interval3 = HelperFunctions.createInterval(-10, 5);

		// Result should be [-5; 15]
		IntervalDomainValue expectedResult1 = HelperFunctions.createInterval(-5, 15);

		assertTrue(HelperFunctions.computeAdditionResult(interval3, interval2, expectedResult1));
	}

	@Test
	public void testBottomIntervalAddition() {
		// Interval \bot
		IntervalDomainValue interval1 = new IntervalDomainValue(true);
		assertTrue(interval1.isBottom());
		assertFalse(interval1.isInfinity());

		// Interval [0, 1]
		IntervalDomainValue interval2 = HelperFunctions.createInterval(0, 1);

		// Result should be \bot
		IntervalDomainValue expectedResult = new IntervalDomainValue(true);

		assertTrue(HelperFunctions.computeAdditionResult(interval1, interval2, expectedResult));

		assertTrue(HelperFunctions.computeAdditionResult(interval2, interval1, expectedResult));

		assertTrue(HelperFunctions.computeAdditionResult(interval1, interval1, expectedResult));
	}
}
