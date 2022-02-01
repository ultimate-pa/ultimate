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

import static org.junit.Assert.assertTrue;

import java.math.BigDecimal;

import org.junit.Test;

/**
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalDomainArithmeticDivisionTest {

	@Test
	public void TestIntervalDivisionPointIntervalPositive() {
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(10, 10);

		final IntervalDomainValue interval2 = HelperFunctions.createInterval(2, 2);

		final IntervalDomainValue expectedResult = HelperFunctions.createInterval(5, 5);

		assertTrue(HelperFunctions.computeDivisionResultReal(interval1, interval2, expectedResult));
	}

	@Test
	public void TestIntervalDivisionPointIntervalNegative() {
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(-10, -10);

		final IntervalDomainValue interval2 = HelperFunctions.createInterval(2, 2);

		final IntervalDomainValue expectedResult = HelperFunctions.createInterval(-5, -5);

		assertTrue(HelperFunctions.computeDivisionResultReal(interval1, interval2, expectedResult));
	}

	@Test
	public void TestIntervalDivisionPointIntervalNegativePositiveResult() {
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(-10, -10);

		final IntervalDomainValue interval2 = HelperFunctions.createInterval(-2, -2);

		final IntervalDomainValue expectedResult = HelperFunctions.createInterval(5, 5);

		assertTrue(HelperFunctions.computeDivisionResultReal(interval1, interval2, expectedResult));
	}

	@Test
	public void TestIntervalDivisionPositive() {
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(1, 10);

		final IntervalDomainValue interval2 = HelperFunctions.createInterval(2, 2);

		final IntervalDomainValue expectedResult = new IntervalDomainValue(new IntervalValue(new BigDecimal("0.5")),
		        new IntervalValue(new BigDecimal(5)));

		assertTrue(HelperFunctions.computeDivisionResultReal(interval1, interval2, expectedResult));
	}
	
	@Test
	public void TestIntervalDivisionNegative() {
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(-10, -1);

		final IntervalDomainValue interval2 = HelperFunctions.createInterval(-2, -2);

		final IntervalDomainValue expectedResult = new IntervalDomainValue(new IntervalValue(new BigDecimal("0.5")),
		        new IntervalValue(new BigDecimal(5)));

		assertTrue(HelperFunctions.computeDivisionResultReal(interval1, interval2, expectedResult));
	}
	
	@Test
	public void TestIntervalDivisionZeroCrossingNominator() {
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(-10, 10);

		final IntervalDomainValue interval2 = HelperFunctions.createInterval(5, 5);

		final IntervalDomainValue expectedResult = HelperFunctions.createInterval(-2, 2);

		assertTrue(HelperFunctions.computeDivisionResultReal(interval1, interval2, expectedResult));
	}
	
	@Test
	public void TestIntervalDivisionZeroCrossingDenominator() {
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(10, 10);

		final IntervalDomainValue interval2 = HelperFunctions.createInterval(-5, 5);

		// Result should be (-\infty; \infty)
		final IntervalDomainValue expectedResult = HelperFunctions.createIntervalTop();

		assertTrue(HelperFunctions.computeDivisionResultReal(interval1, interval2, expectedResult));
	}
	
	@Test
	public void TestIntervalDivisionByZero() {
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(10, 10);

		final IntervalDomainValue interval2 = HelperFunctions.createInterval(0, 0);

		final IntervalDomainValue expectedResult = new IntervalDomainValue(true);

		assertTrue(HelperFunctions.computeDivisionResultReal(interval1, interval2, expectedResult));
	}
	
	@Test
	public void TestIntervalDivisionRegression() {
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(-16, 16);

		final IntervalDomainValue interval2 = HelperFunctions.createInterval(8, 8);

		final IntervalDomainValue expectedResult = HelperFunctions.createInterval(-2, 2);

		assertTrue(HelperFunctions.computeDivisionResultInteger(interval1, interval2, expectedResult));
	}
}
