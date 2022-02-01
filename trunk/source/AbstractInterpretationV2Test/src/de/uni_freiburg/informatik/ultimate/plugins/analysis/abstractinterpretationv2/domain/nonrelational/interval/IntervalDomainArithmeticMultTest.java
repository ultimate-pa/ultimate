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

import org.junit.Test;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class IntervalDomainArithmeticMultTest {

	@Test
	public void testIntervalPositiveMult() {
		
		// Interval [10, 20]
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(10, 20);
		
		// Interval [10, 10]
		final IntervalDomainValue interval2 = HelperFunctions.createInterval(10, 10);
		
		// Expected Interval [100, 200]
		final IntervalDomainValue expectedResult = HelperFunctions.createInterval(100, 200);
		
		assertTrue(HelperFunctions.computeMultiplicationResult(interval1, interval2, expectedResult));
	}
	
	@Test
	public void testIntervalNegativeMult() {
		// Interval [1, 5]
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(1, 5);
		
		// Interval [-5, -1]
		final IntervalDomainValue interval2 = HelperFunctions.createInterval(-5, -1);
		
		// Expected Interval [-25, -1]
		final IntervalDomainValue expectedResult = HelperFunctions.createInterval(-25, -1);
		
		assertTrue(HelperFunctions.computeMultiplicationResult(interval1, interval2, expectedResult));
	}
	
	@Test
	public void testIntervalZero() {
		// Interval [1, 5]
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(1, 5);
		
		// Interval [0, 0]
		final IntervalDomainValue interval2 = HelperFunctions.createInterval(0, 0);
		
		// Expected Interval [0, 0]
		final IntervalDomainValue expectedResult = HelperFunctions.createInterval(0, 0);
		
		assertTrue(HelperFunctions.computeMultiplicationResult(interval1, interval2, expectedResult));
	}
	
	@Test
	public void testInfiniteIntervalMult() {
		// Interval [-\infty, \infty]
		final IntervalDomainValue interval1 = HelperFunctions.createIntervalTop();
		
		// Interval [-\infty, \infty]
		final IntervalDomainValue interval2 = HelperFunctions.createIntervalTop();
		
		// Expected Interval [-\infty, \infty]
		final IntervalDomainValue expectedResult = HelperFunctions.createIntervalTop();
		
		assertTrue(HelperFunctions.computeMultiplicationResult(interval1, interval2, expectedResult));
		
		
		// Interval [-\infty, \infty]
		final IntervalDomainValue interval3 = HelperFunctions.createIntervalTop();
		
		// Interval [0, 0]
		final IntervalDomainValue interval4 = HelperFunctions.createInterval(0, 0);
		
		// Expected Interval [0, 0]
		final IntervalDomainValue expectedResult2 = HelperFunctions.createInterval(0,0);
		
		assertTrue(HelperFunctions.computeMultiplicationResult(interval3, interval4, expectedResult2));
		
		// Interval [10,20]
		final IntervalDomainValue interval5 = HelperFunctions.createInterval(10, 20);
		
		// Expected Interval [-\infty, \infty]
		assertTrue(HelperFunctions.computeMultiplicationResult(interval1, interval5, expectedResult));
	}
	
	@Test
	public void testNegInfiniteIntervalMult() {
		// Interval [-\infty, -1]
		final IntervalDomainValue interval1 = new IntervalDomainValue(new IntervalValue(), new IntervalValue(-1));
		
		//Interval [1, 1]
		final IntervalDomainValue interval2 = HelperFunctions.createInterval(1, 1);
		
		// Expected: [-\infty, -1]
		final IntervalDomainValue expected = new IntervalDomainValue(new IntervalValue(), new IntervalValue(-1));
		
		assertTrue(HelperFunctions.computeMultiplicationResult(interval1, interval2, expected));
		
		// Interval [-2, -1]
		final IntervalDomainValue interval3 = HelperFunctions.createInterval(-2, -1);
		
		// Expected: [1, \infty]
		final IntervalDomainValue expected2 = new IntervalDomainValue(new IntervalValue(1), new IntervalValue());
		
		assertTrue(HelperFunctions.computeMultiplicationResult(interval1, interval3, expected2));
		
	}
}
