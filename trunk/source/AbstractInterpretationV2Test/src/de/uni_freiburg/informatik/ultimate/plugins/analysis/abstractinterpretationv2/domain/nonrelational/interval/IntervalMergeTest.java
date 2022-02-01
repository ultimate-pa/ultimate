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
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public class IntervalMergeTest {

	@Test
	public void testIntervalMergePoint() {
		// [0; 0]
		final IntervalDomainValue int1 = HelperFunctions.createInterval(0, 0);

		// [1; 1]
		final IntervalDomainValue int2 = HelperFunctions.createInterval(1, 1);

		// Expected: [0; 1]
		final IntervalDomainValue exp1 = HelperFunctions.createInterval(0, 1);

		assertTrue(HelperFunctions.computeMergedInterval(int1, int2, exp1));
	}

	@Test
	public void testIntervalMergeClosed() {
		// [0; 1]
		final IntervalDomainValue int1 = HelperFunctions.createInterval(0, 0);

		// [0; 10]
		final IntervalDomainValue int2 = HelperFunctions.createInterval(0, 10);

		// Expected: [0; 10]
		final IntervalDomainValue exp1 = HelperFunctions.createInterval(0, 10);

		assertTrue(HelperFunctions.computeMergedInterval(int1, int2, exp1));
	}

	@Test
	public void testIntervalMergeNegativeClosed() {
		// [-5; -1]
		final IntervalDomainValue int1 = HelperFunctions.createInterval(-5, -1);

		// [-3; 0]
		final IntervalDomainValue int2 = HelperFunctions.createInterval(-3, 0);

		// Expected: [-5; 0]
		final IntervalDomainValue exp1 = HelperFunctions.createInterval(-5, 0);

		assertTrue(HelperFunctions.computeMergedInterval(int1, int2, exp1));
	}

	@Test
	public void testIntervalMergeOpen() {
		// [10; \infty]
		final IntervalDomainValue int1 = new IntervalDomainValue(new IntervalValue(BigDecimal.TEN), new IntervalValue());

		// [1; 10]
		final IntervalDomainValue int2 = HelperFunctions.createInterval(1, 10);

		// Expected: [1; \infty]
		final IntervalDomainValue exp1 = new IntervalDomainValue(new IntervalValue(BigDecimal.ONE), new IntervalValue());

		assertTrue(HelperFunctions.computeMergedInterval(int1, int2, exp1));
	}

	@Test
	public void testIntervalMergeOpenNegative() {
		// [-\infty; -10]
		final IntervalDomainValue int1 = new IntervalDomainValue(new IntervalValue(), new IntervalValue(new BigDecimal(-10)));

		// [-3; -1]
		final IntervalDomainValue int2 = HelperFunctions.createInterval(-3, -1);

		// Expected: [-\infty; -1]
		final IntervalDomainValue exp1 = new IntervalDomainValue(new IntervalValue(), new IntervalValue(new BigDecimal(-1)));

		assertTrue(HelperFunctions.computeMergedInterval(int1, int2, exp1));
	}
}
