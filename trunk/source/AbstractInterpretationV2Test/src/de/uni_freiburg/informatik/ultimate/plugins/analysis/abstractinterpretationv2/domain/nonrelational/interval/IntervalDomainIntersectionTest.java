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
public class IntervalDomainIntersectionTest {

	@Test
	public void testIntervalIntersectionIncluded() {
		// Interval: [10, 20]
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(10, 20);

		// Interval: [13, 15]
		final IntervalDomainValue interval2 = HelperFunctions.createInterval(13, 15);

		// Expected: [13, 15]
		assertTrue(HelperFunctions.computeIntersectionResult(interval1, interval2, interval2));

		assertTrue(HelperFunctions.computeIntersectionResult(interval2, interval1, interval2));
	}

	@Test
	public void testIntervalIntersectionHalfOutsideUp() {
		// Interval: [10, 20]
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(10, 20);

		// Interval: [15, 30]
		final IntervalDomainValue interval2 = HelperFunctions.createInterval(15, 30);

		// Expected: [15, 20]
		final IntervalDomainValue expected = HelperFunctions.createInterval(15, 20);

		assertTrue(HelperFunctions.computeIntersectionResult(interval1, interval2, expected));
		assertTrue(HelperFunctions.computeIntersectionResult(interval2, interval1, expected));
	}

	@Test
	public void testIntervalIntersectionHalfOutsideDown() {
		// Interval: [10, 20]
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(10, 20);

		// Interval: [5, 15]
		final IntervalDomainValue interval2 = HelperFunctions.createInterval(5, 15);

		// Expected: [15, 20]
		final IntervalDomainValue expected = HelperFunctions.createInterval(10, 15);

		assertTrue(HelperFunctions.computeIntersectionResult(interval1, interval2, expected));
		assertTrue(HelperFunctions.computeIntersectionResult(interval2, interval1, expected));
	}

	@Test
	public void testIntervalIntersectionDisjoint() {
		// Interval: [10, 20]
		final IntervalDomainValue interval1 = HelperFunctions.createInterval(10, 20);

		// Interval: [30, 40]
		final IntervalDomainValue interval2 = HelperFunctions.createInterval(30, 40);

		// Expected: \bot
		final IntervalDomainValue expected = HelperFunctions.createIntervalBottom();

		assertTrue(HelperFunctions.computeIntersectionResult(interval1, interval2, expected));
		assertTrue(HelperFunctions.computeIntersectionResult(interval2, interval1, expected));
	}

	@Test
	public void testInfiniteIntervalIntersection() {
		// Interval: (-\infty, \infty)
		final IntervalDomainValue interval1 = new IntervalDomainValue();

		// Interval: [1, 1]
		final IntervalDomainValue oneone = HelperFunctions.createInterval(1, 1);

		// Expected: [1, 1]
		assertTrue(HelperFunctions.computeIntersectionResult(interval1, oneone, oneone));
		assertTrue(HelperFunctions.computeIntersectionResult(oneone, interval1, oneone));

		// Interval: [-10, \infty)
		final IntervalDomainValue interval2 =
				new IntervalDomainValue(new IntervalValue(new BigDecimal(-10)), new IntervalValue());

		// Expected: [1, 1]
		assertTrue(HelperFunctions.computeIntersectionResult(interval2, oneone, oneone));
		assertTrue(HelperFunctions.computeIntersectionResult(oneone, interval2, oneone));
	}
}
