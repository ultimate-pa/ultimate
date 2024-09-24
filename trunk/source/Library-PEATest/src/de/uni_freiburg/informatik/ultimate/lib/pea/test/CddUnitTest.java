/*
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE ReqParser plug-in.
 *
 * The ULTIMATE ReqParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ReqParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReqParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReqParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ReqParer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Tests for the function getDecisionsConjunction(CDD cdd) implemented by me in the Class CDD as part of my bachelors
 * thesis.
 *
 * @author lena
 */
@RunWith(JUnit4.class)
public class CddUnitTest {

	List<Pair<CDD, Map<String, Pair<Decision<?>, int[]>>>> mTestCases;

	public CddUnitTest() {
		mTestCases = new ArrayList<>();
		createTestCase0();

	}

	public void createTestCase0() {
		final Map<String, Pair<Decision<?>, int[]>> expected = new HashMap<>();

		final CDD a = BooleanDecision.create("a");
		final int[] trueChildA = { 0 };
		final Pair<Decision<?>, int[]> pairA = new Pair<>(a.getDecision(), trueChildA);
		expected.put(a.getDecision().getVar(), pairA);

		final CDD b = BooleanDecision.create("b");
		final CDD notb = b.negate();
		final int[] trueChildNotB = { 1 };
		final Pair<Decision<?>, int[]> pairNotB = new Pair<>(notb.getDecision(), trueChildNotB);
		expected.put(notb.getDecision().getVar(), pairNotB);

		final CDD c5 = RangeDecision.create("c5", RangeDecision.OP_GT, 5);
		final int[] trueChildC5 = { 1 };
		final Pair<Decision<?>, int[]> pairC5 = new Pair<>(c5.getDecision(), trueChildC5);
		expected.put(c5.getDecision().getVar(), pairC5);

		final CDD c6 = RangeDecision.create("c6", RangeDecision.OP_LT, 5);
		final int[] trueChildC6 = { 0 };
		final Pair<Decision<?>, int[]> pairC6 = new Pair<>(c6.getDecision(), trueChildC6);
		expected.put(c6.getDecision().getVar(), pairC6);

		final CDD c7 = RangeDecision.create("c7", RangeDecision.OP_EQ, 5);
		final int[] trueChildC7 = { 1 };
		final Pair<Decision<?>, int[]> pairC7 = new Pair<>(c7.getDecision(), trueChildC7);
		expected.put(c7.getDecision().getVar(), pairC7);

		final CDD c8 = RangeDecision.create("c8", RangeDecision.OP_NEQ, 5);
		final int[] trueChildC8 = { 0, 2 };
		final Pair<Decision<?>, int[]> pairC8 = new Pair<>(c8.getDecision(), trueChildC8);
		expected.put(c8.getDecision().getVar(), pairC8);

		final CDD testCDD = c8.and(a).and(c6).and(c7).and(notb).and(c5);
		final Pair<CDD, Map<String, Pair<Decision<?>, int[]>>> testCase = new Pair<>(testCDD, expected);
		mTestCases.add(testCase);
	}

	@Test
	/***
	 * TestCDD: a && !b && c5 >= 5 && c6 <= 5 && c7 == 5 && c8 != 5 expected: [(a, [0]) (b, [1]), (c5, [1]), (c6, [0]),
	 * (c7, [1]), (c8, [0, 2])]
	 *
	 */
	public void getDecisionConjunctionTest0() {
		final Pair<CDD, Map<String, Pair<Decision<?>, int[]>>> testCase = mTestCases.get(0);
		final CDD testCDD = testCase.getFirst();
		final Map<String, Pair<Decision<?>, int[]>> expected = testCase.getSecond();
		final List<Pair<Decision<?>, int[]>> actual = testCDD.getDecisionsConjunction();
		assertEquals(expected.size(), actual.size());
		for (final Pair<Decision<?>, int[]> Pair : actual) {
			final Pair<Decision<?>, int[]> match = expected.get(Pair.getFirst().getVar());
			final Decision<?> expectedfirst = match.getFirst();
			final int[] expectedsecond = match.getSecond();
			final Decision<?> actualFirst = Pair.getFirst();
			final int[] actualSecond = Pair.getSecond();
			assertEquals(expectedfirst, actualFirst);
			assertEquals(expectedsecond[0], actualSecond[0]);
		}
	}

	@Test
	public void getDecisionsConjunctionTest1() {
		final List<Pair<Decision<?>, int[]>> actual = CDD.TRUE.getDecisionsConjunction();
		assertEquals(0, actual.size());
	}

}
