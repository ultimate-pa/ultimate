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

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Test class for the functions filterCDD() and strict() in the class RangeDecision implemented by me as part of my
 * bachelors Thesis.
 *
 *
 * @author Lena Funk
 */

@RunWith(JUnit4.class)
public class RangeDecisionTest {
	List<Pair<CDD, CDD>> mTestCasesFilterCdd;
	List<Pair<CDD, CDD>> mTestCasesStrict;
	List<Pair<CDD, Boolean>> mTestCasesIsStrict;

	public RangeDecisionTest() {
		mTestCasesFilterCdd = new ArrayList<>();
		mTestCasesStrict = new ArrayList<>();
		mTestCasesIsStrict = new ArrayList<>();
		createTestCasesFilterCdd();
		createTestCasesStrict();
		createTestCasesIsStict();

	}

	public void createTestCasesFilterCdd() {
		// c1 <= 5
		final CDD c1 = RangeDecision.create("c1", RangeDecision.OP_LTEQ, 5);
		// c2 >= 5
		final CDD c2 = RangeDecision.create("c2", RangeDecision.OP_GTEQ, 5);
		// c3 > 5
		final CDD c3 = RangeDecision.create("c3", RangeDecision.OP_GT, 5);
		// c4 < 5
		final CDD c4 = RangeDecision.create("c4", RangeDecision.OP_GT, 5);

		// -----------------------------------------------------------
		// Test 0 (Contains all binary operators
		//
		final CDD conj1 = c1.and(c2).and(c4);
		final CDD conj2 = c1.and(c3).and(c4);
		final CDD testCdd0 = conj1.or(conj2);
		final CDD conj1expected = c1.and(c2);
		final CDD conj2expected = c1;
		final CDD expected0 = conj1expected.or(conj2expected);
		final Pair<CDD, CDD> testCase0 = new Pair<>(testCdd0, expected0);
		mTestCasesFilterCdd.add(testCase0);

		// -----------------------------------------------------------
		// Test 1 (Fringe Case)
		//
		final CDD testCdd1 = CDD.TRUE;
		final CDD expected1 = CDD.TRUE;
		final Pair<CDD, CDD> testCase1 = new Pair<>(testCdd1, expected1);
		mTestCasesFilterCdd.add(testCase1);

		// -----------------------------------------------------------
		// Test 2 (Simple Case)
		//
		final CDD testCdd2 = c1.and(c2);
		final CDD expected2 = c2;
		final Pair<CDD, CDD> testCase2 = new Pair<>(testCdd2, expected2);
		mTestCasesFilterCdd.add(testCase2);

		// -----------------------------------------------------------
		// Test 3 (filter out all)
		//
		final Pair<CDD, CDD> testCase3 = new Pair<>(testCdd0, CDD.TRUE);
		mTestCasesFilterCdd.add(testCase3);
	}

	public void createTestCasesStrict() {
		// -----------------------------------------------------------
		// Test 0 (Contains all binary operators
		//
		// c1 <= 5
		final CDD c1 = RangeDecision.create("c1", RangeDecision.OP_LT, 5);
		// c2 >= 5
		final CDD c2 = RangeDecision.create("c2", RangeDecision.OP_GT, 5);
		// c3 > 5
		final CDD c3 = RangeDecision.create("c3", RangeDecision.OP_GT, 5);
		// c4 < 5
		final CDD c4 = RangeDecision.create("c4", RangeDecision.OP_GT, 5);

		final CDD conj1 = c1.and(c2).and(c4);
		final CDD conj2 = c1.and(c3).and(c4);

		final CDD testCdd = mTestCasesFilterCdd.get(0).getFirst();
		final CDD expected = conj1.or(conj2);

		final Pair<CDD, CDD> testCase = new Pair<>(testCdd, expected);

		mTestCasesStrict.add(testCase);

		// -----------------------------------------------------------
		// Test 1 (Fringe Case) Grenzfälle des FBI
		//
		final CDD testCdd1 = CDD.TRUE;
		final CDD expected1 = CDD.TRUE;
		final Pair<CDD, CDD> testCase1 = new Pair<>(testCdd1, expected1);
		mTestCasesStrict.add(testCase1);

	}

	public void createTestCasesIsStict() {
		// c1 <= 5
		final CDD c1 = RangeDecision.create("c1", RangeDecision.OP_LTEQ, 5);
		// c2 <= 7
		final CDD c2 = RangeDecision.create("c2", RangeDecision.OP_LTEQ, 7);
		// c3 < 5
		final CDD c3 = RangeDecision.create("c3", RangeDecision.OP_LT, 5);
		// c4 < 7
		final CDD c4 = RangeDecision.create("c4", RangeDecision.OP_LT, 7);

		// -----------------------------------------------------------
		// Test 1
		mTestCasesIsStrict.add(new Pair<>(c3, true));

		// -----------------------------------------------------------
		// Test 2
		mTestCasesIsStrict.add(new Pair<>(c1, false));

		c1.and(c2).and(c4);
		c1.and(c3).and(c4);

		final CDD testCdd = mTestCasesFilterCdd.get(0).getFirst();
		mTestCasesIsStrict.add(new Pair<>(testCdd, true));

	}

	/**
	 * Test 0 (Contains all binary operators#
	 *
	 * TestCdd (DNF): (c1 && c2 && c4) || (c1 && c3 && c4) reset = ["c3", "c4"] expected: (c1 && c2) || (c1) = c1
	 */
	@Test
	public void filterCDDTest0() {
		final Pair<CDD, CDD> testCase = mTestCasesFilterCdd.get(0);
		final String[] reset = { "c3", "c4" };
		final CDD testCDD = testCase.getFirst();
		final CDD expected = testCase.getSecond();
		final CDD actual = RangeDecision.filterCdd(testCDD, reset);
		assertTrue(actual.equals(expected));
	}

	/**
	 * Test 1 (Fringe Case)
	 *
	 * TestCDD: TRUE reset: ["c3", "c4"]
	 */
	@Test
	public void filterCDDTest1() {
		final Pair<CDD, CDD> testCase = mTestCasesFilterCdd.get(1);
		final String[] reset = { "c3", "c4" };
		final CDD testCDD = testCase.getFirst();
		final CDD expected = testCase.getSecond();
		final CDD actual = RangeDecision.filterCdd(testCDD, reset);
		assertTrue(actual.equals(expected));
	}

	/**
	 * Test 2 (Simple Case)
	 *
	 * TestCDD (DNF): c1 && c2 reset = ["c1"] expected: c2
	 */
	@Test
	public void filterCDDTest2() {
		final Pair<CDD, CDD> testCase = mTestCasesFilterCdd.get(2);
		final String[] reset = { "c1" };
		final CDD testCDD = testCase.getFirst();
		final CDD expected = testCase.getSecond();
		final CDD actual = RangeDecision.filterCdd(testCDD, reset);
		assertTrue(actual.equals(expected));
	}

	/**
	 * Test 3 (reset is all variables)
	 *
	 * TestCdd (DNF): (c1 && c2 && c4) || (c1 && c3 && c4) reset = ["c1", "c2", "c3", "c4"] expected: TRUE
	 */
	@Test
	public void filterCDDTest3() {
		final Pair<CDD, CDD> testCase = mTestCasesFilterCdd.get(3);
		final String[] reset = { "c1", "c2", "c3", "c4" };
		final CDD testCDD = testCase.getFirst();
		final CDD expected = testCase.getSecond();
		final CDD actual = RangeDecision.filterCdd(testCDD, reset);
		assertTrue(actual.equals(expected));

	}

	/**
	 * Test 0 (Contains all binary operators)
	 *
	 * TestCdd (DNF): (c1 <= 5 && c2 >= 5 && c4 < 5) || (c1 <= 5 && c3 > 5 && c4 < 5) expected: (c1 < 5 && c2 > 5 && c4
	 * < 5) || (c1 < 5 && c3 > 5 && c4 < 5)
	 */
	@Test
	public void strictTest0() {
		final Pair<CDD, CDD> testCase = mTestCasesStrict.get(0);
		final CDD testCDD = testCase.getFirst();
		final CDD expected = testCase.getSecond();
		final CDD actual = RangeDecision.strict(testCDD);
		assertTrue(actual.equals(expected));
	}

	/**
	 * Test 1 (Fringe Case)
	 *
	 * TestCDD: TRUE expected: TRUE
	 */
	@Test
	public void strictTest1() {
		final Pair<CDD, CDD> testCase = mTestCasesFilterCdd.get(1);
		final CDD testCDD = testCase.getFirst();
		final CDD expected = testCase.getSecond();
		final CDD actual = RangeDecision.strict(testCDD);
		assertTrue(actual.equals(expected));
	}

	@Test
	public void isStrictTest0() {
		final Pair<CDD, Boolean> testCase = mTestCasesIsStrict.get(0);
		final CDD testCdd = testCase.getFirst();
		final Boolean expected = testCase.getSecond();
		final Boolean actual = RangeDecision.isStrictLess(testCdd);
		assertTrue(actual.equals(expected));
	}

	@Test
	public void isStrictTest1() {
		final Pair<CDD, Boolean> testCase = mTestCasesIsStrict.get(1);
		final CDD testCdd = testCase.getFirst();
		final Boolean expected = testCase.getSecond();
		final Boolean actual = RangeDecision.isStrictLess(testCdd);
		assertTrue(actual.equals(expected));
	}

	@Test
	public void isStrictTest2() {
		final Pair<CDD, Boolean> testCase = mTestCasesIsStrict.get(2);
		final CDD testCdd = testCase.getFirst();
		final Boolean expected = testCase.getSecond();
		final Boolean actual = RangeDecision.isStrictLess(testCdd);
		assertTrue(actual.equals(expected));
	}

}
