package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.SimplePair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Test class for the functions filterCDD() and strict() in the class RangeDecision 
 * implemented by me as part of my bachelors Thesis.
 *
 * @author Lena Funk
 */

@RunWith(JUnit4.class)
public class RangeDecisionTest {
	ArrayList<SimplePair<CDD, CDD>> mTestCases;
	
	public RangeDecisionTest() {
		mTestCases = new ArrayList<SimplePair<CDD, CDD>>();
		createTestCases();
		
	}
	
	public void createTestCases() {
		// c1 <= 5
		CDD c1 = RangeDecision.create("c1", RangeDecision.OP_LTEQ, 5);
		// c2 >= 5
		CDD c2 = RangeDecision.create("c2", RangeDecision.OP_GTEQ, 5);
		// c3 > 5
		CDD c3 = RangeDecision.create("c3", RangeDecision.OP_GT, 5);
		// c4 < 5
		CDD c4 = RangeDecision.create("c4", RangeDecision.OP_GT, 5);
		
		//-----------------------------------------------------------
		// Test 0
		//
		// c1 <= 5 && (c2 >= 5 || c3 > 5) && c4 < 5
		// DNF: (c1 && c2 && c4) || (c1 && c3 && c4)
		// reset = ["c3", "c4"]
		// after reset: c1 <= 5 && (c2 >= 5 || FALSE) && TRUE = c1 <= 5 && c2 >= 5 
		//
		CDD conj1 = (c1.and(c2)).and(c4);
		CDD conj2 = (c1.and(c3)).and(c4);
		CDD testCdd0 = conj1.and(conj2);
		CDD conj1expected = c1.and(c2);
		CDD conj2expected = c1;
		CDD expected0 = conj1expected.and(conj2expected);
		SimplePair<CDD, CDD> testCase0 = new SimplePair<CDD, CDD>(testCdd0, expected0);
		mTestCases.add(testCase0);
		
		//-----------------------------------------------------------
		// Test 1
		//
		CDD testCdd1 = CDD.TRUE;
		CDD expected1 = CDD.TRUE;
		SimplePair<CDD, CDD> testCase1 = new SimplePair<CDD, CDD>(testCdd1, expected1);
		mTestCases.add(testCase1);
		
		//-----------------------------------------------------------
		// Test 2
		//
		// reset = ["c1"]
		CDD testCdd2 = c1.and(c2);
		CDD expected2 = c2;
		SimplePair<CDD, CDD> testCase2 = new SimplePair<CDD, CDD>(testCdd2, expected2);
		mTestCases.add(testCase2);
	}	
	
	
	/**
	 * Test case 0
	 */
	@Test
	public void getDecisionsTest0() {
		SimplePair<CDD, CDD> testCase = mTestCases.get(0);
		String[] reset = {"c3", "c4"};
		CDD testCDD = testCase.getFirst();
		CDD expected = testCase.getSecond();
		CDD actual = RangeDecision.filterCdd(testCDD, reset);
		assertTrue(actual.equals(expected));
	}
	
	@Test
	public void getDecisionsTest1() {
		SimplePair<CDD, CDD> testCase = mTestCases.get(1);
		String[] reset = {"c3", "c4"};
		CDD testCDD = testCase.getFirst();
		CDD expected = testCase.getSecond();
		CDD actual = RangeDecision.filterCdd(testCDD, reset);
		assertTrue(actual.equals(expected));
	}
	
	@Test
	public void getDecisionsTest2() {
		SimplePair<CDD, CDD> testCase = mTestCases.get(2);
		String[] reset = {"c1"};
		CDD testCDD = testCase.getFirst();
		CDD expected = testCase.getSecond();
		CDD actual = RangeDecision.filterCdd(testCDD, reset);
		assertTrue(actual.equals(expected));
	}
	
}
