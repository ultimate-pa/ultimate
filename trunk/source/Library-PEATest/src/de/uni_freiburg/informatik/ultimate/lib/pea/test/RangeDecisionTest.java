package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Test class for the functions filterCDD() and strict() in the class RangeDecision 
 * implemented by me as part of my bachelors Thesis.
 * 
 * TODO: test strict()
 *
 * @author Lena Funk
 */

@RunWith(JUnit4.class)
public class RangeDecisionTest {
	ArrayList<Pair<CDD, CDD>> mTestCasesFilterCdd;
	ArrayList<Pair<CDD, CDD>> mTestCasesStrict;
	
	public RangeDecisionTest() {
		mTestCasesFilterCdd = new ArrayList<Pair<CDD, CDD>>();
		mTestCasesStrict = new ArrayList<Pair<CDD, CDD>>();
		createTestCasesFilterCdd();
		createTestCasesStrict();
		
	}
	
	public void createTestCasesFilterCdd() {
		// c1 <= 5
		CDD c1 = RangeDecision.create("c1", RangeDecision.OP_LTEQ, 5);
		// c2 >= 5
		CDD c2 = RangeDecision.create("c2", RangeDecision.OP_GTEQ, 5);
		// c3 > 5
		CDD c3 = RangeDecision.create("c3", RangeDecision.OP_GT, 5);
		// c4 < 5
		CDD c4 = RangeDecision.create("c4", RangeDecision.OP_GT, 5);
		
		//-----------------------------------------------------------
		// Test 0 (Contains all binary operators
		//
		CDD conj1 = (c1.and(c2)).and(c4);
		CDD conj2 = (c1.and(c3)).and(c4);
		CDD testCdd0 = conj1.or(conj2);
		CDD conj1expected = c1.and(c2);
		CDD conj2expected = c1;
		CDD expected0 = conj1expected.or(conj2expected);
		Pair<CDD, CDD> testCase0 = new Pair<CDD, CDD>(testCdd0, expected0);
		mTestCasesFilterCdd.add(testCase0);
		
		//-----------------------------------------------------------
		// Test 1 (Fringe Case)
		//
		CDD testCdd1 = CDD.TRUE;
		CDD expected1 = CDD.TRUE;
		Pair<CDD, CDD> testCase1 = new Pair<CDD, CDD>(testCdd1, expected1);
		mTestCasesFilterCdd.add(testCase1);
		
		//-----------------------------------------------------------
		// Test 2 (Simple Case)
		// 
		CDD testCdd2 = c1.and(c2);
		CDD expected2 = c2;
		Pair<CDD, CDD> testCase2 = new Pair<CDD, CDD>(testCdd2, expected2);
		mTestCasesFilterCdd.add(testCase2);
		
		//-----------------------------------------------------------
		// Test 3 (filter out all)
		// 
		Pair<CDD, CDD> testCase3 = new Pair<CDD, CDD>(testCdd0, CDD.TRUE);
		mTestCasesFilterCdd.add(testCase3);
	}
	
	public void createTestCasesStrict() {
		//-----------------------------------------------------------
		// Test 0 (Contains all binary operators
		//
		// c1 <= 5
		CDD c1 = RangeDecision.create("c1", RangeDecision.OP_LT, 5);
		// c2 >= 5
		CDD c2 = RangeDecision.create("c2", RangeDecision.OP_GT, 5);
		// c3 > 5
		CDD c3 = RangeDecision.create("c3", RangeDecision.OP_GT, 5);
		// c4 < 5
		CDD c4 = RangeDecision.create("c4", RangeDecision.OP_GT, 5);
		
		CDD conj1 = (c1.and(c2)).and(c4);
		CDD conj2 = (c1.and(c3)).and(c4);
		
		CDD testCdd = mTestCasesFilterCdd.get(0).getFirst();
		CDD expected = conj1.or(conj2);
		
		Pair<CDD, CDD> testCase = new Pair<CDD, CDD>(testCdd, expected);
		
		mTestCasesStrict.add(testCase);
		
		//-----------------------------------------------------------
		// Test 1 (Fringe Case) Grenzfälle des FBI
		//
		CDD testCdd1 = CDD.TRUE;
		CDD expected1 = CDD.TRUE;
		Pair<CDD, CDD> testCase1 = new Pair<CDD, CDD>(testCdd1, expected1);
		mTestCasesStrict.add(testCase1);
		
	}
	
	
	/**
	 * Test 0 (Contains all binary operators#
	 * 
	 * TestCdd (DNF): (c1 && c2 && c4) || (c1 && c3 && c4)
	 * reset = ["c3", "c4"]
	 * expected: (c1 && c2) || (c1) = c1
	 */
	@Test
	public void filterCDDTest0() {
		Pair<CDD, CDD> testCase = mTestCasesFilterCdd.get(0);
		String[] reset = {"c3", "c4"};
		CDD testCDD = testCase.getFirst();
		CDD expected = testCase.getSecond();
		CDD actual = RangeDecision.filterCdd(testCDD, reset);
		assertTrue(actual.equals(expected));
	}
	
	/**
	 * Test 1 (Fringe Case)
	 * 
	 * TestCDD: TRUE
	 * reset: ["c3", "c4"]
	 */
	@Test
	public void filterCDDTest1() {
		Pair<CDD, CDD> testCase = mTestCasesFilterCdd.get(1);
		String[] reset = {"c3", "c4"};
		CDD testCDD = testCase.getFirst();
		CDD expected = testCase.getSecond();
		CDD actual = RangeDecision.filterCdd(testCDD, reset);
		assertTrue(actual.equals(expected));
	}
	/**
	 *  Test 2 (Simple Case)
	 *  
	 *  TestCDD (DNF): c1 && c2
	 *  reset = ["c1"]
	 *  expected: c2
	 */
	@Test
	public void filterCDDTest2() {
		Pair<CDD, CDD> testCase = mTestCasesFilterCdd.get(2);
		String[] reset = {"c1"};
		CDD testCDD = testCase.getFirst();
		CDD expected = testCase.getSecond();
		CDD actual = RangeDecision.filterCdd(testCDD, reset);
		assertTrue(actual.equals(expected));
	}
	
	/**
	 * Test 3 (reset is all variables)
	 * 
	 * TestCdd (DNF): (c1 && c2 && c4) || (c1 && c3 && c4)
	 * reset = ["c1", "c2", "c3", "c4"]
	 * expected: TRUE
	 */
	@Test
	public void filterCDDTest3() {
		Pair<CDD, CDD> testCase = mTestCasesFilterCdd.get(3);
		String[] reset = {"c1", "c2", "c3", "c4" };
		CDD testCDD = testCase.getFirst();
		CDD expected = testCase.getSecond();
		CDD actual = RangeDecision.filterCdd(testCDD, reset);
		assertTrue(actual.equals(expected));
		
	}
	
	/**
	 * Test 0 (Contains all binary operators#
	 * 
	 * TestCdd (DNF):  (c1 <= 5 && c2 >= 5 && c4 < 5) || (c1 <= 5 && c3 > 5 && c4 < 5)
	 * expected: (c1 < 5 && c2 > 5 && c4 < 5) || (c1 < 5 && c3 > 5 && c4 < 5)
	 */
	@Test
	public void strictTest0() {
		Pair<CDD, CDD> testCase = mTestCasesStrict.get(0);
		CDD testCDD = testCase.getFirst();
		CDD expected = testCase.getSecond();
		CDD actual = RangeDecision.strict(testCDD);
		assertTrue(actual.equals(expected));
	}
	/**
	 * Test 1 (Fringe Case)
	 * 
	 * TestCDD: TRUE
	 * expected: TRUE
	 */
	@Test
	public void strictTest1() {
		Pair<CDD, CDD> testCase = mTestCasesFilterCdd.get(1);
		CDD testCDD = testCase.getFirst();
		CDD expected = testCase.getSecond();
		CDD actual = RangeDecision.strict(testCDD);
		assertTrue(actual.equals(expected));
	}
	
}
