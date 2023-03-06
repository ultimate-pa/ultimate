package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.HashSet;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;

/**
 * TODO: Moved the main method from CDD to this class; make unit tests from it.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 * Tests for the function getDecisions(CDD cdd) implemented by me in the Class CDD as part of my bachelors Thesis.
 * @author lena
 */
@RunWith(JUnit4.class)
public class CddTest {
	
	ArrayList<CDD> mTestCddsTest3;
	ArrayList<Decision<?>> mExpectedTest3;
	CDD mTestCddTest4;
	ArrayList<Decision<?>> mExpectedTest4;
	
	public CddTest() {
		mTestCddsTest3 = new ArrayList<CDD>();
		mExpectedTest3 = new ArrayList<Decision<?>>();
		mExpectedTest4 = new ArrayList<Decision<?>>();
		createTestCDDsTest3();
		createTestCDDTest4();
		
	}
	
	public void createTestCDDsTest3() {
		// c1 <= 5
		CDD c1 = RangeDecision.create("c1", RangeDecision.OP_LTEQ, 5);
		mTestCddsTest3.add(c1);
		mExpectedTest3.add(c1.getDecision());
		
		// c2 >= 5
		CDD c2 = RangeDecision.create("c2", RangeDecision.OP_GTEQ, 5);
		mTestCddsTest3.add(c2);
		mExpectedTest3.add(c2.getDecision());
		
		// c3 < 5
		CDD c3 = RangeDecision.create("c3", RangeDecision.OP_LT, 5);
		mTestCddsTest3.add(c3);
		mExpectedTest3.add(c3.getDecision());
		
		// c4 > 5
		CDD c4 = RangeDecision.create("c4", RangeDecision.OP_GT, 5);
		mTestCddsTest3.add(c4);
		mExpectedTest3.add(c4.getDecision());
	}
	
	public void createTestCDDTest4() {
		CDD a = BooleanDecision.create("a");
		CDD b = BooleanDecision.create("b");
		
		mExpectedTest4.add(a.getDecision());
		mExpectedTest4.add(b.getDecision());
		
		CDD c1 = mTestCddsTest3.get(0);
		CDD c2 = mTestCddsTest3.get(1);
 
		mExpectedTest4.add(c1.getDecision());
		mExpectedTest4.add(c2.getDecision());
		
		CDD subCDD1 = a.and(c1);
		CDD subCDD2 = b.negate().or(c2);
		
		mTestCddTest4 = subCDD1.and(subCDD2); 
	}

	/**
	 * Test von Daniel
	 */
//	@Test
//	public static void main(final String[] args) {
//		final CDD a = BooleanDecision.create("a");
//		final CDD b = BooleanDecision.create("b");
//		final CDD c = BooleanDecision.create("c");
//		final CDD d = BooleanDecision.create("d");
//
//		// CDD main = ((a.and(b)).and(c.or(d))).or(e).or(f.negate());
//		// CDD main2 = ((a.and(b)).or(a.negate().and(b.negate())));
//		// CDD main = main2.or(c.and(d));
//		// CDD main = c.or(main2);
//
//		// CDD teil1 = a.negate().and(b).and(c);
//		// CDD teil2 = a.and(b);
//		// CDD main = teil1.or(teil2);
//
//		// CDD links = a.negate().or(b.or(c));
//		// CDD rechts = a.or(b);
//		// CDD main = links.and(rechts);
//		// CDD links = a.negate().and(b.and(c));
//		// CDD rechts = a.and(d);
//		// CDD main = links.or(rechts);
//		final CDD links = a.negate().and(b);
//		final CDD rechts = a.and(b.or(c)).and(d);
//		final CDD main = links.or(rechts);
//
//		final CDD test = a.negate();
//		final CDD test2 = a.or(b);
//
//		System.out.println("********************************* CDD ********************************* ");
//		System.out.println(main.toString());
//		System.out.println(main.toTexString());
//		testIsAtomic(test);
//		testIsAtomic(test2);
//		testIsAtomic(links);
//		testIsAtomic(main);
//		testIsAtomic(a);
//
//		final CDD[] dnf = main.toDNF();
//		System.out.println("********************************* DNF ********************************* ");
//
//		for (int i = 0; i < dnf.length; i++) {
//			System.out.println("*** Conjunctive term " + i + ": ");
//			System.out.println(dnf[i].toString());
//		}
//
//		final CDD[] cnf = main.toCNF();
//		System.out.println("********************************* CNF ********************************* ");
//
//		for (int i = 0; i < cnf.length; i++) {
//			System.out.println("*** Disjunctive term " + i + ": ");
//			System.out.println(cnf[i].toString());
//		}
//
//		System.out.println("*********************************************************************** ");
//	}
//
//	private static void testIsAtomic(final CDD cdd) {
//		System.out.println("The formula " + cdd.toString() + " is atomic: " + cdd.isAtomic());
//	}
	
	/**
	 * Test fringe case 1: 
	 * 		CDD.TRUE
	 */
	@Test
	public void getDecisionsTest1() {
		HashSet<Decision<?>> actual = CDD.TRUE.getDecisions();
		assertEquals(0, actual.size());
	}
	
	/**
	 * Test fringe case 1: 
	 * 		CDD.FALSE 
	 */
	@Test
	public void getDecisionsTest2() {
		HashSet<Decision<?>> actual = CDD.FALSE.getDecisions();
		assertEquals(0, actual.size());
	}
	
	/**
	 * Test "normal" case: 
	 * 		Disjunction of mixed RangeDecisions, no EQ or NEQ:
	 * 		c1 <= 5 || c2 >= 5 || c3 < 5 || c4 > 5
	 * 		
	 */
	@Test
	public void getDecisionsTest3() {
		CDD disjunction = CDD.FALSE;
		ArrayList<Decision<?>> expected = new ArrayList<>();
		for (CDD cdd : mTestCddsTest3) {
			expected.add(cdd.getDecision());
			disjunction = disjunction.or(cdd);
		}
		HashSet<Decision<?>> actual = disjunction.getDecisions();
		assertEquals(expected.size(), actual.size());
		assertTrue(actual.contains(expected.get(0)));
		assertTrue(actual.contains(expected.get(1)));
		assertTrue(actual.contains(expected.get(2)));
		assertTrue(actual.contains(expected.get(3)));
	}
	
	/**
	 * Test "mixed" case: 
	 * 
	 */
	@Test
	public void getDecisionsTest4() {
		HashSet<Decision<?>> actual = mTestCddTest4.getDecisions();
		assertEquals(mExpectedTest4.size(), actual.size());
		for (Decision<?> decision : mExpectedTest4) {
			Boolean result = actual.contains(decision); 
			assertTrue(result);
		}
		
	}
}
