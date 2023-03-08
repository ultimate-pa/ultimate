package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;


import java.util.ArrayList;
import java.util.HashMap;
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
 * Tests for the function getDecisions(CDD cdd) implemented by me in the Class CDD as part of my bachelors Thesis.
 * @author lena
 */
@RunWith(JUnit4.class)
public class CddUnitTest {
	
	ArrayList<Pair<CDD, HashMap<String, Pair<Decision<?>, int[]>>>> mTestCases;
	
	ArrayList<CDD> mTestCddsTest3;
	ArrayList<Decision<?>> mExpectedTest3;
	CDD mTestCddTest4;
	ArrayList<Decision<?>> mExpectedTest4;
	
	CDD mCDDTest2;
	ArrayList<Pair<Decision<?>, int[]>> mExpected2;
	HashMap<String, Pair<Decision<?>, int[]>> mExpected2HashMap;
	
	public CddUnitTest() {
		mTestCddsTest3 = new ArrayList<CDD>();
		mExpectedTest3 = new ArrayList<Decision<?>>();
		mExpectedTest4 = new ArrayList<Decision<?>>();
		mExpected2 = new ArrayList<Pair<Decision<?>, int[]>>();
		mExpected2HashMap = new HashMap<>();
		createTestCDDsTest3();
		createTestCDDTest4();
		
		
		
		mTestCases = new ArrayList<Pair<CDD, HashMap<String, Pair<Decision<?>, int[]>>>>();
		createTestCase0();
		createTestCase1();
		
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
		CDD c3 = mTestCddsTest3.get(2);
		CDD c4 = mTestCddsTest3.get(3);
 
		mExpectedTest4.add(c1.getDecision());
		mExpectedTest4.add(c2.getDecision());
		
		CDD c5 = RangeDecision.create("c5", RangeDecision.OP_GT, 5);
		CDD c6 = RangeDecision.create("c6", RangeDecision.OP_GT, 5);
		CDD c7 = RangeDecision.create("c7", RangeDecision.OP_GT, 5);
		
		CDD conjunctionGTCdd = c5.and(c7).and(c7);
		
		CDD subCDD1 = c2.and(c1);
		CDD subCDD2 = c3.and(c4);
		
		mTestCddTest4 = subCDD1.or(subCDD2); 
		CDD testCddTest4DNF = mTestCddTest4.toDNF_CDD();
		CDD conjunctions[] = mTestCddTest4.toDNF();
	}
	
	public void createTestCase0() {
		HashMap<String, Pair<Decision<?>, int[]>> expected = new HashMap<String, Pair<Decision<?>, int[]>>();
		
		CDD a = BooleanDecision.create("a");
		int[] trueChildA = {0};
		Pair<Decision<?>, int[]> pairA = new Pair<Decision<?>, int[]>(a.getDecision(), trueChildA);
		expected.put(a.getDecision().getVar(), pairA);
		
		CDD b = BooleanDecision.create("b");
		CDD notb = b.negate();
		int[] trueChildNotB = {1};
		Pair<Decision<?>, int[]> pairNotB = new Pair<Decision<?>, int[]>(notb.getDecision(), trueChildNotB);
		expected.put(notb.getDecision().getVar(), pairNotB);
		
		CDD c5 = RangeDecision.create("c5", RangeDecision.OP_GT, 5);
		int[] trueChildC5 = {1};
		Pair<Decision<?>, int[]> pairC5 = new Pair<Decision<?>, int[]>(c5.getDecision(), trueChildC5);
		expected.put(c5.getDecision().getVar(), pairC5);
		
		CDD c6 = RangeDecision.create("c6", RangeDecision.OP_LT, 5);
		int[] trueChildC6 = {0};
		Pair<Decision<?>, int[]> pairC6 = new Pair<Decision<?>, int[]>(c6.getDecision(), trueChildC6);
		expected.put(c6.getDecision().getVar(), pairC6);
		
		CDD c7 = RangeDecision.create("c7", RangeDecision.OP_EQ, 5);
		int[] trueChildC7 = {1};
		Pair<Decision<?>, int[]> pairC7 = new Pair<Decision<?>, int[]>(c7.getDecision(), trueChildC7);
		expected.put(c7.getDecision().getVar(), pairC7);
		
		CDD c8 = RangeDecision.create("c8", RangeDecision.OP_NEQ, 5);
		int[] trueChildC8 = {0, 2};
		Pair<Decision<?>, int[]> pairC8 = new Pair<Decision<?>, int[]>(c8.getDecision(), trueChildC8);
		expected.put(c8.getDecision().getVar(), pairC8);
		
		CDD testCDD = c8.and(a).and(c6).and(c7).and(notb).and(c5);
		Pair<CDD, HashMap<String, Pair<Decision<?>, int[]>>> testCase = new Pair<>(testCDD, expected);
		mTestCases.add(testCase);
	}
	
	public void createTestCase1() {
		CDD c1 = RangeDecision.create("c1", RangeDecision.OP_LT, 5);
		mExpected2.add(new Pair<Decision<?>, int[]>(c1.getDecision(),new int[] {0}));
		CDD c2 = RangeDecision.create("c2", RangeDecision.OP_GT, 5);
		mExpected2.add(new Pair<Decision<?>, int[]>(c2.getDecision(), new int[] {1}));
		CDD c3 = RangeDecision.create("c3", RangeDecision.OP_EQ, 5);
		mExpected2.add(new Pair<Decision<?>, int[]>(c3.getDecision(), new int[] {1}));
		CDD c4 = RangeDecision.create("c4", RangeDecision.OP_EQ, 5);
		mExpected2.add(new Pair<Decision<?>, int[]>(c4.getDecision(), new int[] {1}));
		CDD c5 = RangeDecision.create("c6", RangeDecision.OP_NEQ, 5);
		mExpected2.add(new Pair<Decision<?>, int[]>(c5.getDecision(), new int[] {0,2}));
		
		mCDDTest2 = c1.and(c5).and(c2).and(c4).and(c3);
		
		for (Pair<Decision<?>, int[]> Pair : mExpected2) {
			mExpected2HashMap.put(Pair.getFirst().getVar(), Pair);
		}
		
		
	}
	
	@Test
	public void getDecisionsConjunctionTest1() {
		ArrayList<Pair<Decision<?>, int[]>> actual = CDD.TRUE.getDecisionsConjunction();
		assertEquals(0, actual.size());
	}
	
	
	@Test
	public void getDecisionConjunctionTest2() {
		ArrayList<Pair<Decision<?>, int[]>> actual = mCDDTest2.getDecisionsConjunction();
		assertEquals(mExpected2.size(), actual.size());
		for (Pair<Decision<?>, int[]> Pair : actual) {
			Pair<Decision<?>, int[]> match = mExpected2HashMap.get(Pair.getFirst().getVar());
			Decision<?> expectedfirst = match.getFirst();
			int[] expectedsecond = match.getSecond();
			Decision<?> actualFirst = Pair.getFirst();
			int[] actualSecond = Pair.getSecond();
			assertEquals(expectedfirst, actualFirst);
			assertEquals(expectedsecond[0], actualSecond[0]);
		}
	}
}
