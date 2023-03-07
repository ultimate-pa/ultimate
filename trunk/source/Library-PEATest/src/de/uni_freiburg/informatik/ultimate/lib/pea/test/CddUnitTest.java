package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.util.SimplePair;

/** 
 * Tests for the function getDecisions(CDD cdd) implemented by me in the Class CDD as part of my bachelors Thesis.
 * @author lena
 */
@RunWith(JUnit4.class)
public class CddUnitTest {
	
	ArrayList<CDD> mTestCddsTest3;
	ArrayList<Decision<?>> mExpectedTest3;
	CDD mTestCddTest4;
	ArrayList<Decision<?>> mExpectedTest4;
	
	CDD mCDDTest2;
	ArrayList<SimplePair<Decision<?>, Integer>> mExpected2;
	HashMap<String, SimplePair<Decision<?>, Integer>> mExpected2HashMap;
	
	public CddUnitTest() {
		mTestCddsTest3 = new ArrayList<CDD>();
		mExpectedTest3 = new ArrayList<Decision<?>>();
		mExpectedTest4 = new ArrayList<Decision<?>>();
		mExpected2 = new ArrayList<SimplePair<Decision<?>, Integer>>();
		mExpected2HashMap = new HashMap<>();
		createTestCDDsTest3();
		createTestCDDTest4();
		createTestCDD1();
		
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
	
	public void createTestCDD1() {
		CDD a = BooleanDecision.create("a");
		mExpected2.add(new SimplePair<Decision<?>, Integer>(a.getDecision(), 0));
		CDD b = BooleanDecision.create("b");
		CDD notb = b.negate();
		mExpected2.add(new SimplePair<Decision<?>, Integer>(notb.getDecision(), 1));
		CDD c5 = RangeDecision.create("c5", RangeDecision.OP_GT, 5);
		mExpected2.add(new SimplePair<Decision<?>, Integer>(c5.getDecision(), 1));
		CDD c6 = RangeDecision.create("c6", RangeDecision.OP_GT, 5);
		mExpected2.add(new SimplePair<Decision<?>, Integer>(c6.getDecision(), 1));
		
		mCDDTest2 = a.and(c6).and(notb).and(c5);
		
		for (SimplePair<Decision<?>, Integer> simplePair : mExpected2) {
			mExpected2HashMap.put(simplePair.getFirst().getVar(), simplePair);
		}
		
		
	}
	
	@Test
	public void getDecisionsConjunctionTest1() {
		ArrayList<SimplePair<Decision<?>, Integer>> actual = CDD.TRUE.getDecisionsConjunction();
		assertEquals(0, actual.size());
	}
	
	
	@Test
	public void getDecisionConjunctionTest2() {
		ArrayList<SimplePair<Decision<?>, Integer>> actual = mCDDTest2.getDecisionsConjunction();
		assertEquals(mExpected2.size(), actual.size());
		for (SimplePair<Decision<?>, Integer> simplePair : actual) {
			SimplePair<Decision<?>, Integer> match = mExpected2HashMap.get(simplePair.getFirst().getVar());
			assertTrue(simplePair.equals(match));
		}
	}
}
