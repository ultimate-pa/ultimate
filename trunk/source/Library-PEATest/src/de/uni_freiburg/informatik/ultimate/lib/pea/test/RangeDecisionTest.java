package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import java.util.ArrayList;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;

/**
 * Test class for the functions filterCDD() and strict() in the class RangeDecision 
 * implemented by me as part of my bachelors Thesis.
 *
 * @author Lena Funk
 */

@RunWith(JUnit4.class)
public class RangeDecisionTest {
	ArrayList<CDD> mTestCdds;
	
	public RangeDecisionTest() {
		createTestCDDs();
		
	}
	
	public void createTestCDDs() {
		// c1 <= 5
		CDD c1 = RangeDecision.create("c1", RangeDecision.OP_LTEQ, 5);
		mTestCdds.add(c1);
		RangeDecision decision = (RangeDecision) c1.getDecision();
		
		
		// c2 >= 5
		CDD c2 = RangeDecision.create("c2", RangeDecision.OP_GTEQ, 5);
		mTestCdds.add(c2);
	}	
	
	
	/**
	 * Test case 1: LTEQ
	 */
	@Test
	public void getDecisionsTest1() {
		CDD c1 = mTestCdds.get(0);
		Decision<?> expected = c1.getDecision();
	}
	
	/**
	 * Test extreme case 1: 
	 */
	@Test
	public void getDecisionsTest2() {
		
	}
	
	/**
	 * Test "normal" case: 
	 */
	@Test
	public void getDecisionsTest3() {
		
	}
	
	/**
	 * Test "crazy" case: 
	 */
	@Test
	public void removeConstraintTest4() {
		
	}

}
