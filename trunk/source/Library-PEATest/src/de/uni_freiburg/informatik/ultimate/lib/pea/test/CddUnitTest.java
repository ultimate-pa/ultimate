package de.uni_freiburg.informatik.ultimate.lib.pea.test;

import static org.junit.Assert.assertEquals;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

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

	ArrayList<Pair<CDD, HashMap<String, Pair<Decision<?>, int[]>>>> mTestCases;

	public CddUnitTest() {
		mTestCases = new ArrayList<Pair<CDD, HashMap<String, Pair<Decision<?>, int[]>>>>();
		createTestCase0();

	}

	public void createTestCase0() {
		HashMap<String, Pair<Decision<?>, int[]>> expected = new HashMap<String, Pair<Decision<?>, int[]>>();

		CDD a = BooleanDecision.create("a");
		int[] trueChildA = { 0 };
		Pair<Decision<?>, int[]> pairA = new Pair<Decision<?>, int[]>(a.getDecision(), trueChildA);
		expected.put(a.getDecision().getVar(), pairA);

		CDD b = BooleanDecision.create("b");
		CDD notb = b.negate();
		int[] trueChildNotB = { 1 };
		Pair<Decision<?>, int[]> pairNotB = new Pair<Decision<?>, int[]>(notb.getDecision(), trueChildNotB);
		expected.put(notb.getDecision().getVar(), pairNotB);

		CDD c5 = RangeDecision.create("c5", RangeDecision.OP_GT, 5);
		int[] trueChildC5 = { 1 };
		Pair<Decision<?>, int[]> pairC5 = new Pair<Decision<?>, int[]>(c5.getDecision(), trueChildC5);
		expected.put(c5.getDecision().getVar(), pairC5);

		CDD c6 = RangeDecision.create("c6", RangeDecision.OP_LT, 5);
		int[] trueChildC6 = { 0 };
		Pair<Decision<?>, int[]> pairC6 = new Pair<Decision<?>, int[]>(c6.getDecision(), trueChildC6);
		expected.put(c6.getDecision().getVar(), pairC6);

		CDD c7 = RangeDecision.create("c7", RangeDecision.OP_EQ, 5);
		int[] trueChildC7 = { 1 };
		Pair<Decision<?>, int[]> pairC7 = new Pair<Decision<?>, int[]>(c7.getDecision(), trueChildC7);
		expected.put(c7.getDecision().getVar(), pairC7);

		CDD c8 = RangeDecision.create("c8", RangeDecision.OP_NEQ, 5);
		int[] trueChildC8 = { 0, 2 };
		Pair<Decision<?>, int[]> pairC8 = new Pair<Decision<?>, int[]>(c8.getDecision(), trueChildC8);
		expected.put(c8.getDecision().getVar(), pairC8);

		CDD testCDD = c8.and(a).and(c6).and(c7).and(notb).and(c5);
		Pair<CDD, HashMap<String, Pair<Decision<?>, int[]>>> testCase = new Pair<>(testCDD, expected);
		mTestCases.add(testCase);
	}

	@Test
	/***
	 * TestCDD: a && !b && c5 >= 5 && c6 <= 5 && c7 == 5 && c8 != 5 expected: [(a, [0]) (b, [1]), (c5, [1]), (c6, [0]),
	 * (c7, [1]), (c8, [0, 2])]
	 * 
	 */
	public void getDecisionConjunctionTest0() {
		Pair<CDD, HashMap<String, Pair<Decision<?>, int[]>>> testCase = mTestCases.get(0);
		CDD testCDD = testCase.getFirst();
		HashMap<String, Pair<Decision<?>, int[]>> expected = testCase.getSecond();
		List<Pair<Decision<?>, int[]>> actual = testCDD.getDecisionsConjunction();
		assertEquals(expected.size(), actual.size());
		for (Pair<Decision<?>, int[]> Pair : actual) {
			Pair<Decision<?>, int[]> match = expected.get(Pair.getFirst().getVar());
			Decision<?> expectedfirst = match.getFirst();
			int[] expectedsecond = match.getSecond();
			Decision<?> actualFirst = Pair.getFirst();
			int[] actualSecond = Pair.getSecond();
			assertEquals(expectedfirst, actualFirst);
			assertEquals(expectedsecond[0], actualSecond[0]);
		}
	}

	@Test
	public void getDecisionsConjunctionTest1() {
		List<Pair<Decision<?>, int[]>> actual = CDD.TRUE.getDecisionsConjunction();
		assertEquals(0, actual.size());
	}

}
