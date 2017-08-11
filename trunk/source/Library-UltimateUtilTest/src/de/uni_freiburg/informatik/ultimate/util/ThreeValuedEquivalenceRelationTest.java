package de.uni_freiburg.informatik.ultimate.util;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.util.datastructures.Equality;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;

public class ThreeValuedEquivalenceRelationTest {

	@Test
	public void test1() {
		final ThreeValuedEquivalenceRelation<String> tver1 = new ThreeValuedEquivalenceRelation<>();
		
		tver1.reportEquality("x", "y");

		assertFalse(tver1.containsContradiction());
		
		assertTrue(tver1.getEquality("x", "x") == Equality.EQUAL);

		assertTrue(tver1.getEquality("x", "y") == Equality.EQUAL);
		assertTrue(tver1.getEquality("y", "x") == Equality.EQUAL);
		
		tver1.reportNotEquals("x", "z");

		assertFalse(tver1.containsContradiction());

		assertTrue(tver1.getEquality("x", "z") == Equality.NOT_EQUAL);
		assertTrue(tver1.getEquality("z", "x") == Equality.NOT_EQUAL);
		assertTrue(tver1.getEquality("y", "z") == Equality.NOT_EQUAL);
		assertTrue(tver1.getEquality("z", "y") == Equality.NOT_EQUAL);
		
		
	
		tver1.reportEquality("a", "b");

		assertTrue(tver1.getEquality("a", "x") == Equality.UNKNOWN);
		
		tver1.reportNotEquals("i", "j");
		
		
		assertTrue(tver1.getEquality("a", "i") == Equality.UNKNOWN);
		assertTrue(tver1.getEquality("x", "i") == Equality.UNKNOWN);
		
		tver1.reportEquality("y", "z");
		
		assertTrue(tver1.containsContradiction());
	
		
	}
}
