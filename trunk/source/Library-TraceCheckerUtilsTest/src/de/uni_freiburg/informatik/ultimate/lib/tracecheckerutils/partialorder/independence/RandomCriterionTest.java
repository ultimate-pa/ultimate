package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import static org.junit.Assert.assertEquals;

import org.junit.Before;
import org.junit.Test;

public class RandomCriterionTest<L, S> {

	private RandomCriterion<L, S> criterion;

	@Before
	public void setUp() throws Exception {
		criterion = new RandomCriterion<>(0.5, 321);
	}

	@Test
	public void test() {
		assertEquals(false, criterion.decide(null, null, null));
	}

}
