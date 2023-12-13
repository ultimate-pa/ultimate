package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;

public class RandomCriterionTest<L extends IIcfgTransition<?>> {

	private RandomCriterion<L> criterion;

	@Before
	public void setUp() throws Exception {
		criterion = new RandomCriterion<>(0.5, 321);
	}

	@Test
	public void test() {
		assertEquals(false, criterion.decide(null, null, null));
	}

}
