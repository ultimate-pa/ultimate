package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.transformers.IInterferenceTransformer;

public class InterferenceTransformerTest {

	@Test
	public void identityReturnsInputUnchanged() {
		final IPredicate p = MockPredicate.of("p");
		assertSame(p, IInterferenceTransformer.identity().transformPredicate(p));
	}

	@Test
	public void transformAppliedToAllInterferences() {
		final Map<String, Set<IPredicate>> input = new HashMap<>();
		input.put("thread1", Set.of(MockPredicate.of("p1"), MockPredicate.of("p2")));
		input.put("thread2", Set.of(MockPredicate.of("q1")));

		final IInterferenceTransformer transformer = pred -> MockPredicate.of("t(" + pred + ")");
		final InterferenceAbstraction result = transformer.transform(InterferenceAbstraction.of(input));

		assertEquals(2, result.getInterferencesProducedBy("thread1").size());
		assertEquals(1, result.getInterferencesProducedBy("thread2").size());

		for (final IPredicate p : result.getInterferencesProducedBy("thread2")) {
			assertEquals("t(q1)", p.toString());
		}
	}
}
