package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.BoundedInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.IInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.JoiningInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public class InterferenceMergerTest {

	private static InterferenceAbstraction createSet(final Map<String, Set<IPredicate>> map) {
		return InterferenceAbstraction.of(map);
	}

	@Test
	public void identityMergerPassesThrough() {
		final IPredicate p1 = MockPredicate.of("p1");
		final IPredicate p2 = MockPredicate.of("p2");
		final IPredicate q1 = MockPredicate.of("q1");

		final Map<String, Set<IPredicate>> input = new HashMap<>();
		input.put("thread1", Set.of(p1, p2));
		input.put("thread2", Set.of(q1));

		final var merger = IInterferenceMerger.identity();
		final InterferenceAbstraction result = merger.merge(createSet(input), null);

		// Identity merger should preserve the mapping
		assertEquals(Set.of(p1, p2), result.getInterferencesProducedBy("thread1"));
		assertEquals(Set.of(q1), result.getInterferencesProducedBy("thread2"));
	}

	@Test
	public void joiningMergerMergesPerThread() {
		final IPredicate p1 = MockPredicate.of("p1");
		final IPredicate p2 = MockPredicate.of("p2");
		final IPredicate q1 = MockPredicate.of("q1");

		final Map<String, Set<IPredicate>> input = new HashMap<>();
		input.put("thread1", Set.of(p1, p2));
		input.put("thread2", Set.of(q1));

		// Use a mock domain that tracks joins
		final var domain = new JoinTrackingMockDomain();
		final var merger = new JoiningInterferenceMerger(false);
		final InterferenceAbstraction result = merger.merge(createSet(input), domain);

		// thread1's p1 and p2 should have been joined into one
		assertEquals(1, result.getInterferencesProducedBy("thread1").size());
		assertTrue("p1 and p2 should have been joined", domain.wasJoined(p1, p2));

		// thread2's q1 remains as is (only one interference, no join needed)
		assertEquals(1, result.getInterferencesProducedBy("thread2").size());
		assertTrue(result.getInterferencesProducedBy("thread2").contains(q1));
	}

	@Test
	public void joiningMergerWithSingleInterferencePerThread() {
		final IPredicate p1 = MockPredicate.of("p1");
		final IPredicate q1 = MockPredicate.of("q1");

		final Map<String, Set<IPredicate>> input = new HashMap<>();
		input.put("thread1", Set.of(p1));
		input.put("thread2", Set.of(q1));

		final var domain = new JoinTrackingMockDomain();
		final var merger = new JoiningInterferenceMerger(false);
		final InterferenceAbstraction result = merger.merge(createSet(input), domain);

		// No joins should have occurred (only one interference per thread)
		assertEquals(0, domain.getJoinCount());

		// Each thread keeps its own interference
		assertEquals(Set.of(p1), result.getInterferencesProducedBy("thread1"));
		assertEquals(Set.of(q1), result.getInterferencesProducedBy("thread2"));
	}

	@Test
	public void boundedMergerUnderLimitPassesThrough() {
		final IPredicate p1 = MockPredicate.of("p1");
		final IPredicate p2 = MockPredicate.of("p2");
		final IPredicate q1 = MockPredicate.of("q1");

		final Map<String, Set<IPredicate>> input = new HashMap<>();
		input.put("thread1", Set.of(p1, p2));
		input.put("thread2", Set.of(q1));

		// Max 10 per thread - we're under that
		final var merger = new BoundedInterferenceMerger(10, false);
		final InterferenceAbstraction result = merger.merge(createSet(input), new JoinTrackingMockDomain());

		// All interferences preserved (under limit)
		assertEquals(Set.of(p1, p2), result.getInterferencesProducedBy("thread1"));
		assertEquals(Set.of(q1), result.getInterferencesProducedBy("thread2"));
	}

	@Test
	public void boundedMergerMergesWhenOverLimit() {
		// Create 6 interferences for thread1
		final Set<IPredicate> thread1Itfs = new HashSet<>();
		for (int i = 0; i < 6; i++) {
			thread1Itfs.add(MockPredicate.of("p" + i));
		}

		final Map<String, Set<IPredicate>> input = new HashMap<>();
		input.put("thread1", thread1Itfs);
		input.put("thread2", Set.of());

		// Max 2 per thread - 6 interferences should become 2
		final var domain = new JoinTrackingMockDomain();
		final var merger = new BoundedInterferenceMerger(2, false);
		final InterferenceAbstraction result = merger.merge(createSet(input), domain);

		// thread1 should have exactly 2 merged interferences
		assertEquals(2, result.getInterferencesProducedBy("thread1").size());
		// Joins should have occurred
		assertTrue(domain.getJoinCount() >= 2);
	}

	private static class JoinTrackingMockDomain implements IDomain {
		private final Map<IPredicate, IPredicate> mJoinPairs = new HashMap<>();
		private int mJoinCount = 0;

		@Override
		public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
			mJoinPairs.put(lhs, rhs);
			mJoinCount++;
			return MockPredicate.of("joined(" + lhs + "," + rhs + ")");
		}

		@Override
		public IPredicate widen(final IPredicate old, final IPredicate widenWith) {
			return MockPredicate.of("widened");
		}

		@Override
		public ResultForAlteredInputs isEqBottom(final IPredicate pred) {
			return new ResultForAlteredInputs(pred, null, false, false);
		}

		@Override
		public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
			return new ResultForAlteredInputs(subset, superset, false, false);
		}

		@Override
		public IPredicate alpha(final IPredicate pred) {
			return pred;
		}

		public boolean wasJoined(final IPredicate a, final IPredicate b) {
			return (mJoinPairs.containsKey(a) && mJoinPairs.get(a) == b)
					|| (mJoinPairs.containsKey(b) && mJoinPairs.get(b) == a);
		}

		public int getJoinCount() {
			return mJoinCount;
		}
	}
}
