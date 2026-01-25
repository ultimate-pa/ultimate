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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.BoundedInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.IInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.JoiningInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain.ResultForAlteredInputs;

/**
 * Tests for interference mergers.
 */
public class InterferenceMergerTest {

	// Helper to create an interference set
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
	public void basicInterferenceSetGetOtherThreads() {
		final IPredicate p1 = MockPredicate.of("p1");
		final IPredicate p2 = MockPredicate.of("p2");
		final IPredicate q1 = MockPredicate.of("q1");

		final Map<String, Set<IPredicate>> input = new HashMap<>();
		input.put("thread1", Set.of(p1, p2));
		input.put("thread2", Set.of(q1));

		final InterferenceAbstraction set = InterferenceAbstraction.of(input);

		// thread1 should get interferences from thread2
		assertEquals(Set.of(q1), set.getInterferencesForOtherThreads("thread1"));
		// thread2 should get interferences from thread1
		assertEquals(Set.of(p1, p2), set.getInterferencesForOtherThreads("thread2"));
	}

	@Test
	public void basicInterferenceSetWithThreeThreads() {
		final IPredicate p1 = MockPredicate.of("p1");
		final IPredicate q1 = MockPredicate.of("q1");
		final IPredicate r1 = MockPredicate.of("r1");

		final Map<String, Set<IPredicate>> input = new HashMap<>();
		input.put("A", Set.of(p1));
		input.put("B", Set.of(q1));
		input.put("C", Set.of(r1));

		final InterferenceAbstraction set = InterferenceAbstraction.of(input);

		// Each thread gets interferences from both other threads
		assertEquals(Set.of(q1, r1), set.getInterferencesForOtherThreads("A"));
		assertEquals(Set.of(p1, r1), set.getInterferencesForOtherThreads("B"));
		assertEquals(Set.of(p1, q1), set.getInterferencesForOtherThreads("C"));
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
		final var merger = new JoiningInterferenceMerger(false); // no alpha
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

	/**
	 * Mock domain that tracks join operations.
	 */
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

	// ==================== BoundedInterferenceMerger tests ====================

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

	@Test
	public void boundedMergerWithMaxOne() {
		final IPredicate p1 = MockPredicate.of("p1");
		final IPredicate p2 = MockPredicate.of("p2");
		final IPredicate p3 = MockPredicate.of("p3");

		final Map<String, Set<IPredicate>> input = new HashMap<>();
		input.put("thread1", Set.of(p1, p2, p3));
		input.put("thread2", Set.of());

		// Max 1 - all interferences merged into one
		final var domain = new JoinTrackingMockDomain();
		final var merger = new BoundedInterferenceMerger(1, false);
		final InterferenceAbstraction result = merger.merge(createSet(input), domain);

		// thread1 should have exactly 1 merged interference
		assertEquals(1, result.getInterferencesProducedBy("thread1").size());
	}

	@Test
	public void boundedMergerEvenDistribution() {
		// Create 10 interferences
		final Set<IPredicate> interferences = new HashSet<>();
		for (int i = 0; i < 10; i++) {
			interferences.add(MockPredicate.of("p" + i));
		}

		final Map<String, Set<IPredicate>> input = new HashMap<>();
		input.put("thread1", interferences);
		input.put("thread2", Set.of());

		// Max 5 - should create 5 buckets of 2 items each
		final var domain = new JoinTrackingMockDomain();
		final var merger = new BoundedInterferenceMerger(5, false);
		final InterferenceAbstraction result = merger.merge(createSet(input), domain);

		// thread1 should have exactly 5 merged interferences
		assertEquals(5, result.getInterferencesProducedBy("thread1").size());
		// Each bucket has 2 items, so 1 join per bucket = 5 joins
		assertEquals(5, domain.getJoinCount());
	}

	@Test
	public void boundedMergerEmptyInput() {
		final Map<String, Set<IPredicate>> input = new HashMap<>();
		input.put("thread1", Set.of());
		input.put("thread2", Set.of());

		final var merger = new BoundedInterferenceMerger(5, false);
		final InterferenceAbstraction result = merger.merge(createSet(input), new JoinTrackingMockDomain());

		assertTrue(result.getInterferencesProducedBy("thread1").isEmpty());
		assertTrue(result.getInterferencesProducedBy("thread2").isEmpty());
	}
}
