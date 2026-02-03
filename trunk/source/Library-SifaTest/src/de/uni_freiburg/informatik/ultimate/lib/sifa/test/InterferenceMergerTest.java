package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.IInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.JoiningInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public class InterferenceMergerTest {

	@Test
	public void identityMergerPassesThrough() {
		final IPredicate p1 = MockPredicate.of("p1");
		final IPredicate p2 = MockPredicate.of("p2");

		final Set<IPredicate> input = Set.of(p1, p2);

		final var merger = IInterferenceMerger.identity();
		final Set<IPredicate> result = merger.merge(input, null);

		assertEquals(Set.of(p1, p2), result);
	}

	@Test
	public void joiningMergerJoinsAll() {
		final IPredicate p1 = MockPredicate.of("p1");
		final IPredicate p2 = MockPredicate.of("p2");

		final Set<IPredicate> input = Set.of(p1, p2);

		final var domain = new JoinTrackingMockDomain();
		final var merger = new JoiningInterferenceMerger(false);
		final Set<IPredicate> result = merger.merge(input, domain);

		// p1 and p2 should have been joined into one
		assertEquals(1, result.size());
		assertTrue("p1 and p2 should have been joined", domain.wasJoined(p1, p2));
	}

	@Test
	public void joiningMergerWithSingleInterference() {
		final IPredicate p1 = MockPredicate.of("p1");

		final Set<IPredicate> input = Set.of(p1);

		final var domain = new JoinTrackingMockDomain();
		final var merger = new JoiningInterferenceMerger(false);
		final Set<IPredicate> result = merger.merge(input, domain);

		// No joins should have occurred (only one interference)
		assertEquals(0, domain.getJoinCount());
		assertEquals(Set.of(p1), result);
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
