package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.fixpoint.SubsumptionConvergenceCheck;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain.ResultForAlteredInputs;

/**
 * Tests for convergence strategies.
 */
public class SubsumptionConvergenceTest {

	// Helper to create an interference set
	private static InterferenceAbstraction createSet(final Map<String, Set<IPredicate>> map) {
		return InterferenceAbstraction.of(map);
	}

	@Test
	public void convergedWhenNewSubsumedByOld() {
		final IPredicate pNew = MockPredicate.of("pNew");
		final IPredicate pOld = MockPredicate.of("pOld");

		final InterferenceAbstraction newInterferences = createSet(Map.of("thread1", Set.of(pNew)));
		final InterferenceAbstraction oldInterferences = createSet(Map.of("thread1", Set.of(pOld)));

		// pNew is subsumed by pOld
		final var domain = new SubsumptionMockDomain(Map.of(pNew, Set.of(pOld)));

		final var strategy = new SubsumptionConvergenceCheck();
		assertTrue(strategy.hasConverged(newInterferences, oldInterferences, domain));
	}

	@Test
	public void notConvergedWhenNewNotSubsumed() {
		final IPredicate pNew = MockPredicate.of("pNew");
		final IPredicate pOld = MockPredicate.of("pOld");

		final InterferenceAbstraction newInterferences = createSet(Map.of("thread1", Set.of(pNew)));
		final InterferenceAbstraction oldInterferences = createSet(Map.of("thread1", Set.of(pOld)));

		// pNew is NOT subsumed by pOld
		final var domain = new SubsumptionMockDomain(Map.of());

		final var strategy = new SubsumptionConvergenceCheck();
		assertFalse(strategy.hasConverged(newInterferences, oldInterferences, domain));
	}

	@Test
	public void convergedWhenBothEmpty() {
		final InterferenceAbstraction newInterferences = createSet(Map.of("thread1", Set.of()));
		final InterferenceAbstraction oldInterferences = createSet(Map.of("thread1", Set.of()));

		final var strategy = new SubsumptionConvergenceCheck();
		assertTrue(strategy.hasConverged(newInterferences, oldInterferences, new SubsumptionMockDomain(Map.of())));
	}

	@Test
	public void convergedWithEmptyNewInterferences() {
		final IPredicate pOld = MockPredicate.of("pOld");

		final InterferenceAbstraction newInterferences = createSet(Map.of("thread1", Set.of()));
		final InterferenceAbstraction oldInterferences = createSet(Map.of("thread1", Set.of(pOld)));

		final var strategy = new SubsumptionConvergenceCheck();
		// Empty new set is trivially subsumed
		assertTrue(strategy.hasConverged(newInterferences, oldInterferences, new SubsumptionMockDomain(Map.of())));
	}

	@Test
	public void notConvergedWhenOldIsEmpty() {
		final IPredicate pNew = MockPredicate.of("pNew");

		final InterferenceAbstraction newInterferences = createSet(Map.of("thread1", Set.of(pNew)));
		final InterferenceAbstraction oldInterferences = createSet(Map.of("thread1", Set.of()));

		final var strategy = new SubsumptionConvergenceCheck();
		// New interference with nothing to subsume it
		assertFalse(strategy.hasConverged(newInterferences, oldInterferences, new SubsumptionMockDomain(Map.of())));
	}

	@Test
	public void multipleThreadsAllMustConverge() {
		final IPredicate p1 = MockPredicate.of("p1");
		final IPredicate p2 = MockPredicate.of("p2");
		final IPredicate oldP1 = MockPredicate.of("oldP1");
		final IPredicate oldP2 = MockPredicate.of("oldP2");

		final Map<String, Set<IPredicate>> newMap = new HashMap<>();
		newMap.put("thread1", Set.of(p1));
		newMap.put("thread2", Set.of(p2));

		final Map<String, Set<IPredicate>> oldMap = new HashMap<>();
		oldMap.put("thread1", Set.of(oldP1));
		oldMap.put("thread2", Set.of(oldP2));

		final InterferenceAbstraction newInterferences = createSet(newMap);
		final InterferenceAbstraction oldInterferences = createSet(oldMap);

		// Only p1 is subsumed, p2 is not
		final var domain = new SubsumptionMockDomain(Map.of(p1, Set.of(oldP1)));

		final var strategy = new SubsumptionConvergenceCheck();
		assertFalse(strategy.hasConverged(newInterferences, oldInterferences, domain));
	}

	@Test
	public void multipleThreadsConvergedWhenAllSubsumed() {
		final IPredicate p1 = MockPredicate.of("p1");
		final IPredicate p2 = MockPredicate.of("p2");
		final IPredicate oldP1 = MockPredicate.of("oldP1");
		final IPredicate oldP2 = MockPredicate.of("oldP2");

		final Map<String, Set<IPredicate>> newMap = new HashMap<>();
		newMap.put("thread1", Set.of(p1));
		newMap.put("thread2", Set.of(p2));

		final Map<String, Set<IPredicate>> oldMap = new HashMap<>();
		oldMap.put("thread1", Set.of(oldP1));
		oldMap.put("thread2", Set.of(oldP2));

		final InterferenceAbstraction newInterferences = createSet(newMap);
		final InterferenceAbstraction oldInterferences = createSet(oldMap);

		// Both p1 and p2 are subsumed
		final var subsumptions = new HashMap<IPredicate, Set<IPredicate>>();
		subsumptions.put(p1, Set.of(oldP1));
		subsumptions.put(p2, Set.of(oldP2));
		final var domain = new SubsumptionMockDomain(subsumptions);

		final var strategy = new SubsumptionConvergenceCheck();
		assertTrue(strategy.hasConverged(newInterferences, oldInterferences, domain));
	}

	@Test
	public void subsumedByAnyInSet() {
		final IPredicate pNew = MockPredicate.of("pNew");
		final IPredicate old1 = MockPredicate.of("old1");
		final IPredicate old2 = MockPredicate.of("old2");

		final InterferenceAbstraction newInterferences = createSet(Map.of("thread1", Set.of(pNew)));
		final Set<IPredicate> oldSet = new HashSet<>();
		oldSet.add(old1);
		oldSet.add(old2);
		final InterferenceAbstraction oldInterferences = createSet(Map.of("thread1", oldSet));

		// pNew is subsumed by old2 (but not old1)
		final var domain = new SubsumptionMockDomain(Map.of(pNew, Set.of(old2)));

		final var strategy = new SubsumptionConvergenceCheck();
		assertTrue(strategy.hasConverged(newInterferences, oldInterferences, domain));
	}

	/**
	 * Mock domain that returns configured subsumption results.
	 */
	private static class SubsumptionMockDomain implements IDomain {
		private final Map<IPredicate, Set<IPredicate>> mSubsumptions;

		/**
		 * @param subsumptions
		 *            Map from predicate A to set of predicates that subsume A (i.e., A ⊆ B for each B in set)
		 */
		public SubsumptionMockDomain(final Map<IPredicate, Set<IPredicate>> subsumptions) {
			mSubsumptions = subsumptions;
		}

		@Override
		public ResultForAlteredInputs isSubsetEq(final IPredicate subset, final IPredicate superset) {
			final Set<IPredicate> subsumers = mSubsumptions.get(subset);
			final boolean isSubsumed = subsumers != null && subsumers.contains(superset);
			return new ResultForAlteredInputs(subset, superset, isSubsumed, false);
		}

		@Override
		public IPredicate join(final IPredicate lhs, final IPredicate rhs) {
			return MockPredicate.of("joined");
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
		public IPredicate alpha(final IPredicate pred) {
			return pred;
		}
	}
}
