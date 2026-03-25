package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

/**
 * Strategy for applying interference predicates to an analysis state. Decouples the application mechanism from the
 * interference grouping (per-thread, per-edge, per-abstract-location).
 */
@FunctionalInterface
public interface IInterferenceApplicator {
	/**
	 * Apply the given interference predicates to the state, returning the (possibly widened) result.
	 *
	 * @param state
	 *            current analysis state
	 * @param predicates
	 *            guarded interference predicates to apply. For non-guarded modes the guard is null.
	 * @param domain
	 *            abstract domain for join/widen/subset operations
	 * @param wideningThreshold
	 *            number of iterations before widening kicks in
	 * @param stats
	 *            statistics collector
	 * @return the state after interference application
	 */
	IPredicate apply(IPredicate state, Collection<GuardedPredicate> predicates, IDomain domain, int wideningThreshold,
			SifaStats stats);
}
