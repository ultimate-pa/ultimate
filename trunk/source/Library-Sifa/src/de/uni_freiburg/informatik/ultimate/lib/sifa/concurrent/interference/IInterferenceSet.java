package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

public interface IInterferenceSet {

	IPredicate applyUntilFixpoint(IPredicate state, String observerThreadId, Set<String> activeThreadIds,
			Set<String> observerLockset, IDomain domain, int wideningThreshold, SifaStats stats);

	boolean isEmpty();

	int summaryCount();

	Set<String> threadIds();

	IInterferenceSet widen(IInterferenceSet other, IDomain domain);

	boolean isSubsumedBy(IInterferenceSet other, IDomain domain);

	/**
	 * Like {@link #isSubsumedBy}, but restricted to summaries whose writer thread is in relevantThreadIds.
	 * Used to decide whether a single observer thread's interference input grew since the previous outer round.
	 * The default conservatively checks full subsumption, which implies the restricted one.
	 */
	default boolean isSubsumedByForThreads(final IInterferenceSet other, final IDomain domain,
			final Set<String> relevantThreadIds) {
		return isSubsumedBy(other, domain);
	}
}
