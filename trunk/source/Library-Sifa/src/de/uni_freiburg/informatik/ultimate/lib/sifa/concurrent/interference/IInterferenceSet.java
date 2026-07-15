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
}
