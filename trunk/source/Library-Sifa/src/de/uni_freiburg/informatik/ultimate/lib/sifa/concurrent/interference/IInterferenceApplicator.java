package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

@FunctionalInterface
public interface IInterferenceApplicator {
	IPredicate apply(IPredicate state, Collection<GuardedPredicate> predicates, IDomain domain, int wideningThreshold,
			SifaStats stats);
}
