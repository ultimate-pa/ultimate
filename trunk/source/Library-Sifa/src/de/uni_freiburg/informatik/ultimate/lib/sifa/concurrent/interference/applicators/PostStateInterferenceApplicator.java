package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.applicators;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GuardedPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceApplicator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

public final class PostStateInterferenceApplicator implements IInterferenceApplicator {

	@Override
	public IPredicate apply(final IPredicate state, final Collection<GuardedPredicate> predicates, final IDomain domain,
			final int wideningThreshold, final SifaStats stats) {
		return InterferenceUtils.applyUntilFixpoint(state, predicates, domain, wideningThreshold, stats,
				(frontier, predicate) -> predicate.effect());
	}
}
