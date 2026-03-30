package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

/** Strongest-post via QE in a local fixpoint loop. */
public final class RelationalQeInterferenceApplicator implements IInterferenceApplicator {

	private final RelationalPredicatePostcondition mPostcondition;

	public RelationalQeInterferenceApplicator(final RelationalPredicatePostcondition postcondition) {
		mPostcondition = postcondition;
	}

	@Override
	public IPredicate apply(final IPredicate state, final Collection<GuardedPredicate> predicates, final IDomain domain,
			final int wideningThreshold, final SifaStats stats) {
		final var effects = predicates.stream().map(GuardedPredicate::effect).toList();
		return InterferenceUtils.applyUntilFixpoint(state,
				InterferenceUtils.prepareNonFalseRelations(effects, mPostcondition), domain, mPostcondition,
				wideningThreshold, stats);
	}
}
