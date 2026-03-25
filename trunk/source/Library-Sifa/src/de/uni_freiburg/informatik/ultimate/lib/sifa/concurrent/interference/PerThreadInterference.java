package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public class PerThreadInterference implements IInterference {

	private final GuardedPredicate mPredicate;
	private final IInterferenceApplicator mApplicator;

	public PerThreadInterference(final GuardedPredicate predicate, final IInterferenceApplicator applicator) {
		mPredicate = predicate;
		mApplicator = applicator;
	}

	@Override
	public Collection<IPredicate> getPredicates() {
		return List.of(mPredicate.effect());
	}

	@Override
	public boolean isTrivial() {
		return SmtUtils.isFalseLiteral(mPredicate.effect().getFormula());
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PerThreadInterference otherFlat)) {
			return false;
		}
		if (!domain.isSubsetEq(mPredicate.effect(), otherFlat.mPredicate.effect()).isTrueForAbstraction()) {
			return false;
		}
		// Guard subsumption: new guard must be subsumed by old guard
		if (mPredicate.hasGuard() && otherFlat.mPredicate.hasGuard()) {
			return domain.isSubsetEq(mPredicate.guard(), otherFlat.mPredicate.guard()).isTrueForAbstraction();
		}
		return true;
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PerThreadInterference otherFlat)) {
			throw new IllegalArgumentException(
					"Cannot widen PerThreadInterference with " + other.getClass().getSimpleName());
		}
		return new PerThreadInterference(
				InterferenceUtils.widenGuardedPredicate(mPredicate, otherFlat.mPredicate, domain), mApplicator);
	}

	@Override
	public int size() {
		return 1;
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain, final int wideningThreshold,
			final SifaStats stats) {
		if (isTrivial()) {
			return state;
		}
		return mApplicator.apply(state, List.of(mPredicate), domain, wideningThreshold, stats);
	}
}
