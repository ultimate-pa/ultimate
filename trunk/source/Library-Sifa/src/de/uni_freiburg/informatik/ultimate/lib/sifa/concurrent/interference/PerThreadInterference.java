package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

public class PerThreadInterference implements IInterference {

	private final Map<InterferenceEdgeKey, GuardedPredicate> mPredicates;
	private final IInterferenceApplicator mApplicator;

	public PerThreadInterference(final Map<InterferenceEdgeKey, GuardedPredicate> predicates,
			final IInterferenceApplicator applicator) {
		mPredicates = Map.copyOf(predicates);
		mApplicator = applicator;
	}

	@Override
	public Collection<IPredicate> getPredicates() {
		return mPredicates.values().stream().map(GuardedPredicate::effect).collect(Collectors.toList());
	}

	@Override
	public boolean isTrivial() {
		return mPredicates.isEmpty();
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PerThreadInterference otherPerThread)) {
			return false;
		}
		for (final Entry<InterferenceEdgeKey, GuardedPredicate> entry : mPredicates.entrySet()) {
			final GuardedPredicate otherGp = otherPerThread.mPredicates.get(entry.getKey());
			if (otherGp == null) {
				return false;
			}
			if (!domain.isSubsetEq(entry.getValue().effect(), otherGp.effect()).isTrueForAbstraction()) {
				return false;
			}
			if (entry.getValue().hasGuard() && otherGp.hasGuard()
					&& !domain.isSubsetEq(entry.getValue().guard(), otherGp.guard()).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PerThreadInterference otherPerThread)) {
			throw new IllegalArgumentException(
					"Cannot widen PerThreadInterference with " + other.getClass().getSimpleName());
		}
		return new PerThreadInterference(
				InterferenceUtils.widenGuardedBuckets(mPredicates, otherPerThread.mPredicates, domain), mApplicator);
	}

	@Override
	public int size() {
		return mPredicates.size();
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain, final int wideningThreshold,
			final SifaStats stats) {
		if (isTrivial()) {
			return state;
		}
		return mApplicator.apply(state, mPredicates.values(), domain, wideningThreshold, stats);
	}
}
