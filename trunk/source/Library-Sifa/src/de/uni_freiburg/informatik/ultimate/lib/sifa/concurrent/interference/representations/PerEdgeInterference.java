package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.representations;

import java.util.Collection;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GuardedPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceApplicator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

public class PerEdgeInterference implements IInterference {

	private final Map<InterferenceEdgeKey, GuardedPredicate> mEdgePredicates;
	private final IInterferenceApplicator mApplicator;

	public PerEdgeInterference(final Map<InterferenceEdgeKey, GuardedPredicate> edgePredicates,
			final IInterferenceApplicator applicator) {
		mEdgePredicates = Map.copyOf(edgePredicates);
		mApplicator = applicator;
	}

	@Override
	public Collection<IPredicate> getPredicates() {
		return mEdgePredicates.values().stream().map(GuardedPredicate::effect).collect(Collectors.toList());
	}

	@Override
	public boolean isTrivial() {
		return mEdgePredicates.isEmpty();
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PerEdgeInterference otherEdge)) {
			return false;
		}
		for (final Entry<InterferenceEdgeKey, GuardedPredicate> entry : mEdgePredicates.entrySet()) {
			final GuardedPredicate otherGp = otherEdge.mEdgePredicates.get(entry.getKey());
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
		if (!(other instanceof final PerEdgeInterference otherEdge)) {
			throw new IllegalArgumentException(
					"Cannot widen PerEdgeInterference with " + other.getClass().getSimpleName());
		}
		return new PerEdgeInterference(
				InterferenceUtils.widenGuardedBuckets(mEdgePredicates, otherEdge.mEdgePredicates, domain), mApplicator);
	}

	@Override
	public int size() {
		return mEdgePredicates.size();
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain, final int wideningThreshold,
			final SifaStats stats) {
		if (isTrivial()) {
			return state;
		}
		return mApplicator.apply(state, mEdgePredicates.values(), domain, wideningThreshold, stats);
	}
}
