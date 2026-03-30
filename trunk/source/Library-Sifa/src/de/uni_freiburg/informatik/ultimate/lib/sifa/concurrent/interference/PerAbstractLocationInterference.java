package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;

public class PerAbstractLocationInterference implements IInterference {

	public static record AbstractLocationRelation(int sourceAbstractLocation, int targetAbstractLocation,
			int sourceLocationPartition, int predicateIndex) {
	}

	private final Map<AbstractLocationRelation, GuardedPredicate> mRelationPredicates;
	private final Set<Integer> mSourceAbstractLocations;
	private final Set<Integer> mTargetAbstractLocations;
	private final IInterferenceApplicator mApplicator;

	public PerAbstractLocationInterference(final Map<AbstractLocationRelation, GuardedPredicate> relationPredicates,
			final IInterferenceApplicator applicator) {
		mRelationPredicates = Map.copyOf(relationPredicates);
		final Set<Integer> sourceAbstractLocations = new HashSet<>();
		final Set<Integer> targetAbstractLocations = new HashSet<>();
		for (final AbstractLocationRelation relation : mRelationPredicates.keySet()) {
			sourceAbstractLocations.add(relation.sourceAbstractLocation());
			targetAbstractLocations.add(relation.targetAbstractLocation());
		}
		mSourceAbstractLocations = Set.copyOf(sourceAbstractLocations);
		mTargetAbstractLocations = Set.copyOf(targetAbstractLocations);
		mApplicator = applicator;
	}

	public Set<AbstractLocationRelation> getAbstractLocationRelations() {
		return mRelationPredicates.keySet();
	}

	public Map<AbstractLocationRelation, GuardedPredicate> getGuardedPredicatesByAbstractLocationRelation() {
		return mRelationPredicates;
	}

	@Override
	public Collection<IPredicate> getPredicates() {
		return mRelationPredicates.values().stream().map(GuardedPredicate::effect).collect(Collectors.toList());
	}

	@Override
	public boolean isTrivial() {
		return mRelationPredicates.isEmpty();
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PerAbstractLocationInterference partitioned)) {
			return false;
		}
		for (final Entry<AbstractLocationRelation, GuardedPredicate> entry : mRelationPredicates.entrySet()) {
			final GuardedPredicate otherGp = partitioned.mRelationPredicates.get(entry.getKey());
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
		if (!(other instanceof final PerAbstractLocationInterference partitioned)) {
			throw new IllegalArgumentException(
					"Cannot widen PerAbstractLocationInterference with " + other.getClass().getSimpleName());
		}
		final Map<AbstractLocationRelation, GuardedPredicate> widened = InterferenceUtils
				.widenGuardedBuckets(mRelationPredicates, partitioned.mRelationPredicates, domain);
		return new PerAbstractLocationInterference(widened, mApplicator);
	}

	@Override
	public int size() {
		return mRelationPredicates.size();
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain, final int wideningThreshold,
			final SifaStats stats) {
		if (isTrivial()) {
			return state;
		}
		return mApplicator.apply(state, mRelationPredicates.values(), domain, wideningThreshold, stats);
	}
}
