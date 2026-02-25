package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceFactory.EdgePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

public class PerAbstractLocationInterference implements IInterference {

	public static record AbstractLocationRelation(int sourceAbstractLocation, int targetAbstractLocation,
			int sourceLocationPartition) {
	}

	private final Map<AbstractLocationRelation, IPredicate> mRelationPredicates;
	private final Set<Integer> mSourceAbstractLocations;
	private final Set<Integer> mTargetAbstractLocations;

	public PerAbstractLocationInterference(final Map<AbstractLocationRelation, IPredicate> relationPredicates) {
		mRelationPredicates = Map.copyOf(relationPredicates);
		final Set<Integer> sourceAbstractLocations = new HashSet<>();
		final Set<Integer> targetAbstractLocations = new HashSet<>();
		for (final AbstractLocationRelation relation : mRelationPredicates.keySet()) {
			sourceAbstractLocations.add(relation.sourceAbstractLocation());
			targetAbstractLocations.add(relation.targetAbstractLocation());
		}
		mSourceAbstractLocations = Set.copyOf(sourceAbstractLocations);
		mTargetAbstractLocations = Set.copyOf(targetAbstractLocations);
	}

	@Override
	public IInterference build(final String threadId, final Map<IcfgLocation, IPredicate> locationStates,
			final InterferenceFactory factory) {
		if (!factory.hasAbstractLocationIds()) {
			return new PerThreadInterference(factory.falsePredicate()).build(threadId, locationStates, factory);
		}
		final Map<AbstractLocationRelation, IPredicate> relationPredicates = new HashMap<>();
		final Map<IcfgLocation, Integer> sourceLocationPartitions = factory
				.computeSourcePartitionsForSingletonWithForks(locationStates);
		for (final EdgePredicate edgePred : factory.collectEdgePredicates(threadId, locationStates)) {
			final Integer sourceAbstractLocation = factory.getAbstractLocationIdOrNull(edgePred.source());
			final Integer targetAbstractLocation = factory.getAbstractLocationIdOrNull(edgePred.target());
			if (sourceAbstractLocation == null || targetAbstractLocation == null) {
				continue;
			}
			final int sourceLocationPartition = sourceLocationPartitions.getOrDefault(edgePred.source(), 0);
			final AbstractLocationRelation relation = new AbstractLocationRelation(sourceAbstractLocation,
					targetAbstractLocation, sourceLocationPartition);
			factory.mergeIntoWithJoin(relationPredicates, relation, edgePred.predicate());
		}
		return new PerAbstractLocationInterference(relationPredicates);
	}

	public Set<AbstractLocationRelation> getAbstractLocationRelations() {
		return mRelationPredicates.keySet();
	}

	public Map<AbstractLocationRelation, IPredicate> getPredicatesByAbstractLocationRelation() {
		return mRelationPredicates;
	}

	@Override
	public Collection<IPredicate> getPredicates() {
		return mRelationPredicates.values();
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
		for (final Entry<AbstractLocationRelation, IPredicate> entry : mRelationPredicates.entrySet()) {
			final IPredicate otherPred = partitioned.mRelationPredicates.get(entry.getKey());
			if (otherPred == null || !domain.isSubsetEq(entry.getValue(), otherPred).isTrueForAbstraction()) {
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
		final Map<AbstractLocationRelation, IPredicate> widened = InterferenceUtils.widenBuckets(mRelationPredicates,
				partitioned.mRelationPredicates, domain);
		return new PerAbstractLocationInterference(widened);
	}

	@Override
	public int size() {
		return mRelationPredicates.size();
	}

	@Override
	public IPredicate applyUntilFixpoint(final IPredicate state, final IDomain domain,
			final RelationalPredicatePostcondition postcondition, final GhostVariableManager ghostVars,
			final ManagedScript managedScript, final BasicPredicateFactory factory, final int wideningThreshold,
			final SifaStats stats) {
		if (isTrivial()) {
			return state;
		}
		return InterferenceUtils.applyUntilFixpoint(state,
				InterferenceUtils.prepareNonFalseRelations(mRelationPredicates.values(), postcondition), domain,
				postcondition, wideningThreshold, stats);
	}
}
