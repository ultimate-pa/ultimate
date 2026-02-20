package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.AbstractLocationInterference.AbstractLocationRelation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.InterferenceMergeMode;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public class AbstractLocationJoinThenOrInterference implements IInterference {

	private final IPredicate mRelation;
	private final Set<Integer> mSourceAbstractLocations;
	private final Set<Integer> mTargetAbstractLocations;
	private final int mRelationGroupCount;
	private final InterferenceMergeMode mApplyMergeMode;

	public AbstractLocationJoinThenOrInterference(final IPredicate relation, final Set<Integer> sourceAbstractLocations,
			final Set<Integer> targetAbstractLocations, final int relationGroupCount,
			final InterferenceMergeMode applyMergeMode) {
		mRelation = relation;
		mSourceAbstractLocations = Set.copyOf(sourceAbstractLocations);
		mTargetAbstractLocations = Set.copyOf(targetAbstractLocations);
		mRelationGroupCount = relationGroupCount;
		mApplyMergeMode = applyMergeMode;
	}

	@Override
	public IInterference build(final String threadId, final Map<IcfgLocation, IPredicate> locationStates,
			final InterferenceFactory factory) {
		if (!factory.hasAbstractLocationIds()) {
			return new PerThreadInterference(factory.falsePredicate(), factory.getMergeMode()).build(threadId,
					locationStates, factory);
		}
		final Map<AbstractLocationRelation, IPredicate> joinedByAbstractLocationRelation = new HashMap<>();
		final Map<IcfgLocation, Integer> sourceLocationPartitions = factory
				.computeSourcePartitionsForSingletonWithForks(locationStates);
		final Set<Integer> sourceAbstractLocations = new HashSet<>();
		final Set<Integer> targetAbstractLocations = new HashSet<>();
		for (final EdgePredicate edgePred : factory.collectEdgePredicates(threadId, locationStates)) {
			final Integer sourceAbstractLocation = factory.getAbstractLocationIdOrNull(edgePred.source());
			final Integer targetAbstractLocation = factory.getAbstractLocationIdOrNull(edgePred.target());
			if (sourceAbstractLocation == null || targetAbstractLocation == null) {
				continue;
			}
			final int sourceLocationPartition = sourceLocationPartitions.getOrDefault(edgePred.source(), 0);
			final AbstractLocationRelation relation = new AbstractLocationRelation(sourceAbstractLocation,
					targetAbstractLocation, sourceLocationPartition);
			factory.mergeIntoWithJoin(joinedByAbstractLocationRelation, relation, edgePred.predicate());
			sourceAbstractLocations.add(sourceAbstractLocation);
			targetAbstractLocations.add(targetAbstractLocation);
		}
		final IPredicate relation = factory.orPredicates(joinedByAbstractLocationRelation.values());
		return new AbstractLocationJoinThenOrInterference(relation, sourceAbstractLocations, targetAbstractLocations,
				joinedByAbstractLocationRelation.size(), factory.getMergeMode());
	}

	@Override
	public Set<Integer> getSourceAbsLocations() {
		return mSourceAbstractLocations;
	}

	@Override
	public Set<Integer> getTargetAbsLocations() {
		return mTargetAbstractLocations;
	}

	@Override
	public Collection<IPredicate> getPredicates() {
		return List.of(mRelation);
	}

	@Override
	public boolean isTrivial() {
		return SmtUtils.isFalseLiteral(mRelation.getFormula());
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final AbstractLocationJoinThenOrInterference joinedOr)) {
			return false;
		}
		if (mApplyMergeMode != joinedOr.mApplyMergeMode) {
			return false;
		}
		return domain.isSubsetEq(mRelation, joinedOr.mRelation).isTrueForAbstraction();
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final AbstractLocationJoinThenOrInterference joinedOr)) {
			throw new IllegalArgumentException(
					"Cannot widen AbstractLocationJoinThenOrInterference with " + other.getClass().getSimpleName());
		}
		if (mApplyMergeMode != joinedOr.mApplyMergeMode) {
			throw new IllegalArgumentException(
					"Cannot widen AbstractLocationJoinThenOrInterference with different merge modes");
		}
		final Set<Integer> widenedSourceAbstractLocations = new HashSet<>(mSourceAbstractLocations);
		widenedSourceAbstractLocations.addAll(joinedOr.mSourceAbstractLocations);
		final Set<Integer> widenedTargetAbstractLocations = new HashSet<>(mTargetAbstractLocations);
		widenedTargetAbstractLocations.addAll(joinedOr.mTargetAbstractLocations);
		return new AbstractLocationJoinThenOrInterference(domain.widen(mRelation, joinedOr.mRelation),
				widenedSourceAbstractLocations, widenedTargetAbstractLocations,
				Math.max(mRelationGroupCount, joinedOr.mRelationGroupCount), mApplyMergeMode);
	}

	@Override
	public int size() {
		return isTrivial() ? 0 : 1;
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
				InterferenceUtils.prepareNonFalseRelations(List.of(mRelation), postcondition), mApplyMergeMode, domain,
				postcondition, managedScript, factory, wideningThreshold, stats);
	}
}
