package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.PerAbstractLocationInterference.AbstractLocationRelation;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class PerAbstractLocationInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeCollector mCollector;
	private final IInterferenceApplicator mApplicator;
	private final BiFunction<IPredicate, IPredicate, GuardedPredicate> mPredicateConverter;
	private final PerThreadInterferenceFactory mFallback;

	public PerAbstractLocationInterferenceFactory(final InterferenceEdgeCollector collector,
			final IInterferenceApplicator applicator,
			final BiFunction<IPredicate, IPredicate, GuardedPredicate> predicateConverter) {
		mCollector = collector;
		mApplicator = applicator;
		mPredicateConverter = predicateConverter;
		mFallback = new PerThreadInterferenceFactory(collector, applicator, predicateConverter);
	}

	@Override
	public IInterference createEmpty() {
		return new PerAbstractLocationInterference(Map.of(), mApplicator);
	}

	@Override
	public IInterference buildFromStates(final String threadId,
			final Map<IcfgLocation, IPredicate> locationStates) {
		if (!mCollector.hasAbstractLocationIds()) {
			return mFallback.buildFromStates(threadId, locationStates);
		}
		final Map<AbstractLocationRelation, GuardedPredicate> relationPredicates = new HashMap<>();
		final Map<IcfgLocation, Integer> sourceLocationPartitions =
				mCollector.computeSourcePartitionsForSingletonWithForks(locationStates);
		for (final PredicateWithSrcAndTrgt edgePred : mCollector.collectEdgePredicates(threadId, locationStates)) {
			final Integer sourceAbsLoc = mCollector.getAbstractLocationIdOrNull(edgePred.source());
			final Integer targetAbsLoc = mCollector.getAbstractLocationIdOrNull(edgePred.target());
			if (sourceAbsLoc == null || targetAbsLoc == null) {
				continue;
			}
			final int sourceLocationPartition = sourceLocationPartitions.getOrDefault(edgePred.source(), 0);
			final AbstractLocationRelation relation =
					new AbstractLocationRelation(sourceAbsLoc, targetAbsLoc, sourceLocationPartition);
			final GuardedPredicate fromConverter = mPredicateConverter.apply(edgePred.predicate(),
					edgePred.preStateGuard());
			final GuardedPredicate converted = new GuardedPredicate(fromConverter.guard(), fromConverter.effect(),
					edgePred.modifiedGlobals());
			mergeIntoWithJoinGuarded(relationPredicates, relation, converted);
		}
		return new PerAbstractLocationInterference(relationPredicates, mApplicator);
	}

	private void mergeIntoWithJoinGuarded(final Map<AbstractLocationRelation, GuardedPredicate> targetMap,
			final AbstractLocationRelation key, final GuardedPredicate gp) {
		final GuardedPredicate existing = targetMap.get(key);
		if (existing == null) {
			targetMap.put(key, gp);
		} else {
			final IPredicate joinedEffect = mCollector.join(existing.effect(), gp.effect());
			final IPredicate joinedGuard;
			if (existing.hasGuard() && gp.hasGuard()) {
				joinedGuard = mCollector.join(existing.guard(), gp.guard());
			} else {
				joinedGuard = null;
			}
			targetMap.put(key, new GuardedPredicate(joinedGuard, joinedEffect,
					InterferenceUtils.mergeModifiedGlobals(existing, gp)));
		}
	}
}
