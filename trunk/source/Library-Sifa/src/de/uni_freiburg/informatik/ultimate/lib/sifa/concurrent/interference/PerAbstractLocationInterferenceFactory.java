package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.HashMap;
import java.util.Map;
import java.util.Collection;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.PerAbstractLocationInterference.AbstractLocationRelation;

public class PerAbstractLocationInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeCollector mCollector;
	private final IInterferenceApplicator mApplicator;
	private final Function<PredicateWithSrcAndTrgt, Collection<GuardedPredicate>> mPredicateConverter;
	private final PerThreadInterferenceFactory mFallback;

	public PerAbstractLocationInterferenceFactory(final InterferenceEdgeCollector collector,
			final IInterferenceApplicator applicator,
			final Function<PredicateWithSrcAndTrgt, Collection<GuardedPredicate>> predicateConverter) {
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
		final Map<String, Integer> nextIndexByRelation = new HashMap<>();
		final Map<IcfgLocation, Integer> sourceLocationPartitions =
				mCollector.computeSourcePartitionsForSingletonWithForks(locationStates);
		for (final PredicateWithSrcAndTrgt edgePred : mCollector.collectEdgePredicates(threadId, locationStates).stream()
				.sorted(InterferenceUtils.EDGE_PREDICATE_ORDER).toList()) {
			final Integer sourceAbsLoc = mCollector.getAbstractLocationIdOrNull(edgePred.source());
			final Integer targetAbsLoc = mCollector.getAbstractLocationIdOrNull(edgePred.target());
			if (sourceAbsLoc == null || targetAbsLoc == null) {
				continue;
			}
			final int sourceLocationPartition = sourceLocationPartitions.getOrDefault(edgePred.source(), 0);
			final String relationKey = sourceAbsLoc + "->" + targetAbsLoc + "#" + sourceLocationPartition;
			for (final GuardedPredicate converted : mPredicateConverter.apply(edgePred)) {
				final int predicateIndex = nextIndexByRelation.getOrDefault(relationKey, 0);
				nextIndexByRelation.put(relationKey, predicateIndex + 1);
				final AbstractLocationRelation relation =
						new AbstractLocationRelation(sourceAbsLoc, targetAbsLoc, sourceLocationPartition, predicateIndex);
				relationPredicates.put(relation, converted);
			}
		}
		return new PerAbstractLocationInterference(relationPredicates, mApplicator);
	}
}
