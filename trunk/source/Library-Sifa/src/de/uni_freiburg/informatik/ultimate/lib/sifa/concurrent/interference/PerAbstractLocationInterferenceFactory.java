package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.PerAbstractLocationInterference.AbstractLocationRelation;

public class PerAbstractLocationInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeCollector mCollector;
	private final PerThreadInterferenceFactory mFallback;

	public PerAbstractLocationInterferenceFactory(final InterferenceEdgeCollector collector) {
		mCollector = collector;
		mFallback = new PerThreadInterferenceFactory(collector);
	}

	@Override
	public IInterference createEmpty() {
		return new PerAbstractLocationInterference(Map.of());
	}

	@Override
	public IInterference buildFromStates(final String threadId,
			final Map<IcfgLocation, IPredicate> locationStates) {
		if (!mCollector.hasAbstractLocationIds()) {
			return mFallback.buildFromStates(threadId, locationStates);
		}
		final Map<AbstractLocationRelation, IPredicate> relationPredicates = new HashMap<>();
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
			mCollector.mergeIntoWithJoin(relationPredicates, relation, edgePred.predicate());
		}
		return new PerAbstractLocationInterference(relationPredicates);
	}
}
