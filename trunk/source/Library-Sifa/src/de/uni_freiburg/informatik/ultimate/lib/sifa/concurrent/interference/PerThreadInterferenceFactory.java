package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Map;
import java.util.HashMap;
import java.util.Collection;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public class PerThreadInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeCollector mCollector;
	private final IInterferenceApplicator mApplicator;
	private final Function<PredicateWithSrcAndTrgt, Collection<GuardedPredicate>> mPredicateConverter;

	public PerThreadInterferenceFactory(final InterferenceEdgeCollector collector,
			final IInterferenceApplicator applicator,
			final Function<PredicateWithSrcAndTrgt, Collection<GuardedPredicate>> predicateConverter) {
		mCollector = collector;
		mApplicator = applicator;
		mPredicateConverter = predicateConverter;
	}

	@Override
	public IInterference createEmpty() {
		return new PerThreadInterference(Map.of(), mApplicator);
	}

	@Override
	public IInterference buildFromStates(final String threadId,
			final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<InterferenceEdgeKey, GuardedPredicate> predicates = new HashMap<>();
		final Map<String, Integer> nextIndexByEdge = new HashMap<>();
		for (final PredicateWithSrcAndTrgt edgePred : mCollector.collectEdgePredicates(threadId, locationStates).stream()
				.sorted(InterferenceUtils.EDGE_PREDICATE_ORDER).toList()) {
			for (final GuardedPredicate converted : mPredicateConverter.apply(edgePred)) {
				final String edgeKey = edgePred.source() + "->" + edgePred.target();
				final int predicateIndex = nextIndexByEdge.getOrDefault(edgeKey, 0);
				nextIndexByEdge.put(edgeKey, predicateIndex + 1);
				predicates.put(new InterferenceEdgeKey(edgePred.source(), edgePred.target(), predicateIndex), converted);
			}
		}
		return new PerThreadInterference(predicates, mApplicator);
	}
}
