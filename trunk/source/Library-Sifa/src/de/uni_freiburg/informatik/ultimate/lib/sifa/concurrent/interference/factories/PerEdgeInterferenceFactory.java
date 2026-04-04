package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.factories;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GuardedPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceApplicator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.representations.PerEdgeInterference;

public class PerEdgeInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeCollector mCollector;
	private final IInterferenceApplicator mApplicator;
	private final Function<PredicateWithSrcAndTrgt, Collection<GuardedPredicate>> mPredicateConverter;

	public PerEdgeInterferenceFactory(final InterferenceEdgeCollector collector,
			final IInterferenceApplicator applicator,
			final Function<PredicateWithSrcAndTrgt, Collection<GuardedPredicate>> predicateConverter) {
		mCollector = collector;
		mApplicator = applicator;
		mPredicateConverter = predicateConverter;
	}

	@Override
	public IInterference createEmpty() {
		return new PerEdgeInterference(Map.of(), mApplicator);
	}

	@Override
	public IInterference buildFromStates(final String threadId, final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<InterferenceEdgeKey, GuardedPredicate> edgePredicates = new HashMap<>();
		final Map<String, Integer> nextIndexByEdge = new HashMap<>();
		for (final PredicateWithSrcAndTrgt edgePred : mCollector.collectEdgePredicates(threadId, locationStates)
				.stream().sorted(InterferenceUtils.EDGE_PREDICATE_ORDER).toList()) {
			for (final GuardedPredicate converted : mPredicateConverter.apply(edgePred)) {
				final String edgeKey = edgePred.source() + "->" + edgePred.target();
				final int predicateIndex = nextIndexByEdge.getOrDefault(edgeKey, 0);
				nextIndexByEdge.put(edgeKey, predicateIndex + 1);
				edgePredicates.put(new InterferenceEdgeKey(edgePred.source(), edgePred.target(), predicateIndex),
						converted);
			}
		}
		return new PerEdgeInterference(edgePredicates, mApplicator);
	}
}
