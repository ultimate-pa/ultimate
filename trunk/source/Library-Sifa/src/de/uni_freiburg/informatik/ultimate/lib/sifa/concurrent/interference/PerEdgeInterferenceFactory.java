package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.PerEdgeInterference.EdgeKey;

public class PerEdgeInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeCollector mCollector;

	// TODO: inline private iinterfaces
	public PerEdgeInterferenceFactory(final InterferenceEdgeCollector collector) {
		mCollector = collector;
	}

	@Override
	public IInterference createEmpty() {
		return new PerEdgeInterference(Map.of());
	}

	@Override
	public IInterference buildFromStates(final String threadId, final Map<IcfgLocation, IPredicate> locationStates) {
		final Map<EdgeKey, IPredicate> edgePredicates = new HashMap<>();
		for (final PredicateWithSrcAndTrgt edgePred : mCollector.collectEdgePredicates(threadId, locationStates)) {
			mCollector.mergeIntoWithJoin(edgePredicates, new EdgeKey(edgePred.source(), edgePred.target()),
					edgePred.predicate());
		}
		return new PerEdgeInterference(edgePredicates);
	}
}
