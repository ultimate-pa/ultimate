package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

public class PerThreadInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeCollector mCollector;

	public PerThreadInterferenceFactory(final InterferenceEdgeCollector collector) {
		mCollector = collector;
	}

	@Override
	public IInterference createEmpty() {
		return new PerThreadInterference(mCollector.falsePredicate());
	}

	@Override
	public IInterference buildFromStates(final String threadId,
			final Map<IcfgLocation, IPredicate> locationStates) {
		IPredicate merged = null;
		for (final PredicateWithSrcAndTrgt edgePred : mCollector.collectEdgePredicates(threadId, locationStates)) {
			merged = merged == null ? edgePred.predicate() : mCollector.join(merged, edgePred.predicate());
		}
		if (merged == null) {
			merged = mCollector.falsePredicate();
		}
		return new PerThreadInterference(merged);
	}
}
