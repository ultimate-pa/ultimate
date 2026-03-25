package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.PerEdgeInterference.EdgeKey;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class PerEdgeInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeCollector mCollector;
	private final IInterferenceApplicator mApplicator;
	private final BiFunction<IPredicate, IPredicate, GuardedPredicate> mPredicateConverter;

	public PerEdgeInterferenceFactory(final InterferenceEdgeCollector collector,
			final IInterferenceApplicator applicator,
			final BiFunction<IPredicate, IPredicate, GuardedPredicate> predicateConverter) {
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
		final Map<EdgeKey, GuardedPredicate> edgePredicates = new HashMap<>();
		for (final PredicateWithSrcAndTrgt edgePred : mCollector.collectEdgePredicates(threadId, locationStates)) {
			final GuardedPredicate fromConverter = mPredicateConverter.apply(edgePred.predicate(),
					edgePred.preStateGuard());
			final GuardedPredicate converted = new GuardedPredicate(fromConverter.guard(), fromConverter.effect(),
					edgePred.modifiedGlobals());
			final EdgeKey key = new EdgeKey(edgePred.source(), edgePred.target());
			mergeIntoWithJoinGuarded(edgePredicates, key, converted);
		}
		return new PerEdgeInterference(edgePredicates, mApplicator);
	}

	private void mergeIntoWithJoinGuarded(final Map<EdgeKey, GuardedPredicate> targetMap, final EdgeKey key,
			final GuardedPredicate gp) {
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
			final Set<TermVariable> mergedModified = InterferenceUtils.mergeModifiedGlobals(existing, gp);
			targetMap.put(key, new GuardedPredicate(joinedGuard, joinedEffect, mergedModified));
		}
	}
}
