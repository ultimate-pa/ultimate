package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class PerThreadInterferenceFactory implements IInterferenceFactory {

	private final InterferenceEdgeCollector mCollector;
	private final IInterferenceApplicator mApplicator;
	private final BiFunction<IPredicate, IPredicate, GuardedPredicate> mPredicateConverter;

	public PerThreadInterferenceFactory(final InterferenceEdgeCollector collector,
			final IInterferenceApplicator applicator,
			final BiFunction<IPredicate, IPredicate, GuardedPredicate> predicateConverter) {
		mCollector = collector;
		mApplicator = applicator;
		mPredicateConverter = predicateConverter;
	}

	@Override
	public IInterference createEmpty() {
		return new PerThreadInterference(GuardedPredicate.unguarded(mCollector.falsePredicate()), mApplicator);
	}

	@Override
	public IInterference buildFromStates(final String threadId,
			final Map<IcfgLocation, IPredicate> locationStates) {
		GuardedPredicate merged = null;
		for (final PredicateWithSrcAndTrgt edgePred : mCollector.collectEdgePredicates(threadId, locationStates)) {
			final GuardedPredicate fromConverter = mPredicateConverter.apply(edgePred.predicate(),
					edgePred.preStateGuard());
			final GuardedPredicate converted = new GuardedPredicate(fromConverter.guard(), fromConverter.effect(),
					edgePred.modifiedGlobals());
			merged = merged == null ? converted : joinGuarded(merged, converted);
		}
		if (merged == null) {
			merged = GuardedPredicate.unguarded(mCollector.falsePredicate());
		}
		return new PerThreadInterference(merged, mApplicator);
	}

	private GuardedPredicate joinGuarded(final GuardedPredicate left, final GuardedPredicate right) {
		final IPredicate joinedEffect = mCollector.join(left.effect(), right.effect());
		final IPredicate joinedGuard;
		if (left.hasGuard() && right.hasGuard()) {
			joinedGuard = mCollector.join(left.guard(), right.guard());
		} else {
			joinedGuard = null;
		}
		final Set<TermVariable> mergedModified = InterferenceUtils.mergeModifiedGlobals(left, right);
		return new GuardedPredicate(joinedGuard, joinedEffect, mergedModified);
	}
}
