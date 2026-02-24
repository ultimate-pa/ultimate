package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceFactory.EdgePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

public class PerEdgeInterference implements IInterference {

	private record EdgeKey(IcfgLocation source, IcfgLocation target) {
	}

	private final Map<EdgeKey, IPredicate> mEdgePredicates;

	public PerEdgeInterference(final Map<EdgeKey, IPredicate> edgePredicates) {
		mEdgePredicates = Map.copyOf(edgePredicates);
	}

	@Override
	public IInterference build(final String threadId, final Map<IcfgLocation, IPredicate> locationStates,
			final InterferenceFactory factory) {
		final Map<EdgeKey, IPredicate> edgePredicates = new HashMap<>();
		for (final EdgePredicate edgePred : factory.collectEdgePredicates(threadId, locationStates)) {
			// edges between distinct location pairs are kept separate; same-pair edges (rare) are joined
			factory.mergeIntoWithJoin(edgePredicates, new EdgeKey(edgePred.source(), edgePred.target()),
					edgePred.predicate());
		}
		return new PerEdgeInterference(edgePredicates);
	}

	@Override
	public Collection<IPredicate> getPredicates() {
		return mEdgePredicates.values();
	}

	@Override
	public boolean isTrivial() {
		return mEdgePredicates.isEmpty();
	}

	@Override
	public boolean isSubsumedBy(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PerEdgeInterference otherEdge)) {
			return false;
		}
		for (final Entry<EdgeKey, IPredicate> entry : mEdgePredicates.entrySet()) {
			final IPredicate otherPred = otherEdge.mEdgePredicates.get(entry.getKey());
			if (otherPred == null || !domain.isSubsetEq(entry.getValue(), otherPred).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}

	@Override
	public IInterference widen(final IInterference other, final IDomain domain) {
		if (!(other instanceof final PerEdgeInterference otherEdge)) {
			throw new IllegalArgumentException(
					"Cannot widen PerEdgeInterference with " + other.getClass().getSimpleName());
		}
		return new PerEdgeInterference(
				InterferenceUtils.widenBuckets(mEdgePredicates, otherEdge.mEdgePredicates, domain));
	}

	@Override
	public int size() {
		return mEdgePredicates.size();
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
				InterferenceUtils.prepareNonFalseRelations(mEdgePredicates.values(), postcondition), domain,
				postcondition, wideningThreshold, stats);
	}
}
