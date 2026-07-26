package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGroupKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.TranslatedInterferenceOfEdge;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition.StrongestPostconditionInterference.RelationalInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

public final class StrongestPostconditionInterferenceFactory
		extends GroupedInterferenceFactory<Map<InterferenceGroupKey, RelationalInterference>> {

	public StrongestPostconditionInterferenceFactory(final InterferenceEdgeCollector edgeCollector,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final BasicPredicateFactory predicateFactory, final ManagedScript managedScript,
			final MustLocksetAnalysis locksetInfo, final Map<String, Set<IcfgLocation>> preForkSourcesByThread) {
		super(edgeCollector, translator, postcondition, managedScript, predicateFactory, locksetInfo,
				preForkSourcesByThread);
	}

	@Override
	protected boolean requiresChangedGlobals() {
		return false;
	}

	@Override
	protected Map<InterferenceGroupKey, RelationalInterference> createAccumulator() {
		return new LinkedHashMap<>();
	}

	@Override
	protected void accumulateEdgeSummary(final Map<InterferenceGroupKey, RelationalInterference> accumulator,
			final TranslatedInterferenceOfEdge edge, final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate relationalInterference = relationalInterferenceOf(edge, threadStates);
		if (relationalInterference == null
				|| InterferenceUtils.shouldSkipTrivialPredicate(relationalInterference)) {
			return;
		}
		final RelationalInterference summary = new RelationalInterference(relationalInterference,
				mPostcondition.prepareRelation(relationalInterference),
				unconditionalPostStateOf(relationalInterference), writesArray(edge));
		accumulator.merge(groupKeyFor(edge), summary, this::mergeSummaries);
	}

	@Override
	protected IInterferenceSet buildInterferenceSet(
			final Map<InterferenceGroupKey, RelationalInterference> accumulator) {
		return accumulator.isEmpty() ? null
				: new StrongestPostconditionInterference(accumulator, mPreForkSourcesByThread, mPostcondition);
	}

	private RelationalInterference mergeSummaries(final RelationalInterference left,
			final RelationalInterference right) {
		final IPredicate mergedRelation = disjoin(left.relationalInterference(), right.relationalInterference());
		final IPredicate mergedPostState = disjoin(left.unconditionalPostState(), right.unconditionalPostState());
		return new RelationalInterference(mergedRelation, mPostcondition.prepareRelation(mergedRelation),
				mergedPostState, left.requiresArrayFallback() || right.requiresArrayFallback());
	}

	private static boolean writesArray(final TranslatedInterferenceOfEdge edge) {
		return edge.changedGlobals().stream().anyMatch(v -> v.getTermVariable().getSort().isArraySort());
	}
}
