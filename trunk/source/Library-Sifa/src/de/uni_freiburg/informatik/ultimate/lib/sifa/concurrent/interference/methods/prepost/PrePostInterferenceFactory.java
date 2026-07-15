package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.prepost;

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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.prepost.PrePostInterference.PrePostPair;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public final class PrePostInterferenceFactory
		extends GroupedInterferenceFactory<Map<InterferenceGroupKey, PrePostPair>> {

	public PrePostInterferenceFactory(final InterferenceEdgeCollector edgeCollector,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final MustLocksetAnalysis locksetInfo, final Map<String, Set<IcfgLocation>> preForkSourcesByThread) {
		super(edgeCollector, translator, postcondition, managedScript, predicateFactory, locksetInfo,
				preForkSourcesByThread);
	}

	@Override
	protected Map<InterferenceGroupKey, PrePostPair> createAccumulator() {
		return new LinkedHashMap<>();
	}

	@Override
	protected void accumulateEdgeSummary(final Map<InterferenceGroupKey, PrePostPair> accumulator,
			final TranslatedInterferenceOfEdge edge, final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate sourceState = threadStates.get(edge.source());
		if (sourceState == null) {
			return;
		}
		final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(sourceState);
		final IPredicate relationalInterference = conjoin(sharedPreState, edge.transitionPredicate());
		if (InterferenceUtils.shouldSkipTrivialPredicate(relationalInterference)) {
			return;
		}
		PrePostPair mergedPair = null;
		for (final Term preDisjunctTerm : SmtUtils.getDisjuncts(sharedPreState.getFormula())) {
			if (SmtUtils.isFalseLiteral(preDisjunctTerm)) {
				continue;
			}
			final IPredicate preDisjunct = mPredicateFactory.newPredicate(preDisjunctTerm);
			final IPredicate postState = mPostcondition.strongestPostcondition(preDisjunct, relationalInterference);
			if (!SmtUtils.isFalseLiteral(postState.getFormula())) {
				final PrePostPair nextPair = new PrePostPair(preDisjunct, postState);
				mergedPair = mergedPair == null ? nextPair : mergePairs(mergedPair, nextPair);
			}
		}
		if (mergedPair != null) {
			accumulator.merge(groupKeyFor(edge), mergedPair, this::mergePairs);
		}
	}

	@Override
	protected IInterferenceSet buildInterferenceSet(final Map<InterferenceGroupKey, PrePostPair> accumulator) {
		return accumulator.isEmpty() ? null
				: new PrePostInterference(accumulator, mPreForkSourcesByThread, mManagedScript);
	}

	private PrePostPair mergePairs(final PrePostPair left, final PrePostPair right) {
		return new PrePostPair(disjoin(left.preState(), right.preState()),
				disjoin(left.postState(), right.postState()));
	}
}
