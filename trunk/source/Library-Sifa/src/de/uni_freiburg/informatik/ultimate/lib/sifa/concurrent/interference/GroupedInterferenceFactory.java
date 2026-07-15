package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public abstract class GroupedInterferenceFactory<A> {

	protected final InterferenceEdgeCollector mEdgeCollector;
	protected final TransFormulaToInterferencePredicate mTranslator;
	protected final RelationalPredicatePostcondition mPostcondition;
	protected final ManagedScript mManagedScript;
	protected final BasicPredicateFactory mPredicateFactory;
	protected final MustLocksetAnalysis mLocksetInfo;
	protected final Map<String, Set<IcfgLocation>> mPreForkSourcesByThread;
	protected final IPredicate mTruePredicate;
	protected final IPredicate mFalsePredicate;

	protected GroupedInterferenceFactory(final InterferenceEdgeCollector edgeCollector,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final MustLocksetAnalysis locksetInfo, final Map<String, Set<IcfgLocation>> preForkSourcesByThread) {
		mEdgeCollector = edgeCollector;
		mTranslator = translator;
		mPostcondition = postcondition;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mLocksetInfo = locksetInfo;
		mPreForkSourcesByThread = Map.copyOf(preForkSourcesByThread);
		mTruePredicate = predicateFactory.newPredicate(managedScript.getScript().term("true"));
		mFalsePredicate = predicateFactory.newPredicate(managedScript.getScript().term("false"));
	}

	public final IInterferenceSet buildFromAllStates(final Map<String, Map<IcfgLocation, IPredicate>> perThreadStates) {
		final Map<IcfgLocation, IPredicate> allStates = mergeStates(perThreadStates);
		final A accumulator = createAccumulator();
		for (final TranslatedInterferenceOfEdge edge : mEdgeCollector.collect(allStates)) {
			if (requiresChangedGlobals() && edge.changedGlobals().isEmpty()) {
				continue;
			}
			final Map<IcfgLocation, IPredicate> threadStates = perThreadStates.get(edge.source().getProcedure());
			if (threadStates == null) {
				continue;
			}
			accumulateEdgeSummary(accumulator, edge, threadStates);
		}
		return buildInterferenceSet(accumulator);
	}

	protected boolean requiresChangedGlobals() {
		return true;
	}

	protected abstract A createAccumulator();

	protected abstract void accumulateEdgeSummary(A accumulator, TranslatedInterferenceOfEdge edge,
			Map<IcfgLocation, IPredicate> threadStates);

	protected abstract IInterferenceSet buildInterferenceSet(A accumulator);

	protected final InterferenceGroupKey groupKeyFor(final TranslatedInterferenceOfEdge edge) {
		return new InterferenceGroupKey(edge.source().getProcedure(), edge.abstractLocationPair(),
				mustHeldLocksAroundEdge(edge), edge.forkedThreadId(), Set.of(edge.source()));
	}

	protected final Set<String> mustHeldLocksAroundEdge(final TranslatedInterferenceOfEdge edge) {
		final Set<String> sourceLockset = mLocksetInfo.mustLocksetAt(edge.source());
		final Set<String> targetLockset = mLocksetInfo.mustLocksetAt(edge.target());
		if (sourceLockset.isEmpty()) {
			return targetLockset;
		}
		if (targetLockset.isEmpty()) {
			return sourceLockset;
		}
		final Set<String> union = new LinkedHashSet<>(sourceLockset);
		union.addAll(targetLockset);
		return Set.copyOf(union);
	}

	protected final IPredicate relationalInterferenceOf(final TranslatedInterferenceOfEdge edge,
			final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate sourceState = threadStates.get(edge.source());
		if (sourceState == null) {
			return null;
		}
		final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(sourceState);
		return conjoin(sharedPreState, edge.transitionPredicate());
	}

	protected final IPredicate unconditionalPostStateOf(final IPredicate relationalInterference) {
		return mPostcondition.strongestPostcondition(mTruePredicate, relationalInterference);
	}

	protected final IPredicate conjoin(final IPredicate left, final IPredicate right) {
		final Term combined = SmtUtils.andWithExtendedLocalSimplification(mManagedScript.getScript(),
				left.getFormula(), right.getFormula());
		return mPredicateFactory.newPredicate(combined);
	}

	protected final IPredicate disjoin(final IPredicate left, final IPredicate right) {
		return mPredicateFactory
				.newPredicate(SmtUtils.or(mManagedScript.getScript(), left.getFormula(), right.getFormula()));
	}

	protected static Map<IcfgLocation, IPredicate> mergeStates(
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadStates) {
		final Map<IcfgLocation, IPredicate> merged = new LinkedHashMap<>();
		perThreadStates.values().forEach(merged::putAll);
		return merged;
	}
}
