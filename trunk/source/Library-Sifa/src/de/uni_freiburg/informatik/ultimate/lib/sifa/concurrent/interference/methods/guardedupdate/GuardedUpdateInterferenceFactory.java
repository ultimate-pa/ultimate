package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.guardedupdate;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGroupKey;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceGrouping;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.TranslatedInterferenceOfEdge;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class GuardedUpdateInterferenceFactory
		extends GroupedInterferenceFactory<Map<InterferenceGroupKey, Map<TranslatedInterferenceOfEdge, GuardedUpdate>>> {

	private Map<String, Map<Integer, LocationMoveSummary>> mLocationMoveSummaries;

	private final Map<TranslatedInterferenceOfEdge, SummaryOfPreviousRound> mSummariesOfPreviousRound =
			new IdentityHashMap<>();
	private final Map<IPredicate, IPredicate> mSharedStateProjections = new IdentityHashMap<>();

	private record SummaryOfPreviousRound(IPredicate sourceState, GuardedUpdate update) {
	}

	public GuardedUpdateInterferenceFactory(final InterferenceEdgeCollector edgeCollector,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final MustLocksetAnalysis locksetInfo, final Map<String, Set<IcfgLocation>> preForkSourcesByThread) {
		super(edgeCollector, translator, postcondition, managedScript, predicateFactory, locksetInfo,
				preForkSourcesByThread);
	}

	@Override
	protected boolean requiresChangedGlobals() {
		return false;
	}

	@Override
	protected Map<InterferenceGroupKey, Map<TranslatedInterferenceOfEdge, GuardedUpdate>> createAccumulator() {
		return new LinkedHashMap<>();
	}

	@Override
	protected void accumulateEdgeSummary(
			final Map<InterferenceGroupKey, Map<TranslatedInterferenceOfEdge, GuardedUpdate>> accumulator,
			final TranslatedInterferenceOfEdge edge, final Map<IcfgLocation, IPredicate> threadStates) {
		final IPredicate sourceState = threadStates.get(edge.source());
		if (sourceState == null) {
			return;
		}
		if (isLocationMove(edge)) {
			accumulateLocationMoveClosure(accumulator, edge);
			return;
		}
		final SummaryOfPreviousRound previous = mSummariesOfPreviousRound.get(edge);
		final GuardedUpdate update;
		if (previous != null && previous.sourceState() == sourceState) {
			update = previous.update();
		} else {
			final IPredicate sharedPreState =
					mSharedStateProjections.computeIfAbsent(sourceState, mTranslator::projectPreStateToSharedState);
			final GuardedUpdate created = tryCreateUpdate(edge, sharedPreState);
			update = created != null && InterferenceUtils.shouldSkipTrivialPredicate(created.effect()) ? null
					: created;
			mSummariesOfPreviousRound.put(edge, new SummaryOfPreviousRound(sourceState, update));
		}
		if (update == null) {
			return;
		}
		accumulator.computeIfAbsent(groupKeyFor(edge), key -> new LinkedHashMap<>()).put(edge, update);
	}

	private void accumulateLocationMoveClosure(
			final Map<InterferenceGroupKey, Map<TranslatedInterferenceOfEdge, GuardedUpdate>> accumulator,
			final TranslatedInterferenceOfEdge edge) {
		final LocationMoveSummary summary =
				locationMoveSummaries().get(edge.source().getProcedure()).get(sourceAbs(edge));
		accumulator.computeIfAbsent(summary.groupKey(), key -> new LinkedHashMap<>())
				.put(summary.representative(), summary.update());
	}

	private boolean isLocationMove(final TranslatedInterferenceOfEdge edge) {
		return edge.changedGlobals().isEmpty() && edge.forkedThreadId() == null && sourceAbs(edge) != targetAbs(edge)
				&& mTranslator.getLocationTermVarOrNull(edge.source().getProcedure()) != null;
	}

	private static int sourceAbs(final TranslatedInterferenceOfEdge edge) {
		return edge.abstractLocationPair().sourceAbstractLocation();
	}

	private static int targetAbs(final TranslatedInterferenceOfEdge edge) {
		return edge.abstractLocationPair().targetAbstractLocation();
	}

	private record LocationMoveSummary(InterferenceGroupKey groupKey, TranslatedInterferenceOfEdge representative,
			GuardedUpdate update) {
	}

	private Map<String, Map<Integer, LocationMoveSummary>> locationMoveSummaries() {
		if (mLocationMoveSummaries != null) {
			return mLocationMoveSummaries;
		}
		final Map<String, Map<Integer, Set<Integer>>> moveGraph = new LinkedHashMap<>();
		final Map<String, Map<Integer, TranslatedInterferenceOfEdge>> representatives = new LinkedHashMap<>();
		final Map<String, Map<Integer, Set<IcfgLocation>>> concreteSources = new LinkedHashMap<>();
		for (final TranslatedInterferenceOfEdge edge : mEdgeCollector.allPreparedEdges()) {
			if (!isLocationMove(edge)) {
				continue;
			}
			final String thread = edge.source().getProcedure();
			moveGraph.computeIfAbsent(thread, t -> new LinkedHashMap<>())
					.computeIfAbsent(sourceAbs(edge), s -> new LinkedHashSet<>()).add(targetAbs(edge));
			representatives.computeIfAbsent(thread, t -> new LinkedHashMap<>()).putIfAbsent(sourceAbs(edge), edge);
			concreteSources.computeIfAbsent(thread, t -> new LinkedHashMap<>())
					.computeIfAbsent(sourceAbs(edge), s -> new LinkedHashSet<>()).add(edge.source());
		}
		final Map<String, Map<Integer, LocationMoveSummary>> summaries = new LinkedHashMap<>();
		moveGraph.forEach((thread, successors) -> {
			final TermVariable locVar = mTranslator.getLocationTermVarOrNull(thread);
			final Map<Integer, LocationMoveSummary> perSource = new LinkedHashMap<>();
			successors.keySet().forEach(src -> perSource.put(src,
					createLocationMoveSummary(thread, locVar, src, writeFreeClosure(src, successors),
							representatives.get(thread).get(src), concreteSources.get(thread).get(src))));
			summaries.put(thread, perSource);
		});
		mLocationMoveSummaries = summaries;
		return summaries;
	}

	private static Set<Integer> writeFreeClosure(final int start, final Map<Integer, Set<Integer>> successors) {
		final Set<Integer> reached = new LinkedHashSet<>();
		final ArrayDeque<Integer> pending = new ArrayDeque<>(successors.getOrDefault(start, Set.of()));
		while (!pending.isEmpty()) {
			final int next = pending.poll();
			if (reached.add(next)) {
				pending.addAll(successors.getOrDefault(next, Set.of()));
			}
		}
		return reached;
	}

	private LocationMoveSummary createLocationMoveSummary(final String thread, final TermVariable locVar,
			final int sourceAbs, final Set<Integer> reachable, final TranslatedInterferenceOfEdge representative,
			final Set<IcfgLocation> sources) {
		final IPredicate guard = mPredicateFactory.newPredicate(locEquality(locVar, sourceAbs));
		final IPredicate effect = mPredicateFactory.newPredicate(SmtUtils.or(mManagedScript.getScript(),
				reachable.stream().map(target -> locEquality(locVar, target)).toList()));
		final GuardedUpdate update = new GuardedUpdate(guard, effect, Set.of(locVar));
		final InterferenceGroupKey key = new InterferenceGroupKey(thread,
				new InterferenceGrouping.AbstractLocationPair(sourceAbs, sourceAbs), Set.of(), null,
				Set.copyOf(sources));
		return new LocationMoveSummary(key, representative, update);
	}

	private Term locEquality(final TermVariable locVar, final int abstractLocation) {
		final var script = mManagedScript.getScript();
		return SmtUtils.binaryEquality(script, locVar,
				SmtUtils.constructIntValue(script, java.math.BigInteger.valueOf(abstractLocation)));
	}

	@Override
	protected IInterferenceSet buildInterferenceSet(
			final Map<InterferenceGroupKey, Map<TranslatedInterferenceOfEdge, GuardedUpdate>> accumulator) {
		if (accumulator.isEmpty()) {
			return null;
		}
		final Map<InterferenceGroupKey, GuardedUpdateInterference.GuardedUpdateGroup> merged = new LinkedHashMap<>();
		accumulator.forEach((key, updates) -> merged.put(key,
				new GuardedUpdateInterference.GuardedUpdateGroup(updates)));
		return new GuardedUpdateInterference(merged, mPreForkSourcesByThread, mManagedScript, mPredicateFactory);
	}

	private GuardedUpdate tryCreateUpdate(final TranslatedInterferenceOfEdge edge, final IPredicate sharedPreState) {
		final Set<TermVariable> modified = modifiedTermVariablesOf(edge);
		if (modified.isEmpty() && edge.changedGlobals().isEmpty()) {
			return null;
		}
		final IPredicate relationalInterference = conjoin(sharedPreState, edge.transitionPredicate());
		if (InterferenceUtils.shouldSkipTrivialPredicate(relationalInterference)) {
			return null;
		}
		final IPredicate effect = mPostcondition.strongestPostcondition(mTruePredicate, relationalInterference);
		final IPredicate guard = GuardedUpdateUtils.extractTransitionAwareGuard(relationalInterference,
				mPostcondition.primedVariablesIn(relationalInterference), mManagedScript, mPredicateFactory);
		if (guard != null && SmtUtils.isFalseLiteral(guard.getFormula())) {
			return null;
		}
		return new GuardedUpdate(guard, effect, modified);
	}

	private Set<TermVariable> modifiedTermVariablesOf(final TranslatedInterferenceOfEdge edge) {
		final Set<TermVariable> modified = new HashSet<>();
		for (final IProgramVar changed : edge.changedGlobals()) {
			modified.add(changed.getTermVariable());
		}
		final IcfgLocation source = edge.source();
		final TermVariable interferingLoc = mTranslator.getLocationTermVarOrNull(source.getProcedure());
		final boolean locationChanges =
				edge.forkedThreadId() != null || !mTranslator.isLocationStutterStep(source, edge.target());
		if (interferingLoc != null && locationChanges) {
			modified.add(interferingLoc);
		}
		if (edge.forkedThreadId() != null) {
			final TermVariable forkedLoc = mTranslator.getLocationTermVarOrNull(edge.forkedThreadId());
			if (forkedLoc != null) {
				modified.add(forkedLoc);
			}
		}
		return modified.isEmpty() ? Set.of() : Set.copyOf(modified);
	}
}
