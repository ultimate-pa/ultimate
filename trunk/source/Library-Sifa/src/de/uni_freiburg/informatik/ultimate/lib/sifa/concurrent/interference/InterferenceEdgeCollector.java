package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class InterferenceEdgeCollector {

	private final TransFormulaToInterferencePredicate mTranslator;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final IDomain mMergeDomain;

	private static boolean optShouldSkipTrivialPredicate(final IPredicate predicate) {
		return SmtUtils.isTrueLiteral(predicate.getFormula()) || SmtUtils.isFalseLiteral(predicate.getFormula());
	}

	private static record EdgeInterferenceData(IcfgLocation target, TransFormula tf, String forkedThreadId,
			Set<IProgramVar> additionallyChangedGlobals) {
	}

	public InterferenceEdgeCollector(final TransFormulaToInterferencePredicate translator, final IDomain domain,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory) {
		this(translator, domain, null, managedScript, predicateFactory);
	}

	public InterferenceEdgeCollector(final TransFormulaToInterferencePredicate translator, final IDomain domain,
			final IDomain mergeDomain, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory) {
		mTranslator = Objects.requireNonNull(translator);
		mMergeDomain = mergeDomain != null ? mergeDomain : Objects.requireNonNull(domain);
		mManagedScript = Objects.requireNonNull(managedScript);
		mPredicateFactory = Objects.requireNonNull(predicateFactory);
	}

	boolean hasAbstractLocationIds() {
		return mTranslator.hasAbstractLocationIds();
	}

	Integer getAbstractLocationIdOrNull(final IcfgLocation location) {
		return mTranslator.getAbstractLocationIdOrNull(location);
	}

	IPredicate falsePredicate() {
		return mPredicateFactory.newPredicate(mManagedScript.getScript().term("false"));
	}

	IPredicate join(final IPredicate left, final IPredicate right) {
		return mMergeDomain.join(left, right);
	}

	List<PredicateWithSrcAndTrgt> collectEdgePredicates(final String threadId,
			final Map<IcfgLocation, IPredicate> locationStates) {
		final List<PredicateWithSrcAndTrgt> predicates = new ArrayList<>();
		for (final Entry<IcfgLocation, IPredicate> entry : locationStates.entrySet()) {
			final IcfgLocation source = entry.getKey();
			final IPredicate preState = entry.getValue();
			if (preState == null) {
				continue;
			}
			final IPredicate sharedPreState = mTranslator.projectPreStateToSharedState(preState);
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final EdgeInterferenceData data = collectEdgeInterferenceData(threadId, source, edge);
				if (data == null) {
					continue;
				}
				final IPredicate transitionPredicate = buildTransitionPredicate(threadId, source, data);
				final IPredicate predicate = combineWithPreState(sharedPreState, transitionPredicate);
				// opt: skip trivially false/true predicates
				if (optShouldSkipTrivialPredicate(predicate)) {
					continue;
				}
				final Set<TermVariable> modifiedGlobals = computeModifiedGlobals(data, threadId);
				predicates.add(new PredicateWithSrcAndTrgt(source, data.target(), predicate, sharedPreState,
						modifiedGlobals));
			}
		}
		return predicates;
	}

	private Set<TermVariable> computeModifiedGlobals(final EdgeInterferenceData data, final String interferingThread) {
		final Set<TermVariable> modified =
				new HashSet<>(InterferenceUtils.getChangedGlobalTermVars(data.tf(), data.additionallyChangedGlobals()));
		final TermVariable interferingLoc = mTranslator.getLocationTermVarOrNull(interferingThread);
		if (interferingLoc != null) {
			modified.add(interferingLoc);
		}
		if (data.forkedThreadId() != null) {
			final TermVariable forkedLoc = mTranslator.getLocationTermVarOrNull(data.forkedThreadId());
			if (forkedLoc != null) {
				modified.add(forkedLoc);
			}
		}
		return Set.copyOf(modified);
	}

	Map<IcfgLocation, Integer> computeSourcePartitionsForSingletonWithForks(
			final Map<IcfgLocation, IPredicate> locationStates) {
		if (!hasForkEdge(locationStates) || !hasSingleAbstractLocation(locationStates)) {
			return Map.of();
		}
		final List<IcfgLocation> ordered = new ArrayList<>(locationStates.keySet());
		ordered.sort(Comparator.comparing(Object::toString));
		final Map<IcfgLocation, Integer> partition = new HashMap<>();
		int nextId = 1;
		for (final IcfgLocation loc : ordered) {
			partition.put(loc, nextId);
			nextId++;
		}
		return partition;
	}

	<K> void mergeIntoWithJoin(final Map<K, IPredicate> targetMap, final K key, final IPredicate predicate) {
		final IPredicate existing = targetMap.get(key);
		targetMap.put(key, existing == null ? predicate : mMergeDomain.join(existing, predicate));
	}

	private boolean hasForkEdge(final Map<IcfgLocation, IPredicate> locationStates) {
		for (final IcfgLocation source : locationStates.keySet()) {
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean hasSingleAbstractLocation(final Map<IcfgLocation, IPredicate> locationStates) {
		final Set<Integer> absIds = new HashSet<>();
		for (final IcfgLocation source : locationStates.keySet()) {
			final Integer abs = mTranslator.getAbstractLocationIdOrNull(source);
			if (abs != null) {
				absIds.add(abs);
				if (absIds.size() > 1) {
					return false;
				}
			}
		}
		return absIds.size() == 1;
	}

	private IPredicate combineWithPreState(final IPredicate sharedPreState, final IPredicate transitionPredicate) {
		final Term combined = SmtUtils.andWithExtendedLocalSimplification(mManagedScript.getScript(),
				sharedPreState.getFormula(), transitionPredicate.getFormula());
		return mPredicateFactory.newPredicate(combined);
	}

	private IPredicate buildTransitionPredicate(final String threadId, final IcfgLocation sourceLocation,
			final EdgeInterferenceData data) {
		if (data.forkedThreadId() != null) {
			final IcfgLocation forkedEntry = mTranslator.getEntryLocation(data.forkedThreadId());
			return mTranslator.translateForInterferenceWithFork(data.tf(), threadId, sourceLocation, data.target(),
					data.forkedThreadId(), forkedEntry, data.additionallyChangedGlobals());
		}
		return mTranslator.translateForInterference(data.tf(), threadId, sourceLocation, data.target(),
				data.additionallyChangedGlobals());
	}

	private static boolean optShouldSkipAsNonInterfering(final boolean interferenceRelevant,
			final boolean locationStutter) {
		return !interferenceRelevant && locationStutter;
	}

	private EdgeInterferenceData collectEdgeInterferenceData(final String threadId, final IcfgLocation source,
			final IcfgEdge edge) {
		final IcfgLocation target = edge.getTarget();
		if (target == null) {
			return null;
		}
		final TransFormula tf = edge.getTransformula();
		if (tf == null) {
			return null;
		}
		final String forkedThreadId = InterferenceUtils.getForkedThreadOrNull(edge);
		final boolean interferenceRelevant = InterferenceUtils.hasRelevantInterferenceEffect(edge);
		final boolean locationStutter = mTranslator.isLocationStutterStep(source, target) && forkedThreadId == null;
		// opt: skip non-interfering edges
		if (optShouldSkipAsNonInterfering(interferenceRelevant, locationStutter)) {
			return null;
		}
		return new EdgeInterferenceData(target, tf, forkedThreadId, InterferenceUtils.getAdditionalChangedGlobals(edge));
	}
}
