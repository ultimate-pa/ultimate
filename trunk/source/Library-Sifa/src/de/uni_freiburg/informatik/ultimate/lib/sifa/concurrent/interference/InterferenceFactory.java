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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.InterferenceMergeMode;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.InterferenceType;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class InterferenceFactory {

	private final TransFormulaToInterferencePredicate mTranslator;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final IDomain mDomain;
	private final InterferenceMergeMode mMergeMode;
	private final InterferenceType mInterferenceType;

	private static boolean modifiesGlobals(final TransFormula tf) {
		return tf.getAssignedVars().stream().anyMatch(pv -> pv.isGlobal());
	}

	private static boolean isTrivialPredicate(final IPredicate predicate) {
		return SmtUtils.isTrueLiteral(predicate.getFormula()) || SmtUtils.isFalseLiteral(predicate.getFormula());
	}

	private static record EdgeInterferenceData(IcfgLocation target, TransFormula tf, String forkedThreadId) {
	}

	public InterferenceFactory(final TransFormulaToInterferencePredicate translator, final IDomain domain,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory,
			final InterferenceMergeMode mergeMode, final InterferenceType interferenceType) {
		mTranslator = Objects.requireNonNull(translator);
		mDomain = Objects.requireNonNull(domain);
		mManagedScript = Objects.requireNonNull(managedScript);
		mPredicateFactory = Objects.requireNonNull(predicateFactory);
		mMergeMode = Objects.requireNonNull(mergeMode);
		mInterferenceType = Objects.requireNonNull(interferenceType);
	}

	public IInterference createBuilder() {
		final IPredicate falsePredicate = falsePredicate();
		return switch (mInterferenceType) {
		case PER_THREAD -> new PerThreadInterference(falsePredicate, mMergeMode);
		case PER_ABSTRACT_LOCATION -> new AbstractLocationInterference(Map.of(), mMergeMode);
		case PER_THREAD_JOINED_ABSTRACT_LOCATIONS ->
			new AbstractLocationJoinThenOrInterference(falsePredicate, Set.of(), Set.of(), 0, mMergeMode);
		};
	}

	InterferenceMergeMode getMergeMode() {
		return mMergeMode;
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

	List<EdgePredicate> collectEdgePredicates(final String threadId,
			final Map<IcfgLocation, IPredicate> locationStates) {
		final List<EdgePredicate> predicates = new ArrayList<>();
		for (final Entry<IcfgLocation, IPredicate> entry : locationStates.entrySet()) {
			final IcfgLocation source = entry.getKey();
			final IPredicate preState = entry.getValue();
			if (preState == null) {
				continue;
			}
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final EdgeInterferenceData data = collectEdgeInterferenceData(source, edge);
				if (data == null) {
					continue;
				}
				final IPredicate predicate = buildInterferencePredicate(threadId, preState, source, data);
				if (isTrivialPredicate(predicate)) {
					continue;
				}
				predicates.add(new EdgePredicate(source, data.target(), predicate));
			}
		}
		return predicates;
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

	IPredicate merge(final IPredicate left, final IPredicate right) {
		if (mMergeMode == InterferenceMergeMode.OR) {
			return mPredicateFactory
					.newPredicate(SmtUtils.or(mManagedScript.getScript(), left.getFormula(), right.getFormula()));
		}
		return mDomain.join(left, right);
	}

	<K> void mergeInto(final Map<K, IPredicate> targetMap, final K key, final IPredicate predicate) {
		final IPredicate existing = targetMap.get(key);
		targetMap.put(key, existing == null ? predicate : merge(existing, predicate));
	}

	<K> void mergeIntoWithOr(final Map<K, IPredicate> targetMap, final K key, final IPredicate predicate) {
		final IPredicate existing = targetMap.get(key);
		if (existing == null) {
			targetMap.put(key, predicate);
			return;
		}
		targetMap.put(key, mPredicateFactory
				.newPredicate(SmtUtils.or(mManagedScript.getScript(), existing.getFormula(), predicate.getFormula())));
	}

	<K> void mergeIntoWithJoin(final Map<K, IPredicate> targetMap, final K key, final IPredicate predicate) {
		final IPredicate existing = targetMap.get(key);
		targetMap.put(key, existing == null ? predicate : mDomain.join(existing, predicate));
	}

	IPredicate orPredicates(final Iterable<IPredicate> predicates) {
		IPredicate result = null;
		for (final IPredicate predicate : predicates) {
			if (SmtUtils.isFalseLiteral(predicate.getFormula())) {
				continue;
			}
			result = result == null ? predicate
					: mPredicateFactory.newPredicate(
							SmtUtils.or(mManagedScript.getScript(), result.getFormula(), predicate.getFormula()));
		}
		if (result == null) {
			return falsePredicate();
		}
		return result;
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

	private IPredicate buildInterferencePredicate(final String threadId, final IPredicate preState,
			final IcfgLocation sourceLocation, final EdgeInterferenceData data) {
		final IPredicate transitionPredicate = buildTransitionPredicate(threadId, sourceLocation, data);
		final Term combined = SmtUtils.andWithExtendedLocalSimplification(mManagedScript.getScript(),
				preState.getFormula(), transitionPredicate.getFormula());
		return mPredicateFactory.newPredicate(combined);
	}

	private IPredicate buildTransitionPredicate(final String threadId, final IcfgLocation sourceLocation,
			final EdgeInterferenceData data) {
		if (data.forkedThreadId() != null) {
			final IcfgLocation forkedEntry = mTranslator.getEntryLocation(data.forkedThreadId());
			return mTranslator.translateForInterferenceWithFork(data.tf(), threadId, sourceLocation, data.target(),
					data.forkedThreadId(), forkedEntry);
		}
		return mTranslator.translateForInterference(data.tf(), threadId, sourceLocation, data.target());
	}

	private EdgeInterferenceData collectEdgeInterferenceData(final IcfgLocation source, final IcfgEdge edge) {
		final IcfgLocation target = edge.getTarget();
		if (target == null) {
			return null;
		}
		final TransFormula tf = edge.getTransformula();
		if (tf == null) {
			return null;
		}
		final String forkedThreadId = edge instanceof final IIcfgForkTransitionThreadCurrent<?> forkEdge
				? forkEdge.getNameOfForkedProcedure()
				: null;
		final boolean writesGlobal = modifiesGlobals(tf) || forkedThreadId != null;
		final boolean locationStutter = mTranslator.isLocationStutterStep(source, target) && forkedThreadId == null;
		if (!writesGlobal && locationStutter) {
			return null;
		}
		return new EdgeInterferenceData(target, tf, forkedThreadId);
	}
}
