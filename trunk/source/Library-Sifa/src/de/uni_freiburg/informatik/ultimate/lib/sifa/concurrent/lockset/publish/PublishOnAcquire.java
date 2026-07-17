package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.publish;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.LockEdgeClassifier;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class PublishOnAcquire {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final BasicPredicateFactory mPredicateFactory;
	private final Set<IProgramVar> mLockVars;
	private final Map<IProgramVar, MutexInvariant> mInvariants;
	private final Set<IcfgLocation> mSequentialLocations;
	private final Set<TermVariable> mGlobalTvs;

	private PublishOnAcquire(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory, final Set<IProgramVar> lockVars,
			final Map<IProgramVar, MutexInvariant> invariants, final Set<IcfgLocation> sequentialLocations,
			final Set<TermVariable> globalTvs) {
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mLockVars = lockVars;
		mInvariants = invariants;
		mSequentialLocations = sequentialLocations;
		mGlobalTvs = globalTvs;
	}

	public static PublishOnAcquire disabled() {
		return new PublishOnAcquire(null, null, null, Set.of(), Map.of(), Set.of(), Set.of());
	}

	public static PublishOnAcquire discoverProtectedGlobalsAndPublishEdgesDuringPreanalysis(
			final IIcfg<IcfgLocation> icfg, final MustLocksetAnalysis locksetInfo, final String entryProcedure,
			final ThreadActivityPreanalysis threadActivity, final IUltimateServiceProvider services,
			final ManagedScript managedScript, final BasicPredicateFactory predicateFactory) {
		final Set<IProgramVar> lockVars = locksetInfo.getLockVars();
		if (lockVars.isEmpty()) {
			return disabled();
		}
		final Predicate<IcfgLocation> isSequential = onlyOwnThreadCanBeActive(entryProcedure, threadActivity);
		final Map<IProgramVar, MutexInvariant> invariants =
				MutexInvariantPreAnalysis.discover(icfg, locksetInfo, lockVars, isSequential);
		if (invariants.isEmpty()) {
			return disabled();
		}
		final Set<TermVariable> globalTvs = new LinkedHashSet<>();
		icfg.getCfgSmtToolkit().getSymbolTable().getGlobals().forEach(g -> globalTvs.add(g.getTermVariable()));
		return new PublishOnAcquire(services, managedScript, predicateFactory, lockVars, invariants,
				sequentialLocationsOf(icfg, isSequential), globalTvs);
	}

	private static Predicate<IcfgLocation> onlyOwnThreadCanBeActive(final String entryProcedure,
			final ThreadActivityPreanalysis threadActivity) {
		return loc -> loc.getProcedure().equals(entryProcedure)
				&& threadActivity.getActiveThreadsAt(loc).size() <= 1;
	}

	private static Set<IcfgLocation> sequentialLocationsOf(final IIcfg<IcfgLocation> icfg,
			final Predicate<IcfgLocation> isSequential) {
		final Set<IcfgLocation> sequentialLocations = new LinkedHashSet<>();
		IcfgUtils.getAllLocations(icfg).filter(isSequential).forEach(sequentialLocations::add);
		return sequentialLocations;
	}

	public boolean isEmpty() {
		return mInvariants.isEmpty();
	}

	public PublishOnAcquire recomputePublishedInvariants(final Map<IcfgLocation, IPredicate> locationStates, final IDomain domain,
			final BiFunction<IPredicate, IcfgEdge, IPredicate> interferenceFreePost) {
		if (isEmpty()) {
			return this;
		}
		return withRecomputedPublished(
				(lock, invariant) -> recomputeJoinedPublishEdgePostStates(invariant, locationStates, domain, interferenceFreePost));
	}

	public PublishOnAcquire widen(final PublishOnAcquire extracted, final IDomain domain) {
		return withRecomputedPublished((lock, invariant) -> widenPublished(invariant, extracted, domain, lock));
	}

	public IPredicate applyLockInvariantAtAcquireEdges(final IPredicate state, final IIcfgTransition<IcfgLocation> transition) {
		if (isEmpty() || isSequentialAcquire(transition)) {
			return state;
		}
		if (SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}
		final IPredicate publishedForAcquiredLock = publishedForAcquiredLock(transition);
		if (publishedForAcquiredLock == null) {
			return state;
		}
		return conjoin(state.getFormula(), publishedForAcquiredLock.getFormula());
	}

	public IPredicate restoreProtectedVars(final IPredicate beforeInterference, final IPredicate afterInterference,
			final Set<String> observerLockset) {
		if (isEmpty() || observerLockset.isEmpty()) {
			return afterInterference;
		}
		final Term afterFormula = afterInterference.getFormula();
		if (SmtUtils.isTrueLiteral(afterFormula) || SmtUtils.isFalseLiteral(afterFormula)) {
			return afterInterference;
		}
		final Set<IProgramVar> protectedVars = varsProtectedByHeldLocks(observerLockset);
		if (protectedVars.isEmpty()) {
			return afterInterference;
		}
		final Set<TermVariable> protectedTvs = termVariablesOf(protectedVars);
		final Term withoutProtected = existentiallyRemove(afterFormula, protectedTvs);
		final Set<TermVariable> protectedTvsAndUntouchableThreadLocalTvs =
				withThreadLocalFreeVars(protectedTvs, beforeInterference);
		final IPredicate preservedProtected = retainOnly(beforeInterference, protectedTvsAndUntouchableThreadLocalTvs);
		return conjoin(withoutProtected, preservedProtected.getFormula());
	}

	private Set<TermVariable> withThreadLocalFreeVars(final Set<TermVariable> tvs, final IPredicate predicate) {
		final Set<TermVariable> result = new LinkedHashSet<>(tvs);
		for (final TermVariable tv : predicate.getFormula().getFreeVars()) {
			if (!mGlobalTvs.contains(tv)) {
				result.add(tv);
			}
		}
		return result;
	}

	public boolean isSubsumedBy(final PublishOnAcquire other, final IDomain domain) {
		for (final Entry<IProgramVar, MutexInvariant> entry : mInvariants.entrySet()) {
			final IPredicate published = entry.getValue().published();
			if (published == null) {
				continue;
			}
			final MutexInvariant otherInvariant = other.mInvariants.get(entry.getKey());
			final IPredicate otherPublished = otherInvariant == null ? null : otherInvariant.published();
			if (otherPublished == null || !domain.isSubsetEq(published, otherPublished).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}

	private boolean isSequentialAcquire(final IIcfgTransition<IcfgLocation> transition) {
		return mSequentialLocations.contains(transition.getSource());
	}

	private IPredicate publishedForAcquiredLock(final IIcfgTransition<IcfgLocation> transition) {
		final IProgramVar acquired =
				LockEdgeClassifier.acquiredLockVarFromTf(transition.getTransformula(), mLockVars);
		final MutexInvariant invariant = acquired == null ? null : mInvariants.get(acquired);
		return invariant == null ? null : invariant.published();
	}

	private Set<IProgramVar> varsProtectedByHeldLocks(final Set<String> observerLockset) {
		final Set<IProgramVar> protectedVars = new LinkedHashSet<>();
		for (final IProgramVar lock : mLockVars) {
			if (!observerLockset.contains(lock.getGloballyUniqueId())) {
				continue;
			}
			final MutexInvariant invariant = mInvariants.get(lock);
			if (invariant != null) {
				protectedVars.addAll(invariant.protectedGlobals());
			}
			protectedVars.add(lock);
		}
		return protectedVars;
	}

	private PublishOnAcquire withRecomputedPublished(
			final BiFunction<IProgramVar, MutexInvariant, IPredicate> newPublished) {
		final Map<IProgramVar, MutexInvariant> updated = new LinkedHashMap<>();
		for (final Entry<IProgramVar, MutexInvariant> entry : mInvariants.entrySet()) {
			updated.put(entry.getKey(),
					entry.getValue().withChangedPublished(newPublished.apply(entry.getKey(), entry.getValue())));
		}
		return new PublishOnAcquire(mServices, mManagedScript, mPredicateFactory, mLockVars, Map.copyOf(updated),
				mSequentialLocations, mGlobalTvs);
	}

	private IPredicate recomputeJoinedPublishEdgePostStates(final MutexInvariant invariant,
			final Map<IcfgLocation, IPredicate> locationStates, final IDomain domain,
			final BiFunction<IPredicate, IcfgEdge, IPredicate> interferenceFreePost) {
		final Set<TermVariable> protectedTvs = termVariablesOf(invariant.protectedGlobals());
		IPredicate joined = null;
		for (final IcfgEdge edge : invariant.publishEdges()) {
			final IPredicate projectedPostState =
					recomputeProjectedPostStateOf(edge, protectedTvs, locationStates, interferenceFreePost);
			if (projectedPostState != null) {
				joined = joined == null ? projectedPostState : domain.join(joined, projectedPostState);
			}
		}
		return nullIfTrivial(joined);
	}

	private IPredicate recomputeProjectedPostStateOf(final IcfgEdge edge, final Set<TermVariable> protectedTvs,
			final Map<IcfgLocation, IPredicate> locationStates,
			final BiFunction<IPredicate, IcfgEdge, IPredicate> interferenceFreePost) {
		final IPredicate sourceState = locationStates.get(edge.getSource());
		if (sourceState == null || SmtUtils.isFalseLiteral(sourceState.getFormula())) {
			return null;
		}
		final IPredicate afterEdge = interferenceFreePost.apply(sourceState, edge);
		if (SmtUtils.isFalseLiteral(afterEdge.getFormula())) {
			return null;
		}
		return retainOnly(afterEdge, protectedTvs);
	}

	private static IPredicate widenPublished(final MutexInvariant invariant, final PublishOnAcquire extracted,
			final IDomain domain, final IProgramVar lock) {
		final MutexInvariant extractedInvariant = extracted.mInvariants.get(lock);
		if (invariant.published() == null || extractedInvariant == null || extractedInvariant.published() == null) {
			return null;
		}
		return nullIfTrivial(domain.widen(invariant.published(), extractedInvariant.published()));
	}

	private static IPredicate nullIfTrivial(final IPredicate predicate) {
		return predicate != null && !SmtUtils.isTrueLiteral(predicate.getFormula()) ? predicate : null;
	}

	private IPredicate conjoin(final Term left, final Term right) {
		return mPredicateFactory.newPredicate(SmtUtils.and(mManagedScript.getScript(), left, right));
	}

	private IPredicate retainOnly(final IPredicate state, final Set<TermVariable> keptVariables) {
		final Set<TermVariable> variablesToRemove = new LinkedHashSet<>();
		for (final TermVariable freeVariable : state.getFormula().getFreeVars()) {
			if (!keptVariables.contains(freeVariable)) {
				variablesToRemove.add(freeVariable);
			}
		}
		if (variablesToRemove.isEmpty()) {
			return state;
		}
		return mPredicateFactory.newPredicate(existentiallyRemove(state.getFormula(), variablesToRemove));
	}

	private Term existentiallyRemove(final Term formula, final Set<TermVariable> removedVariables) {
		return RelationalPredicateUtils.existentiallyProject(formula, removedVariables, mServices, mManagedScript);
	}

	private static Set<TermVariable> termVariablesOf(final Set<IProgramVar> vars) {
		final Set<TermVariable> termVariables = new LinkedHashSet<>();
		for (final IProgramVar var : vars) {
			termVariables.add(var.getTermVariable());
		}
		return termVariables;
	}
}
