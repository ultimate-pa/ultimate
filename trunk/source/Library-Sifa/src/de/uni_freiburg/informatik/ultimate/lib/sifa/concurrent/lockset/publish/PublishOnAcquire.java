/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
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
	private final Set<TermVariable> mGlobalTermVariables;

	private PublishOnAcquire(final IUltimateServiceProvider services, final ManagedScript managedScript,
			final BasicPredicateFactory predicateFactory, final Set<IProgramVar> lockVars,
			final Map<IProgramVar, MutexInvariant> invariants, final Set<IcfgLocation> sequentialLocations,
			final Set<TermVariable> globalTermVariables) {
		mServices = services;
		mManagedScript = managedScript;
		mPredicateFactory = predicateFactory;
		mLockVars = Set.copyOf(lockVars);
		mInvariants = Map.copyOf(invariants);
		mSequentialLocations = Set.copyOf(sequentialLocations);
		mGlobalTermVariables = Set.copyOf(globalTermVariables);
	}

	public static PublishOnAcquire disabled() {
		return new PublishOnAcquire(null, null, null, Set.of(), Map.of(), Set.of(), Set.of());
	}

	public static PublishOnAcquire discover(final IIcfg<IcfgLocation> icfg,
			final MustLocksetAnalysis locksetInfo, final String entryProcedure,
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
		final Set<TermVariable> globalTermVariables = new LinkedHashSet<>();
		icfg.getCfgSmtToolkit().getSymbolTable().getGlobals()
				.forEach(global -> globalTermVariables.add(global.getTermVariable()));
		return new PublishOnAcquire(services, managedScript, predicateFactory, lockVars, invariants,
				sequentialLocationsOf(icfg, isSequential), globalTermVariables);
	}

	private static Predicate<IcfgLocation> onlyOwnThreadCanBeActive(final String entryProcedure,
			final ThreadActivityPreanalysis threadActivity) {
		return location -> location.getProcedure().equals(entryProcedure)
				&& threadActivity.getActiveThreadsAt(location).size() <= 1;
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

	public PublishOnAcquire recomputePublishedInvariants(final Map<IcfgLocation, IPredicate> locationStates,
			final IDomain domain, final BiFunction<IPredicate, IcfgEdge, IPredicate> interferenceFreePost) {
		if (isEmpty()) {
			return this;
		}
		return withRecomputedPublished((lock, invariant) -> recomputeJoinedPublishEdgePostStates(invariant,
				locationStates, domain, interferenceFreePost));
	}

	public PublishOnAcquire widen(final PublishOnAcquire extracted, final IDomain domain) {
		return withRecomputedPublished((lock, invariant) -> widenPublished(invariant, extracted, domain, lock));
	}

	public IPredicate applyAtAcquire(final IPredicate state,
			final IIcfgTransition<IcfgLocation> transition) {
		if (isEmpty() || isSequentialAcquire(transition) || SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}
		final IPredicate published = publishedForAcquiredLock(transition);
		return published == null ? state : conjoin(state.getFormula(), published.getFormula());
	}

	public IPredicate restoreProtectedVariables(final IPredicate beforeInterference,
			final IPredicate afterInterference, final Set<String> observerLockset) {
		if (isEmpty() || observerLockset.isEmpty()) {
			return afterInterference;
		}
		final Term afterFormula = afterInterference.getFormula();
		if (SmtUtils.isFalseLiteral(afterFormula)) {
			return afterInterference;
		}
		final Set<IProgramVar> protectedVariables = variablesProtectedByHeldLocks(observerLockset);
		if (protectedVariables.isEmpty()) {
			return afterInterference;
		}
		final Set<TermVariable> protectedTermVariables = termVariablesOf(protectedVariables);
		final Term withoutProtected = existentiallyRemove(afterFormula, protectedTermVariables);
		final Set<TermVariable> variablesToPreserve =
				withThreadLocalFreeVariables(protectedTermVariables, beforeInterference);
		final IPredicate preserved = retainOnly(beforeInterference, variablesToPreserve);
		return conjoin(withoutProtected, preserved.getFormula());
	}

	private Set<TermVariable> withThreadLocalFreeVariables(final Set<TermVariable> variables,
			final IPredicate predicate) {
		final Set<TermVariable> result = new LinkedHashSet<>(variables);
		for (final TermVariable freeVariable : predicate.getFormula().getFreeVars()) {
			if (!mGlobalTermVariables.contains(freeVariable)) {
				result.add(freeVariable);
			}
		}
		return result;
	}

	public boolean isSubsumedBy(final PublishOnAcquire other, final IDomain domain) {
		for (final Entry<IProgramVar, MutexInvariant> entry : mInvariants.entrySet()) {
			final IPredicate published = entry.getValue().published();
			final MutexInvariant otherInvariant = other.mInvariants.get(entry.getKey());
			final IPredicate otherPublished = otherInvariant == null ? null : otherInvariant.published();
			if (!isPublishedStateSubsumed(published, otherPublished, domain)) {
				return false;
			}
		}
		return true;
	}

	private static boolean isPublishedStateSubsumed(final IPredicate published,
			final IPredicate otherPublished, final IDomain domain) {
		if (published == null) {
			return otherPublished == null;
		}
		return otherPublished == null
				|| domain.isSubsetEq(published, otherPublished).isTrueForAbstraction();
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

	private Set<IProgramVar> variablesProtectedByHeldLocks(final Set<String> observerLockset) {
		final Set<IProgramVar> protectedVariables = new LinkedHashSet<>();
		for (final IProgramVar lock : mLockVars) {
			if (!observerLockset.contains(lock.getGloballyUniqueId())) {
				continue;
			}
			final MutexInvariant invariant = mInvariants.get(lock);
			if (invariant != null) {
				protectedVariables.addAll(invariant.protectedGlobals());
			}
			protectedVariables.add(lock);
		}
		return protectedVariables;
	}

	private PublishOnAcquire withRecomputedPublished(
			final BiFunction<IProgramVar, MutexInvariant, IPredicate> newPublished) {
		final Map<IProgramVar, MutexInvariant> updated = new LinkedHashMap<>();
		for (final Entry<IProgramVar, MutexInvariant> entry : mInvariants.entrySet()) {
			updated.put(entry.getKey(),
					entry.getValue().withChangedPublished(newPublished.apply(entry.getKey(), entry.getValue())));
		}
		return new PublishOnAcquire(mServices, mManagedScript, mPredicateFactory, mLockVars, updated,
				mSequentialLocations, mGlobalTermVariables);
	}

	private IPredicate recomputeJoinedPublishEdgePostStates(final MutexInvariant invariant,
			final Map<IcfgLocation, IPredicate> locationStates, final IDomain domain,
			final BiFunction<IPredicate, IcfgEdge, IPredicate> interferenceFreePost) {
		final Set<TermVariable> protectedTermVariables = termVariablesOf(invariant.protectedGlobals());
		IPredicate joined = null;
		for (final IcfgEdge edge : invariant.publishEdges()) {
			final IPredicate projectedPostState = recomputeProjectedPostStateOf(edge, protectedTermVariables,
					locationStates, interferenceFreePost);
			if (projectedPostState != null) {
				joined = joined == null ? projectedPostState : domain.join(joined, projectedPostState);
			}
		}
		return nullIfTrivial(joined);
	}

	private IPredicate recomputeProjectedPostStateOf(final IcfgEdge edge,
			final Set<TermVariable> protectedTermVariables,
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
		return retainOnly(afterEdge, protectedTermVariables);
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

	private static Set<TermVariable> termVariablesOf(final Set<IProgramVar> variables) {
		final Set<TermVariable> termVariables = new LinkedHashSet<>();
		for (final IProgramVar variable : variables) {
			termVariables.add(variable.getTermVariable());
		}
		return termVariables;
	}
}
