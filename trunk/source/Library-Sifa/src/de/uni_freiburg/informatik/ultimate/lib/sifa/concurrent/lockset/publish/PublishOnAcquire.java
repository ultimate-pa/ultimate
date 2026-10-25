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

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.threadactivity.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.threadanalysis.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * This class uses mutexes to improve what the analysis knows about shared variables. We only do this for variables that
 * all threads protect with the same mutex. After the normal analysis finishes, we collect the possible values before
 * threads start and after each unlock. These are the values a thread can see when it locks that mutex. We analyze the
 * threads once more using these results. The collected results stay the same during this last run.
 */
public final class PublishOnAcquire {

	private record Publication(Set<IProgramVar> protectedGlobals, Set<IcfgEdge> publishEdges) {
	}

	private final IUltimateServiceProvider mServices;
	private final MustLocksetAnalysis mLocks;
	private final ConcurrentSymbolicTools mTools;
	private final Map<IProgramVar, Publication> mPublications = new LinkedHashMap<>();
	private final Map<IProgramVar, IPredicate> mPublishedStates = new LinkedHashMap<>();

	public PublishOnAcquire(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg,
			final MustLocksetAnalysis locks, final ThreadActivityPreanalysis activity,
			final ConcurrentSymbolicTools tools) {
		mServices = services;
		mLocks = locks;
		mTools = tools;
		if (locks.getLockVars().isEmpty()) {
			return;
		}
		final List<IcfgEdge> edges =
				IcfgUtils.getAllLocations(icfg).flatMap(location -> location.getOutgoingEdges().stream()).toList();
		final Set<IProgramVar> globals = new LinkedHashSet<>(icfg.getCfgSmtToolkit().getSymbolTable().getGlobals());
		globals.removeAll(locks.getLockVars());
		for (final IProgramVar lock : locks.getLockVars()) {
			final Set<IProgramVar> protectedGlobals = findProtectedGlobals(lock, globals, edges, activity);
			final Set<IcfgEdge> publishEdges = findPublishEdges(lock, edges, activity);
			if (!protectedGlobals.isEmpty() && !publishEdges.isEmpty()) {
				mPublications.put(lock, new Publication(protectedGlobals, publishEdges));
			}
		}
	}

	private Set<IProgramVar> findProtectedGlobals(final IProgramVar lock, final Set<IProgramVar> globals,
			final List<IcfgEdge> edges, final ThreadActivityPreanalysis activity) {
		final Set<IProgramVar> protectedGlobals = new LinkedHashSet<>(globals);
		for (final IcfgEdge edge : edges) {
			final IcfgLocation source = edge.getSource();
			if (activity.hasOtherActiveThreadsAt(source)
					&& !mLocks.mustLocksetAt(source).contains(lock.getGloballyUniqueId())) {
				protectedGlobals.removeAll(InterferenceUtils.getChangedGlobals(edge.getTransformula(),
						InterferenceUtils.getAdditionalChangedGlobals(edge)));
			}
		}
		return protectedGlobals;
	}

	private Set<IcfgEdge> findPublishEdges(final IProgramVar lock, final List<IcfgEdge> edges,
			final ThreadActivityPreanalysis activity) {
		final Set<IcfgEdge> publishEdges = new LinkedHashSet<>();
		for (final IcfgEdge edge : edges) {
			final boolean startsThread = !activity.hasOtherActiveThreadsAt(edge.getSource())
					&& edge instanceof IIcfgForkTransitionThreadCurrent<?>;
			final boolean heldBefore = mLocks.mustLocksetAt(edge.getSource()).contains(lock.getGloballyUniqueId());
			final boolean heldAfter = mLocks.mustLocksetAt(edge.getTarget()).contains(lock.getGloballyUniqueId());
			// A thread might lock the mutex before any other thread has unlocked it.
			// We include the initial values because the thread could see them in that case.
			if (startsThread || heldBefore && !heldAfter) {
				publishEdges.add(edge);
			}
		}
		return publishEdges;
	}

	public Set<IcfgLocation> getPublishSources(final String threadId) {
		return mPublications.values().stream().flatMap(publication -> publication.publishEdges().stream())
				.map(IcfgEdge::getSource).filter(source -> source.getProcedure().equals(threadId))
				.collect(Collectors.toSet());
	}

	/**
	 * We use results from the completed analysis to collect the values a thread may see when it locks a mutex. If a
	 * result is missing, we assume that the shared variables may have any value.
	 */
	public boolean collectPublishedStates(final Map<IcfgLocation, IPredicate> invariants, final IDomain domain) {
		for (final var entry : mPublications.entrySet()) {
			IPredicate publishedState = mTools.bottom();
			for (final IcfgEdge edge : entry.getValue().publishEdges()) {
				final IPredicate sourceState = invariants.get(edge.getSource());
				final IPredicate postState =
						sourceState == null ? mTools.top() : mTools.postWithoutInterference(sourceState, edge);
				publishedState = domain.join(publishedState,
						projectToProtectedGlobals(postState, entry.getValue().protectedGlobals()));
			}
			if (!SmtUtils.isTrueLiteral(publishedState.getFormula())) {
				mPublishedStates.put(entry.getKey(), publishedState);
			}
		}
		return !mPublishedStates.isEmpty();
	}

	public IPredicate applyAtAcquire(final IPredicate state, final IIcfgTransition<IcfgLocation> transition) {
		IPredicate result = state;
		for (final var entry : mPublishedStates.entrySet()) {
			final IProgramVar lock = entry.getKey();
			if (mLocks.mustLocksetAt(transition.getTarget()).contains(lock.getGloballyUniqueId())
					&& !mLocks.mustLocksetAt(transition.getSource()).contains(lock.getGloballyUniqueId())) {
				result = mTools.and(result, entry.getValue());
			}
		}
		return result;
	}

	private IPredicate projectToProtectedGlobals(final IPredicate state, final Set<IProgramVar> protectedGlobals) {
		final Set<TermVariable> protectedTerms =
				protectedGlobals.stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());
		final Set<TermVariable> variablesToRemove = Arrays.stream(state.getFormula().getFreeVars())
				.filter(variable -> !protectedTerms.contains(variable)).collect(Collectors.toSet());
		final Term projectedFormula = RelationalPredicateUtils.existentiallyProject(state.getFormula(),
				variablesToRemove, mServices, mTools.getManagedScript());
		return mTools.getFactory().newPredicate(projectedFormula);
	}
}
