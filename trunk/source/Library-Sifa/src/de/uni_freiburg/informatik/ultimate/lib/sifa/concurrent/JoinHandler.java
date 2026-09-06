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
package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

class JoinHandler {

	private final ConcurrentSymbolicTools mTools;
	private final IUltimateServiceProvider mServices;
	private final IIcfg<IcfgLocation> mIcfg;
	private GhostVariableManager mGhostVariables;
	private final Map<String, Set<TermVariable>> mGhostVarsToProjectCache = new HashMap<>();
	private final IdentityHashMap<IIcfgJoinTransitionThreadCurrent<?>, Set<TermVariable>> mAssignedVarsCache =
			new IdentityHashMap<>();
	private final IdentityHashMap<IIcfgJoinTransitionThreadCurrent<?>, Set<TermVariable>> mAssignedGlobalVarsCache =
			new IdentityHashMap<>();

	JoinHandler(final ConcurrentSymbolicTools tools, final IUltimateServiceProvider services,
			final IIcfg<IcfgLocation> icfg) {
		mTools = tools;
		mServices = services;
		mIcfg = icfg;
	}

	void configureStaticAnalysis(final GhostVariableManager ghostVariables) {
		mGhostVariables = ghostVariables;
	}

	IPredicate extractJoinedThreadGlobalExitStateAndIntersect(final IPredicate state,
			final IIcfgTransition<IcfgLocation> transition, final ThreadAnalysisContext threadContext,
			final ThreadActivityPreanalysis activityPreanalysis) {
		if (!(transition instanceof final IIcfgJoinTransitionThreadCurrent<?> join)) {
			return state;
		}
		final String joinedThread = activityPreanalysis
				.getJoinedThreadForJoin((IIcfgJoinTransitionThreadCurrent<IcfgLocation>) join);
		if (joinedThread == null) {
			return state;
		}
		final IcfgLocation exitLoc = mIcfg.getProcedureExitNodes().get(joinedThread);
		if (exitLoc == null) {
			return state;
		}
		final IPredicate globalizedExit = globalExitState(threadContext, exitLoc, joinedThread, join);
		if (globalizedExit == null) {
			return state;
		}
		return intersectStateAndExitLocationState(state, joinedThread, exitLoc, globalizedExit);
	}

	private IPredicate globalExitState(final ThreadAnalysisContext threadContext, final IcfgLocation exitLoc,
			final String joinedThread, final IIcfgJoinTransitionThreadCurrent<?> join) {
		final IPredicate exitState = threadContext.locationPredicates().get(exitLoc);
		if (exitState == null || isTrivial(exitState)) {
			return null;
		}
		final IPredicate projected = projectToGlobalVars(exitState, joinedThread, join);
		return SmtUtils.isFalseLiteral(projected.getFormula()) ? null : projected;
	}

	private static boolean isTrivial(final IPredicate pred) {
		return SmtUtils.isTrueLiteral(pred.getFormula()) || SmtUtils.isFalseLiteral(pred.getFormula());
	}

	private IPredicate projectToGlobalVars(final IPredicate state, final String joinedThread,
			final IIcfgJoinTransitionThreadCurrent<?> join) {
		final Set<TermVariable> varsToProject = new HashSet<>(ghostLocVarsToProject(joinedThread));
		varsToProject.addAll(collectAssignedGlobalTermVars(join));
		return InterferenceUtils.projectToGlobalState(state, varsToProject, mServices, mTools.getManagedScript(),
				mTools::predicate);
	}

	private Set<TermVariable> ghostLocVarsToProject(final String joinedThread) {
		if (mGhostVariables == null) {
			return Set.of();
		}
		return mGhostVarsToProjectCache.computeIfAbsent(joinedThread, k -> {
			final Set<TermVariable> extra = new HashSet<>(mGhostVariables.getLocationTermVariables());
			extra.remove(mGhostVariables.getLocationTermVar(k));
			return Set.copyOf(extra);
		});
	}

	private IPredicate intersectStateAndExitLocationState(final IPredicate state, final String joinedThread,
			final IcfgLocation exitLoc, final IPredicate sharedExit) {
		final IPredicate atExit = mTools.addLocationUpdateForThread(state, joinedThread, exitLoc);
		final Term exitFormula = sharedExit.getFormula();
		return mTools.predicate(SmtUtils.and(mTools.getScript(), atExit.getFormula(), exitFormula));
	}

	IPredicate projectJoinAssignedVars(final IPredicate state, final IIcfgTransition<IcfgLocation> transition) {
		if (!(transition instanceof final IIcfgJoinTransitionThreadCurrent<?> join) || isTrivial(state)) {
			return state;
		}
		final Set<TermVariable> assigned = collectAssignedTermVars(join);
		return assigned.isEmpty() ? state
				: mTools.predicate(RelationalPredicateUtils.existentiallyProject(state.getFormula(), assigned,
						mServices, mTools.getManagedScript()));
	}

	private Set<TermVariable> collectAssignedTermVars(final IIcfgJoinTransitionThreadCurrent<?> join) {
		return mAssignedVarsCache.computeIfAbsent(join, k -> k.getJoinSmtArguments().getAssignmentLhs().stream()
				.filter(Objects::nonNull).map(IProgramVar::getTermVariable).collect(Collectors.toUnmodifiableSet()));
	}

	private Set<TermVariable> collectAssignedGlobalTermVars(final IIcfgJoinTransitionThreadCurrent<?> join) {
		return mAssignedGlobalVarsCache.computeIfAbsent(join,
				k -> k.getJoinSmtArguments().getAssignmentLhs().stream().filter(Objects::nonNull)
						.filter(IProgramVar::isGlobal).map(IProgramVar::getTermVariable)
						.collect(Collectors.toUnmodifiableSet()));
	}

}
