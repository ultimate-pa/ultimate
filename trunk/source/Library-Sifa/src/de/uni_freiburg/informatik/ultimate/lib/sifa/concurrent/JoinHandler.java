package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.BucketPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

// Handles the two join-specific state transformations in post(): variable projection and exit summary import.
class JoinHandler {

	private final ConcurrentSymbolicTools mTools;
	private final IUltimateServiceProvider mServices;
	private final IIcfg<IcfgLocation> mIcfg;
	private GhostVariableManager mGhostVariables;

	JoinHandler(final ConcurrentSymbolicTools tools, final IUltimateServiceProvider services,
			final IIcfg<IcfgLocation> icfg) {
		mTools = tools;
		mServices = services;
		mIcfg = icfg;
	}

	void configureStaticAnalysis(final GhostVariableManager ghostVariables) {
		mGhostVariables = ghostVariables;
	}

	IPredicate extractJoinedThreadGlobalExitState(final IPredicate state,
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
		final IPredicate sharedExit = globalExitState(threadContext, exitLoc, joinedThread);
		if (sharedExit == null) {
			return state;
		}
		return intersectStateAndExitLocationState(state, joinedThread, exitLoc, sharedExit);
	}

	// Returns the exit state of the joined thread projected to global variables, or null if trivial/absent.
	private IPredicate globalExitState(final ThreadAnalysisContext threadContext, final IcfgLocation exitLoc,
			final String joinedThread) {
		final IPredicate exitState = threadContext.locationPredicates().get(exitLoc);
		if (exitState == null || isTrivial(exitState)) {
			return null;
		}
		final IPredicate projected = projectToGlobalVars(exitState, joinedThread);
		return SmtUtils.isFalseLiteral(projected.getFormula()) ? null : projected;
	}

	private IPredicate projectToGlobalVars(final IPredicate state, final String joinedThread) {
		return InterferenceUtils.projectToGlobalState(state, ghostLocVarsToProject(joinedThread), mServices,
				mTools.getManagedScript(), mTools::predicate);
	}

	private static boolean isTrivial(final IPredicate pred) {
		return SmtUtils.isTrueLiteral(pred.getFormula()) || SmtUtils.isFalseLiteral(pred.getFormula());
	}

	private IPredicate intersectStateAndExitLocationState(final IPredicate state, final String joinedThread, final IcfgLocation exitLoc,
			final IPredicate sharedExit) {
		final IPredicate atExit = mTools.addLocationUpdateForThread(state, joinedThread, exitLoc);
		final Term exitFormula = sharedExit.getFormula();
		return mTools.mapBuckets(atExit,
				bucket -> mTools.predicate(SmtUtils.and(mTools.getScript(), bucket.getFormula(), exitFormula)));
	}

	private Set<TermVariable> ghostLocVarsToProject(final String joinedThread) {
		if (mGhostVariables == null) {
			return Set.of();
		}
		final Set<TermVariable> extra = new HashSet<>(mGhostVariables.getLocationTermVariables());
		extra.remove(mGhostVariables.getLocationTermVar(joinedThread));
		return extra;
	}

	IPredicate projectJoinAssignedVars(final IPredicate state, final IIcfgTransition<IcfgLocation> transition) {
		if (state instanceof BucketPredicate) {
			return mTools.mapBuckets(state, bucket -> projectJoinAssignedVars(bucket, transition));
		}
		if (!(transition instanceof final IIcfgJoinTransitionThreadCurrent<?> join) || isTrivial(state)) {
			return state;
		}
		final Set<TermVariable> assigned = collectAssignedTermVars(join);
		return assigned.isEmpty() ? state : mTools.predicate(RelationalPredicateUtils.existentiallyProject(
				state.getFormula(), assigned, mServices, mTools.getManagedScript()));
	}

	private Set<TermVariable> collectAssignedTermVars(final IIcfgJoinTransitionThreadCurrent<?> join) {
		return join.getJoinSmtArguments().getAssignmentLhs().stream().filter(Objects::nonNull)
				.map(IProgramVar::getTermVariable).collect(Collectors.toCollection(HashSet::new));
	}

}
