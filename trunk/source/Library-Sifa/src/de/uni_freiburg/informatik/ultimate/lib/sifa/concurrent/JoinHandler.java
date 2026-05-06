package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.HashSet;
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
	private ThreadAnalysisContext mThreadContext;
	private ThreadActivityPreanalysis mActivityPreanalysis;

	JoinHandler(final ConcurrentSymbolicTools tools, final IUltimateServiceProvider services,
			final IIcfg<IcfgLocation> icfg) {
		mTools = tools;
		mServices = services;
		mIcfg = icfg;
	}

	void configureStaticAnalysis(final GhostVariableManager ghostVariables) {
		mGhostVariables = ghostVariables;
	}

	void configureForThread(final ThreadAnalysisContext context, final ThreadActivityPreanalysis activityPreanalysis) {
		mThreadContext = context;
		mActivityPreanalysis = activityPreanalysis;
	}

	// Projects out variables assigned by the join's LHS from the post-state.
	IPredicate projectJoinAssignedVars(final IPredicate state, final IIcfgTransition<IcfgLocation> transition) {
		if (state instanceof BucketPredicate) {
			return mTools.mapBuckets(state, bucket -> projectJoinAssignedVars(bucket, transition));
		}
		if (!(transition instanceof final IIcfgJoinTransitionThreadCurrent<?> join)
				|| SmtUtils.isFalseLiteral(state.getFormula()) || SmtUtils.isTrueLiteral(state.getFormula())) {
			return state;
		}
		final Set<TermVariable> assigned = new HashSet<>();
		for (final IProgramVar lhs : join.getJoinSmtArguments().getAssignmentLhs()) {
			if (lhs != null) {
				assigned.add(lhs.getTermVariable());
			}
		}
		if (assigned.isEmpty()) {
			return state;
		}
		final Term projected = RelationalPredicateUtils.existentiallyProject(state.getFormula(), assigned, mServices,
				mTools.getManagedScript());
		return mTools.predicate(projected);
	}

	// Conjoins the joined thread's exit state (projected to shared variables) into the current state.
	IPredicate importJoinedThreadExitSummary(final IPredicate state, final IIcfgTransition<IcfgLocation> transition) {
		if (!(transition instanceof final IIcfgJoinTransitionThreadCurrent<?> join)
				|| mActivityPreanalysis == null || mThreadContext == null) {
			return state;
		}
		@SuppressWarnings("unchecked")
		final IIcfgJoinTransitionThreadCurrent<IcfgLocation> typedJoin =
				(IIcfgJoinTransitionThreadCurrent<IcfgLocation>) join;
		final String joinedThread = mActivityPreanalysis.getJoinedThreadForJoin(typedJoin);
		if (joinedThread == null) {
			return state;
		}
		final IcfgLocation exitLoc = mIcfg.getProcedureExitNodes().get(joinedThread);
		if (exitLoc == null) {
			return state;
		}
		final IPredicate exitState = mThreadContext.locationPredicates().get(exitLoc);
		if (exitState == null || SmtUtils.isTrueLiteral(exitState.getFormula())
				|| SmtUtils.isFalseLiteral(exitState.getFormula())) {
			return state;
		}
		final IPredicate sharedExit = projectToSharedExitVars(exitState, joinedThread);
		if (SmtUtils.isFalseLiteral(sharedExit.getFormula())) {
			return state;
		}
		final IPredicate atExit = mTools.addLocationUpdateForThread(state, joinedThread, exitLoc);
		final Term sharedExitFormula = sharedExit.getFormula();
		return mTools.mapBuckets(atExit,
				bucket -> mTools.predicate(SmtUtils.and(mTools.getScript(), bucket.getFormula(), sharedExitFormula)));
	}

	private IPredicate projectToSharedExitVars(final IPredicate state, final String joinedThread) {
		final Set<TermVariable> toProject = state.getVars().stream()
				.filter(var -> !var.isGlobal())
				.map(IProgramVar::getTermVariable)
				.collect(Collectors.toCollection(HashSet::new));
		if (mGhostVariables != null) {
			toProject.addAll(mGhostVariables.getLocationTermVariables());
			toProject.remove(mGhostVariables.getLocationTermVar(joinedThread));
		}
		if (toProject.isEmpty()) {
			return state;
		}
		final Term projected = RelationalPredicateUtils.existentiallyProject(state.getFormula(), toProject,
				mServices, mTools.getManagedScript());
		return mTools.predicate(projected);
	}
}
