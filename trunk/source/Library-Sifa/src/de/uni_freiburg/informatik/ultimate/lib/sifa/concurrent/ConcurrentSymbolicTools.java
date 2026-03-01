package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing.LocationMarkerTransition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.ObservedThreadStateRecorder;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceCollection;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.InitialStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ConcurrentSymbolicTools extends SymbolicTools {

	private final IUltimateServiceProvider mServices;
	private final ThreadModularSifaSettings mSettings;
	private final InitialStateFactory mInitialStateFactory;
	private GhostVariableManager mGhostVariables;
	private ThreadActivityPreanalysis mThreadActivityPreanalysis;
	private ThreadAnalysisContext mThreadContext;
	private ObservedThreadStateRecorder mObservedStateRecorder;

	public ConcurrentSymbolicTools(final IUltimateServiceProvider services, final SifaStats stats,
			final IIcfg<IcfgLocation> icfg, final SimplificationTechnique simplification,
			final IIcfgSymbolTable symbolTable, final ThreadModularSifaSettings settings) {
		super(services, stats, icfg, simplification, symbolTable);
		mServices = services;
		mSettings = settings;
		mInitialStateFactory = new InitialStateFactory(this, icfg);
	}

	public ThreadModularSifaSettings getSettings() {
		return mSettings;
	}

	public IUltimateServiceProvider getServices() {
		return mServices;
	}

	public GhostVariableManager getGhostVariables() {
		return mGhostVariables;
	}

	public ThreadActivityPreanalysis getThreadActivityPreanalysis() {
		return mThreadActivityPreanalysis;
	}

	public void rememberThreadLocationState(final IcfgLocation location, final IPredicate state) {
		mObservedStateRecorder.recordObservedState(location, state);
	}

	public Map<IcfgLocation, IPredicate> getObservedThreadLocationStates() {
		return mObservedStateRecorder.snapshotObservedStates();
	}

	public void configureStaticAnalysis(final GhostVariableManager ghostVariables,
			final ThreadActivityPreanalysis activityPreanalysis) {
		mGhostVariables = ghostVariables;
		mThreadActivityPreanalysis = activityPreanalysis;
		mInitialStateFactory.configureStaticAnalysis(ghostVariables);
	}

	private static record ThreadAnalysisContext(String threadId, InterferenceCollection interferences,
			IDomain interferenceDomain, RelationalPredicatePostcondition postcondition, boolean includeSelfInterference,
			List<String> sortedInterferenceThreadIds,
			Map<IcfgLocation, List<IInterference>> applicableInterferencesByLocation) {
	}

	public void configureForThread(final String threadId, final InterferenceCollection interferences,
			final Map<IcfgLocation, IPredicate> locationPredicates, final IDomain analysisDomain,
			final IDomain interferenceDomain, final RelationalPredicatePostcondition postcondition) {
		final List<String> sortedInterferenceThreadIds = new ArrayList<>(interferences.getThreadIds());
		Collections.sort(sortedInterferenceThreadIds);
		final boolean includeSelfInterference = mThreadActivityPreanalysis.getMultiForkedThreads().contains(threadId);
		mThreadContext = new ThreadAnalysisContext(threadId, interferences, interferenceDomain, postcondition,
				includeSelfInterference, List.copyOf(sortedInterferenceThreadIds), new HashMap<>());
		mObservedStateRecorder = new ObservedThreadStateRecorder(interferenceDomain, mGhostVariables);
		mInitialStateFactory.configureForThread(locationPredicates, analysisDomain);
	}

	@Override
	public IPredicate post(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		mObservedStateRecorder.recordTransitionInputState(transition, input);
		final IPredicate spResult = super.post(input, transition);
		final IPredicate joinAdjusted = overapproximateJoinAssignment(spResult, transition);
		return updateGhostvarsAndApplyInterferences(joinAdjusted, transition);
	}

	@Override
	public IPredicate postCall(final IPredicate input, final IIcfgCallTransition<IcfgLocation> transition) {
		throw new UnsupportedOperationException();
	}

	@Override
	public IPredicate postReturn(final IPredicate inputBeforeCall, final IPredicate inputBeforeReturn,
			final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> returnTransition) {
		throw new UnsupportedOperationException();
	}

	public IPredicate postNoOpTransition(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		if (transition instanceof LocationMarkerTransition) {
			mObservedStateRecorder.recordTransitionInputState(transition, input);
			return applyInterferences(input, transition.getTarget());
		}
		return post(input, transition);
	}

	private IPredicate overapproximateJoinAssignment(final IPredicate state,
			final IIcfgTransition<IcfgLocation> transition) {
		if (!(transition instanceof final IIcfgJoinTransitionThreadCurrent<?> joinCurrent)) {
			return state;
		}
		final List<IProgramVar> assignmentLhs = joinCurrent.getJoinSmtArguments().getAssignmentLhs();
		if (assignmentLhs.isEmpty() || SmtUtils.isFalseLiteral(state.getFormula()) || SmtUtils.isTrueLiteral(state.getFormula())) {
			return state;
		}
		final Set<TermVariable> assignedTermVars = new HashSet<>();
		for (final IProgramVar lhs : assignmentLhs) {
			if (lhs != null) {
				assignedTermVars.add(lhs.getTermVariable());
			}
		}
		if (assignedTermVars.isEmpty()) {
			return state;
		}
		final Term projected = RelationalPredicateUtils.existentiallyProject(state.getFormula(), assignedTermVars,
				mServices, getManagedScript());
		return predicate(projected);
	}

	public IPredicate applyInterferences(final IPredicate state, final IcfgLocation location) {
		final ThreadAnalysisContext threadContext = mThreadContext;
		final InterferenceCollection interferences = threadContext.interferences();
		if (hasNoInterferencesToApply(state, interferences)) {
			return state;
		}

		final IDomain domain = threadContext.interferenceDomain();
		final RelationalPredicatePostcondition postcondition = threadContext.postcondition();
		final List<IInterference> applicableInterferences = getApplicableInterferencesForLocation(threadContext,
				location);
		if (applicableInterferences.isEmpty()) {
			return state;
		}
		return applyPerInterferenceFixpointRounds(state, domain, postcondition, applicableInterferences);
	}

	private IPredicate applyPerInterferenceFixpointRounds(final IPredicate state, final IDomain domain,
			final RelationalPredicatePostcondition postcondition, final List<IInterference> applicableInterferences) {
		IPredicate current = state;
		while (true) {
			final IPredicate roundStart = current;
			boolean changedInRound = false;
			for (final IInterference itf : applicableInterferences) {
				final IPredicate next = itf.applyUntilFixpoint(current, domain, postcondition, mGhostVariables,
						getManagedScript(), getFactory(), mSettings.innerWideningThreshold(), getStats());
				if (doesNotGrowState(domain, next, current)) {
					continue;
				}
				current = next;
				changedInRound = true;
			}
			if (shouldStopInterferenceRound(changedInRound, domain, current, roundStart)) {
				return current;
			}
		}
	}

	private static boolean hasNoInterferencesToApply(final IPredicate state,
			final InterferenceCollection interferences) {
		return interferences.isEmpty() || isTrueOrFalse(state);
	}

	private static boolean isTrueOrFalse(final IPredicate predicate) {
		return SmtUtils.isTrueLiteral(predicate.getFormula()) || SmtUtils.isFalseLiteral(predicate.getFormula());
	}

	private static boolean doesNotGrowState(final IDomain domain, final IPredicate candidate,
			final IPredicate currentState) {
		return domain.isSubsetEq(candidate, currentState).isTrueForAbstraction();
	}

	private static boolean shouldStopInterferenceRound(final boolean changedInRound, final IDomain domain,
			final IPredicate currentState, final IPredicate roundStartState) {
		return !changedInRound || doesNotGrowState(domain, currentState, roundStartState);
	}

	private List<IInterference> getApplicableInterferencesForLocation(final ThreadAnalysisContext threadContext,
			final IcfgLocation location) {
		final Map<IcfgLocation, List<IInterference>> cache = threadContext.applicableInterferencesByLocation();
		final List<IInterference> cached = cache.get(location);
		if (cached != null) {
			return cached;
		}
		final List<IInterference> computed = computeApplicableInterferencesForLocation(threadContext, location);
		cache.put(location, computed);
		return computed;
	}

	private List<IInterference> computeApplicableInterferencesForLocation(final ThreadAnalysisContext threadContext,
			final IcfgLocation location) {
		final List<IInterference> applicable = new ArrayList<>();
		final String threadId = threadContext.threadId();
		final boolean includeSelfInterference = threadContext.includeSelfInterference();
		for (final String otherThreadId : threadContext.sortedInterferenceThreadIds()) {
			if (isDisallowedSelfInterference(threadId, otherThreadId, includeSelfInterference)) {
				continue;
			}
			if (isInactiveAtLocation(location, otherThreadId)) {
				continue;
			}
			final IInterference itf = threadContext.interferences().getInterferenceForThread(otherThreadId);
			if (isMissingOrTrivialInterference(itf)) {
				continue;
			}
			applicable.add(itf);
		}
		return List.copyOf(applicable);
	}

	private static boolean isDisallowedSelfInterference(final String currentThreadId, final String candidateThreadId,
			final boolean includeSelfInterference) {
		return candidateThreadId.equals(currentThreadId) && !includeSelfInterference;
	}

	private boolean isInactiveAtLocation(final IcfgLocation location, final String threadId) {
		return !mThreadActivityPreanalysis.mayBeActiveAt(location, threadId);
	}

	private static boolean isMissingOrTrivialInterference(final IInterference interference) {
		return interference == null || interference.isTrivial();
	}

	private IPredicate updateGhostvarsAndApplyInterferences(final IPredicate state,
			final IIcfgTransition<IcfgLocation> transition) {
		IPredicate updated = addLocationUpdate(state, transition);
		if (hasGhostLocationTracking() && transition instanceof final IIcfgForkTransitionThreadCurrent<?> fork) {
			final String forkedThreadId = fork.getNameOfForkedProcedure();
			final IcfgLocation forkedEntry = mGhostVariables.getEntryLocation(forkedThreadId);
			updated = addLocationUpdateForThread(updated, forkedThreadId, forkedEntry);
		}
		if (!shouldApplyInterferencesOnTransition(transition)) {
			return updated;
		}
		return applyInterferences(updated, transition.getTarget());
	}

	private IPredicate addLocationUpdate(final IPredicate postState, final IIcfgTransition<IcfgLocation> transition) {
		return addLocationUpdateForThread(postState, mThreadContext.threadId(), transition.getTarget());
	}

	public IPredicate addLocationUpdateForThread(final IPredicate postState, final String threadId,
			final IcfgLocation targetLocation) {
		if (!hasGhostLocationTracking()) {
			return postState;
		}
		if (SmtUtils.isFalseLiteral(postState.getFormula())) {
			return postState;
		}

		final TermVariable currentLocTv = mGhostVariables.getLocationTermVar(threadId);
		final Term locConstraint = mGhostVariables.createLocationConstraint(threadId, targetLocation);
		if (SmtUtils.isTrueLiteral(postState.getFormula())) {
			return predicate(locConstraint);
		}

		final Term projected = RelationalPredicateUtils.existentiallyProject(postState.getFormula(),
				Set.of(currentLocTv), mServices, getManagedScript());
		final Term combined = SmtUtils.and(getScript(), projected, locConstraint);
		return predicate(combined);
	}

	private boolean hasGhostLocationTracking() {
		return mGhostVariables != null;
	}

	private static boolean shouldApplyInterferencesOnTransition(final IIcfgTransition<IcfgLocation> transition) {
		return isForkOrJoinTransition(transition) || readsOrWritesGlobalVariables(transition);
	}

	private static boolean isForkOrJoinTransition(final IIcfgTransition<IcfgLocation> transition) {
		return transition instanceof IIcfgForkTransitionThreadCurrent<?>
				|| transition instanceof IIcfgJoinTransitionThreadCurrent<?>;
	}

	private static boolean readsOrWritesGlobalVariables(final IIcfgTransition<IcfgLocation> transition) {
		final var transformula = transition.getTransformula();
		if (transformula == null) {
			return false;
		}
		return transformula.getInVars().keySet().stream().anyMatch(var -> var.isGlobal())
				|| transformula.getOutVars().keySet().stream().anyMatch(var -> var.isGlobal());
	}

	public IPredicate getInitialStatePredicate(final String threadId) {
		return mInitialStateFactory.getInitialStatePredicate(threadId);
	}

}
