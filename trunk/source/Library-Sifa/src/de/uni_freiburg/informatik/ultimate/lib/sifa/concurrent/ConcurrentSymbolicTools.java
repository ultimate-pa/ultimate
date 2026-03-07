package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
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

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final ThreadModularSifaSettings mSettings;
	private final InitialStateFactory mInitialStateFactory;
	private GhostVariableManager mGhostVariables;
	private ThreadActivityPreanalysis mThreadActivityPreanalysis;
	private ThreadAnalysisContext mThreadContext;
	private ObservedThreadStateRecorder mObservedStateRecorder;
	// join-current -> join-other edges (one per thread instance)
	private final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, List<IIcfgJoinTransitionThreadOther<IcfgLocation>>> mJoinOtherByJoinCurrent;

	public ConcurrentSymbolicTools(final IUltimateServiceProvider services, final SifaStats stats,
			final IIcfg<IcfgLocation> icfg, final SimplificationTechnique simplification,
			final IIcfgSymbolTable symbolTable, final ThreadModularSifaSettings settings) {
		super(services, stats, icfg, simplification, symbolTable);
		mLogger = services.getLoggingService().getLogger(ConcurrentSymbolicTools.class);
		mServices = services;
		mSettings = settings;
		mInitialStateFactory = new InitialStateFactory(this, icfg);
		mJoinOtherByJoinCurrent = buildJoinOtherMap(icfg);
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
		return updateGhostvarsAndApplyInterferences(spResult, transition);
	}

	@Override
	public IPredicate postCall(final IPredicate input, final IIcfgCallTransition<IcfgLocation> transition) {
		mLogger.error("Thread-modular SIFA encountered a procedure call at %s. Procedure calls are not supported; "
				+ "enable procedure inlining in the RCFG builder settings.", transition.getSource());
		throw new UnsupportedOperationException("Thread-modular SIFA does not support procedure calls (found at "
				+ transition.getSource() + "). Enable procedure inlining or restrict to fork/join concurrency.");
	}

	@Override
	public IPredicate postReturn(final IPredicate inputBeforeCall, final IPredicate inputBeforeReturn,
			final IIcfgReturnTransition<IcfgLocation, IIcfgCallTransition<IcfgLocation>> returnTransition) {
		mLogger.error("Thread-modular SIFA encountered a return transition at %s. Procedure calls are not supported; "
				+ "enable procedure inlining in the RCFG builder settings.", returnTransition.getSource());
		throw new UnsupportedOperationException("Thread-modular SIFA does not support procedure calls (found return at "
				+ returnTransition.getSource() + "). Enable procedure inlining or restrict to fork/join concurrency.");
	}

	public IPredicate postNoOpTransition(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		if (transition instanceof LocationMarkerTransition) {
			mObservedStateRecorder.recordTransitionInputState(transition, input);
			return applyInterferences(input, transition.getTarget());
		}
		return post(input, transition);
	}

	private static Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, List<IIcfgJoinTransitionThreadOther<IcfgLocation>>> buildJoinOtherMap(
			final IIcfg<IcfgLocation> icfg) {
		final Map<IIcfgJoinTransitionThreadCurrent<IcfgLocation>, List<IIcfgJoinTransitionThreadOther<IcfgLocation>>> map = new HashMap<>();
		for (final var procLocs : icfg.getProgramPoints().values()) {
			for (final IcfgLocation loc : procLocs.values()) {
				for (final IcfgEdge edge : loc.getOutgoingEdges()) {
					if (edge instanceof IIcfgJoinTransitionThreadOther) {
						final IIcfgJoinTransitionThreadOther<IcfgLocation> joinOther = (IIcfgJoinTransitionThreadOther<IcfgLocation>) edge;
						final IIcfgJoinTransitionThreadCurrent<IcfgLocation> joinCurrent = joinOther
								.getCorrespondingIIcfgJoinTransitionCurrentThread();
						map.computeIfAbsent(joinCurrent, k -> new ArrayList<>()).add(joinOther);
					}
				}
			}
		}
		return Map.copyOf(map);
	}

	public IPredicate applyInterferences(final IPredicate state, final IcfgLocation location) {
		if (Optimizations.trivialState(state, mThreadContext.interferences())) {
			return state;
		}
		final List<IInterference> applicable = Optimizations.filterApplicable(mThreadContext, location,
				mThreadActivityPreanalysis);
		if (applicable.isEmpty()) {
			return state;
		}
		return applyInterferenceRounds(state, applicable);
	}

	private IPredicate applyInterferenceRounds(final IPredicate state, final List<IInterference> interferences) {
		final IDomain domain = mThreadContext.interferenceDomain();
		final RelationalPredicatePostcondition postcondition = mThreadContext.postcondition();
		IPredicate current = state;
		while (true) {
			final IPredicate roundStart = current;
			boolean changed = false;
			for (final IInterference itf : interferences) {
				final IPredicate next = itf.applyUntilFixpoint(current, domain, postcondition, mGhostVariables,
						getManagedScript(), getFactory(), mSettings.innerWideningThreshold(), getStats());
				if (Optimizations.noGrowth(domain, next, current)) {
					continue;
				}
				current = next;
				changed = true;
			}
			if (Optimizations.roundConverged(changed, domain, current, roundStart)) {
				return current;
			}
		}
	}

	private IPredicate updateGhostvarsAndApplyInterferences(final IPredicate state,
			final IIcfgTransition<IcfgLocation> transition) {
		IPredicate updated = addLocationUpdate(state, transition);
		if (hasGhostLocationTracking() && transition instanceof final IIcfgForkTransitionThreadCurrent<?> fork) {
			updated = addLocationUpdateForThread(updated, fork.getNameOfForkedProcedure(),
					mGhostVariables.getEntryLocation(fork.getNameOfForkedProcedure()));
		}
		updated = assumeJoinedThreadAtExit(updated, transition);
		if (Optimizations.localTransition(transition)) {
			return updated;
		}
		return applyInterferences(updated, transition.getTarget());
	}

	private IPredicate assumeJoinedThreadAtExit(final IPredicate state,
			final IIcfgTransition<IcfgLocation> transition) {
		if (!hasGhostLocationTracking() || !(transition instanceof IIcfgJoinTransitionThreadCurrent<?>)) {
			return state;
		}
		@SuppressWarnings("unchecked")
		final IIcfgJoinTransitionThreadCurrent<IcfgLocation> joinCurrent = (IIcfgJoinTransitionThreadCurrent<IcfgLocation>) transition;
		IPredicate result = state;
		for (final IIcfgJoinTransitionThreadOther<IcfgLocation> joinOther : mJoinOtherByJoinCurrent
				.getOrDefault(joinCurrent, List.of())) {
			if (SmtUtils.isFalseLiteral(result.getFormula())) {
				return result;
			}
			final IcfgLocation joinedExit = joinOther.getSource();
			final String joinedThread = joinedExit.getProcedure();
			if (!mGhostVariables.tracksLocationPrecisely(joinedThread)) {
				continue;
			}
			final Term exitConstraint = mGhostVariables.createLocationConstraint(joinedThread, joinedExit);
			result = predicate(SmtUtils.and(getScript(), result.getFormula(), exitConstraint));
		}
		return result;
	}

	private IPredicate addLocationUpdate(final IPredicate postState, final IIcfgTransition<IcfgLocation> transition) {
		return addLocationUpdateForThread(postState, mThreadContext.threadId(), transition.getTarget());
	}

	public IPredicate addLocationUpdateForThread(final IPredicate postState, final String threadId,
			final IcfgLocation targetLocation) {
		if (!hasGhostLocationTracking() || !mGhostVariables.tracksLocationPrecisely(threadId)
				|| SmtUtils.isFalseLiteral(postState.getFormula())) {
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

	public IPredicate getInitialStatePredicate(final String threadId) {
		return mInitialStateFactory.getInitialStatePredicate(threadId);
	}

}
