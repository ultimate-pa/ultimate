package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing.LocationMarkerTransition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.BucketPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.ObservedThreadStateRecorder;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceCollection;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate.PostStateInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.unaryglobals.UnaryGlobalInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.InitialStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.InterferenceApplicatorType;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ConcurrentSymbolicTools extends SymbolicTools {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IIcfg<IcfgLocation> mIcfg;
	private final ThreadModularSifaSettings mSettings;
	private final InitialStateFactory mInitialStateFactory;
	private final JoinHandler mJoinHandler;
	private GhostVariableManager mGhostVariables;
	private ThreadActivityPreanalysis mThreadActivityPreanalysis;
	private ThreadAnalysisContext mThreadContext;
	private ObservedThreadStateRecorder mObservedStateRecorder;

	public ConcurrentSymbolicTools(final IUltimateServiceProvider services, final SifaStats stats,
			final IIcfg<IcfgLocation> icfg, final SimplificationTechnique simplification,
			final IIcfgSymbolTable symbolTable, final ThreadModularSifaSettings settings) {
		super(services, stats, icfg, simplification, symbolTable);
		mLogger = services.getLoggingService().getLogger(ConcurrentSymbolicTools.class);
		mServices = services;
		mIcfg = icfg;
		mSettings = settings;
		mInitialStateFactory = new InitialStateFactory(this, icfg);
		mJoinHandler = new JoinHandler(this, services, icfg);
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
		mJoinHandler.configureStaticAnalysis(ghostVariables);
	}

	public void configureForThread(final String threadId, final InterferenceCollection interferences,
			final Map<IcfgLocation, IPredicate> locationPredicates, final IDomain analysisDomain,
			final IDomain interferenceDomain, final RelationalPredicatePostcondition postcondition) {
		IThreadLocalDomainContext.setIfApplicable(analysisDomain, threadId);
		IThreadLocalDomainContext.setIfApplicable(interferenceDomain, threadId);
		final List<String> sortedInterferenceThreadIds = new ArrayList<>(interferences.getThreadIds());
		Collections.sort(sortedInterferenceThreadIds);
		final boolean includeSelfInterference = mThreadActivityPreanalysis.getMultiForkedThreads().contains(threadId);
		mThreadContext = new ThreadAnalysisContext(threadId, interferences, interferenceDomain, postcondition,
				includeSelfInterference, List.copyOf(sortedInterferenceThreadIds), locationPredicates, new HashMap<>());
		mObservedStateRecorder = new ObservedThreadStateRecorder(interferenceDomain, mGhostVariables);
		mInitialStateFactory.configureForThread(locationPredicates, analysisDomain);
		mJoinHandler.configureForThread(mThreadContext, mThreadActivityPreanalysis);
	}


	@Override
	public IPredicate post(final IPredicate input, final IIcfgTransition<IcfgLocation> transition) {
		mObservedStateRecorder.recordTransitionInputState(transition, input);
		final IPredicate spResult = mapBuckets(input, bucket -> super.post(bucket, transition));
		final IPredicate joinProjected = mJoinHandler.projectJoinAssignedVars(spResult, transition);
		return updateGhostvarsAndApplyInterferences(joinProjected, transition);
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
		if (usesOnePassApplication(interferences)) {
			return applyInterferencesOnce(state, interferences, domain);
		}
		IPredicate current = state;
		while (true) {
			final IPredicate roundStart = current;
			boolean changed = false;
			for (final IInterference itf : interferences) {
				final IPredicate next = itf.applyUntilFixpoint(current, domain, mSettings.innerWideningThreshold(),
						getStats());
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

	private boolean usesOnePassApplication(final List<IInterference> interferences) {
		return mSettings.interferenceApplicatorType() == InterferenceApplicatorType.UNARY_GLOBALS
				|| mSettings.interferenceApplicatorType() == InterferenceApplicatorType.POST_STATE
				|| interferences.stream().allMatch(itf -> itf instanceof UnaryGlobalInterference
						|| itf instanceof PostStateInterference);
	}

	private IPredicate applyInterferencesOnce(final IPredicate state, final List<IInterference> interferences,
			final IDomain domain) {
		IPredicate current = state;
		for (final IInterference itf : interferences) {
			current = itf.applyUntilFixpoint(current, domain, mSettings.innerWideningThreshold(), getStats());
		}
		return current;
	}

	private IPredicate updateGhostvarsAndApplyInterferences(final IPredicate state,
			final IIcfgTransition<IcfgLocation> transition) {
		IPredicate updated = addLocationUpdate(state, transition);
		if (hasGhostLocationTracking() && transition instanceof final IIcfgForkTransitionThreadCurrent<?> fork) {
			updated = addLocationUpdateForThread(updated, fork.getNameOfForkedProcedure(),
					mGhostVariables.getEntryLocation(fork.getNameOfForkedProcedure()));
		}
		updated = mJoinHandler.importJoinedThreadExitSummary(updated, transition);
		if (Optimizations.localTransition(transition)) {
			return updated;
		}
		return applyInterferences(updated, transition.getTarget());
	}

	private IPredicate addLocationUpdate(final IPredicate postState, final IIcfgTransition<IcfgLocation> transition) {
		return addLocationUpdateForThread(postState, mThreadContext.threadId(), transition.getTarget());
	}

	public IPredicate addLocationUpdateForThread(final IPredicate postState, final String threadId,
			final IcfgLocation targetLocation) {
		return mapBuckets(postState, bucket -> addLocationUpdateForThreadPlain(bucket, threadId, targetLocation));
	}

	private IPredicate addLocationUpdateForThreadPlain(final IPredicate postState, final String threadId,
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

	IPredicate mapBuckets(final IPredicate state, final Function<IPredicate, IPredicate> operation) {
		if (!(state instanceof final BucketPredicate buckets)) {
			return operation.apply(state);
		}
		final Map<Integer, IPredicate> result = new LinkedHashMap<>();
		buckets.buckets().forEach((bucket, bucketState) -> result.put(bucket, operation.apply(bucketState)));
		return BucketPredicate.of(this, result);
	}

	private boolean hasGhostLocationTracking() {
		return mGhostVariables != null;
	}

	public IPredicate getInitialStatePredicate(final String threadId) {
		return mInitialStateFactory.getInitialStatePredicate(threadId);
	}

}
