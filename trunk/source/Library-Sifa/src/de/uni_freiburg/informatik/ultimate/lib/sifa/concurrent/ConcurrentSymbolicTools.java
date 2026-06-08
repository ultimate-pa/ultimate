package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
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
	private final IIcfg<IcfgLocation> mIcfg;
	private final ThreadModularSifaSettings mSettings;
	private final InitialStateFactory mInitialStateFactory;
	private final JoinHandler mJoinHandler;
	private GhostVariableManager mGhostVariables;
	private ThreadActivityPreanalysis mThreadActivityPreanalysis;
	private ThreadAnalysisContext mThreadContext;
	private ObservedThreadStateRecorder mObservedStateRecorder;
	// Per-thread cache of existential projections over the ghost location var: Term identity is safe in SmtInterpol.
	// Persists across outer iterations since the ghost loc var for a thread never changes.
	private final Map<String, IdentityHashMap<Term, Term>> mLocProjectionCache = new HashMap<>();

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

	public void configureForThread(final String threadId, final IInterference interference,
			final Map<IcfgLocation, IPredicate> locationPredicates, final IDomain domain,
			final RelationalPredicatePostcondition postcondition) {
		IThreadLocalDomainContext.setIfApplicable(domain, threadId);
		final ArrayList<String> sortedInterferenceThreadIds = interference != null
				? new ArrayList<>(interference.threadIds()) : new ArrayList<>();
		Collections.sort(sortedInterferenceThreadIds);
		final boolean includeSelfInterference = mThreadActivityPreanalysis.getMultiForkedThreads().contains(threadId);
		mThreadContext = new ThreadAnalysisContext(threadId, interference, domain, postcondition,
				includeSelfInterference, java.util.List.copyOf(sortedInterferenceThreadIds), locationPredicates,
				new HashMap<>());
		mObservedStateRecorder = new ObservedThreadStateRecorder(domain, mGhostVariables);
		mInitialStateFactory.configureForThread(locationPredicates, domain);
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
		if (Optimizations.trivialState(state, mThreadContext.interference())) {
			return state;
		}
		final Set<String> activeThreadIds =
				Optimizations.filterApplicable(mThreadContext, location, mThreadActivityPreanalysis);
		if (activeThreadIds.isEmpty()) {
			return state;
		}
		return mThreadContext.interference().applyUntilFixpoint(state, activeThreadIds,
				mThreadContext.domain(), mSettings.innerWideningThreshold(), getStats());
	}

	private IPredicate updateGhostvarsAndApplyInterferences(final IPredicate state,
			final IIcfgTransition<IcfgLocation> transition) {
		IPredicate updated = addLocationUpdate(state, transition);
		if (hasGhostLocationTracking() && transition instanceof final IIcfgForkTransitionThreadCurrent<?> fork) {
			updated = addLocationUpdateForThread(updated, fork.getNameOfForkedProcedure(),
					mGhostVariables.getEntryLocation(fork.getNameOfForkedProcedure()));
		}
		updated = mJoinHandler.extractJoinedThreadGlobalExitStateAndIntersect(updated, transition, mThreadContext,
				mThreadActivityPreanalysis);
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

		final Term locConstraint = mGhostVariables.createLocationConstraint(threadId, targetLocation);
		if (SmtUtils.isTrueLiteral(postState.getFormula())) {
			return predicate(locConstraint);
		}

		final TermVariable currentLocTv = mGhostVariables.getLocationTermVar(threadId);
		final Term stateTerm = postState.getFormula();
		final Term projected = mLocProjectionCache.computeIfAbsent(threadId, k -> new IdentityHashMap<>())
				.computeIfAbsent(stateTerm,
						k -> RelationalPredicateUtils.existentiallyProject(k, Set.of(currentLocTv), mServices,
								getManagedScript()));
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
