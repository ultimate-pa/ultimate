package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbsIntResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IFixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IFixpointEngineFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.SummaryMap;

// TODO: fix nondeterminism caused by random union orders and/or widening!
public class FixpointEngineGuardedConcurrent<UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, VARDECL, LOC extends IcfgLocation>
		implements IFixpointEngine<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> {

	private final int mMaxUnwindings;
	private final int mMaxInterferenceFixpointUnwindings;
	private final int mMaxParallelStates;
	private int mIteration = 0;
	Integer aInteger = 0;

	private final ITransitionProvider<ACTION, LOC> mTransitionProvider;
	private final IAbstractStateStorage<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mStateStorage;
	private final GuardedInterferenceDomain<UNDERLYINGSTATE, ACTION, LOC> mDomain;
	private final IAbstractDomain<UNDERLYINGSTATE, ACTION> mUnderlyingDomain;
	private final IVariableProvider<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION> mVarProvider;
	private final ILogger mLogger;

	private AbsIntResult<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mResult;
	private final SummaryMap<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mSummaryMap;

	private final IFixpointEngineFactory<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> mFixpointEngineFactory;
	private final Map<String, ? extends LOC> mEntryLocs;
	private final FixpointEngineParameters<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> mParams;
	private final ConcurrentIcfgAnalyzer<ACTION, LOC> mAnalyzer;
	private final FixpointPrintHelper<UNDERLYINGSTATE, ACTION, LOC> mPrinter;
	private final String mLocationAbstraction;
	private final GuardedInterferenceApplier<UNDERLYINGSTATE, ACTION, LOC> mItfApplier;
	private final InterferenceWideningOperator<UNDERLYINGSTATE, ACTION, LOC> mInterferenceWideningOperator;
	private final DisjunctiveGuardedStateFactory<UNDERLYINGSTATE, ACTION, LOC> mDisjFactory;

	public FixpointEngineGuardedConcurrent(final IUltimateServiceProvider services,
			final FixpointEngineParameters<UNDERLYINGSTATE, ACTION, VARDECL, LOC> params,
			final IFixpointEngineFactory<UNDERLYINGSTATE, ACTION, VARDECL, LOC> factory,
			final IIcfg<? extends LOC> icfg, final String locationAbstraction) {
		if (params == null || !params.isValid()) {
			throw new IllegalArgumentException("invalid params");
		}
		mMaxUnwindings = params.getMaxUnwindings();
		mMaxParallelStates = params.getMaxParallelStates();
		mMaxInterferenceFixpointUnwindings = 32;
		GuardedInterferenceApplier.iterationsReached = 0;
		mEntryLocs = icfg.getProcedureEntryNodes();
		final var absLoc = new LocationAbstraction<LOC>(mEntryLocs);
		final AbstractLocationMap<LOC> absMap = absLoc.computeLocationAbstraction(locationAbstraction, services, icfg);
		mUnderlyingDomain = params.getAbstractDomain();
		mDomain = new GuardedInterferenceDomain<>(icfg, mUnderlyingDomain, params.getLogger(), absMap,
				mMaxParallelStates, mMaxInterferenceFixpointUnwindings);
		mInterferenceWideningOperator = new InterferenceWideningOperator<>(mDomain);
		// TODO: not sure this is sound
		mParams = (FixpointEngineParameters<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC>) params
				.setDomain((IAbstractDomain<UNDERLYINGSTATE, ACTION>) mDomain);

		mLogger = mParams.getLogger();
		mTransitionProvider = mParams.getTransitionProvider();
		mStateStorage = mParams.getStorage();
		mVarProvider = mParams.getVariableProvider();
		mSummaryMap = new SummaryMap<>(mTransitionProvider, mLogger);

		mFixpointEngineFactory = (IFixpointEngineFactory<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC>) factory;

		mAnalyzer = new ConcurrentIcfgAnalyzer<>(icfg);
		mPrinter = new FixpointPrintHelper<>(mMaxUnwindings, mMaxInterferenceFixpointUnwindings, mMaxParallelStates,
				mLogger);
		mLocationAbstraction = locationAbstraction;
		final var applier = ((GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain
				.getPostOperator()).getItfApplier();
		mItfApplier = applier;
		mDisjFactory = new DisjunctiveGuardedStateFactory<>(mStateStorage, mAnalyzer, mMaxParallelStates, mDomain,
				mItfApplier, mEntryLocs);
	}

	@Override
	public AbsIntResult<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> run(
			final Collection<? extends LOC> initialNodes, final Script script) {

		mLogger.info("Starting fixpoint engine with domain " + mDomain.getClass().getSimpleName() + " (maxUnwinding="
				+ mMaxUnwindings + ", maxParallelStates=" + mMaxParallelStates + "location abstraction: "
				+ mLocationAbstraction + ")");
		mResult = new AbsIntResult<>(script, mDomain, mTransitionProvider, mVarProvider);
		mDomain.beforeFixpointComputation(mResult.getBenchmark());
		calculateFixpoint(script);
		mResult.saveRootStorage(mStateStorage);
		mResult.saveSummaryStorage(mSummaryMap);
		mLogger.debug("Fixpoint computation completed");

		mDomain.afterFixpointComputation(
				(IAbstractInterpretationResult<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC>) mResult);

		// TODO: to weak right now, make stronger
//		assert areStatesInterferenceFree();
		return mResult;
	}

	private void calculateFixpoint(final Script script) {
		mIteration = 1;
		final int unchangedRounds = 0;
		final Set<LOC> reachableErrorLocations = new HashSet<>();
		while (true) {
			mLogger.error("\n");
			mLogger.error("Starting thread modular fixpoint engine iteration " + mIteration);
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> oldInterferenceState = mItfApplier
					.getInterferences();

			final Map<String, AbsIntResult<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC>> resultSet = new HashMap<>();
			for (final String procedure : mAnalyzer.getTopologicalProcedureOrder()) {
				final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> initialState = mDisjFactory
						.getInitialState(procedure);
				final FixpointEngineParameters<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> paramsWithInterferences = mParams
						.setStorage(mStateStorage.copy())
						.setVariableProvider(new InterferingVariableProvider<>(mVarProvider, initialState));
				final IFixpointEngine<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> fixpointEngine = mFixpointEngineFactory
						.constructFixpointEngine(paramsWithInterferences);
				final AbsIntResult<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> threadResult = fixpointEngine
						.run(Set.of(mEntryLocs.get(procedure)), script);

				// TODO: for debugging, remove later
				resultSet.put(procedure, threadResult);

				// Merge mStateStorage and result.getLoc2States
				threadResult.getLoc2States().forEach((k, v) -> mStateStorage.addAbstractState(k,
						DisjunctiveAbstractState.createDisjunction(v, mMaxParallelStates)));
				// Add present counterexamples
				for (final var counterExample : threadResult.getCounterexamples()) {
					final var execution = counterExample.getAbstractExecution();
					final var errorLocation = execution.get(execution.size() - 1).getSecond();
					if (reachableErrorLocations.add(errorLocation)) {
						mResult.addCounterexample(counterExample);
					}
				}
			}

			mItfApplier.updateInterferences();
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> newInterferenceState = mItfApplier
					.getInterferences();

			// interference fixpoint reached
			mLogger.error("Interference Set we used:");
			for (final String termString : oldInterferenceState.interferenceStrings()) {
				mLogger.error(termString);
			}
			mLogger.error("new Interference Set");
			for (final String termString : oldInterferenceState.interferenceStrings()) {
				mLogger.error(termString);
			}
			final boolean changed = !newInterferenceState.isSubsetOf(oldInterferenceState);
			if (!changed) {
				mPrinter.printResults(mLogger, newInterferenceState, newInterferenceState, mIteration, resultSet,
						mEntryLocs, mDomain.getAbstractLocationMap(), script);
				break;
			}
			if (mIteration > mMaxUnwindings && changed) {
				mItfApplier.setInterferences(mInterferenceWideningOperator
						.calcWidenedInterferences(oldInterferenceState, newInterferenceState));
				mLogger.error("DID WIDENING ON INTERFERENCES.");
			}
			mIteration++;
		}
	}
}
