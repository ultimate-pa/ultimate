package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.LinkedHashSet;
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

// TODO: Dont widen states which dont need it (dont group-widen)
// TODO: fix nondeterminism caused by random union orders and/or widening!
public class FixpointEngineGuardedConcurrent<UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, VARDECL, LOC extends IcfgLocation>
		implements IFixpointEngine<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> {

	private final ILogger mLogger;
	private final int mMaxUnwindings;
	private final int mMaxInterferenceFixpointUnwindings;
	private final int mMaxParallelStates;
	private int mIteration = 0;

	private final String mLocationAbstractionType;
	private final Map<String, ? extends LOC> mEntryLocs;
	private final ITransitionProvider<ACTION, LOC> mTransitionProvider;
	private final IAbstractStateStorage<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mStateStorage;
	private final GuardedInterferenceDomain<UNDERLYINGSTATE, ACTION, LOC> mDomain;
	private final IAbstractDomain<UNDERLYINGSTATE, ACTION> mUnderlyingDomain;
	private final IVariableProvider<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION> mVarProvider;
	private final IFixpointEngineFactory<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> mFixpointEngineFactory;
	private final FixpointEngineParameters<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> mParams;
	private final ConcurrentIcfgAnalyzer<ACTION, LOC> mAnalyzer;
	private final FixpointPrintHelper<UNDERLYINGSTATE, ACTION, LOC> mPrinter;
	private AbsIntResult<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mResult;
	private final SummaryMap<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mSummaryMap;
	private final IIcfg<? extends LOC> mIfcg;
	private final AbstractLocationMap<LOC> mLocationAbstraction;
	private final LocationAbstraction<LOC> mLocationAbstractionCalculator;
	private final InterferenceWideningOperator<UNDERLYINGSTATE, ACTION, LOC> mInterferenceWideningOperator;
	private final ThreadModularAbsintPrefs mThreadModPrefs;
	private final int LOCATION_TRACK_LIMIT = 100;

	public FixpointEngineGuardedConcurrent(final IUltimateServiceProvider services,
			final FixpointEngineParameters<UNDERLYINGSTATE, ACTION, VARDECL, LOC> params,
			final IFixpointEngineFactory<UNDERLYINGSTATE, ACTION, VARDECL, LOC> factory,
			final IIcfg<? extends LOC> icfg, final ThreadModularAbsintPrefs threadModPrefs) {
		if (params == null || !params.isValid()) {
			throw new IllegalArgumentException("invalid params");
		}
		mMaxUnwindings = threadModPrefs.maxItf();
		mUnderlyingDomain = params.getAbstractDomain();
		mLogger = params.getLogger();
		mEntryLocs = icfg.getProcedureEntryNodes();
		mThreadModPrefs = threadModPrefs;
		mMaxInterferenceFixpointUnwindings = threadModPrefs.maxItf();
		SimpleInterferenceApplier.mReductionMethod = threadModPrefs.locationReduction();
		SimpleInterferenceApplier.mReiterateOverStates = threadModPrefs.reiterate();
		GuardedInterferenceApplier.iterationsReached = 0;
		mIfcg = icfg;
		mLocationAbstractionCalculator = new LocationAbstraction<>(mEntryLocs);
		final AbstractLocationMap<LOC> absMap = mLocationAbstractionCalculator
				.computeLocationAbstraction(threadModPrefs.locationAbstraction(), services, icfg);
		mLocationAbstraction = absMap;
		if (absMap.maximumOfAll() > threadModPrefs.maxStates()) {
			if (absMap.maximumOfAll() > LOCATION_TRACK_LIMIT) {
				mMaxParallelStates = 1;
			} else {
				mMaxParallelStates = threadModPrefs.maxStates();
			}
		} else {
			mMaxParallelStates = absMap.maximumOfAll();
		}
		mDomain = new GuardedInterferenceDomain<>(mIfcg, mUnderlyingDomain, mLogger, mLocationAbstraction,
				mMaxParallelStates, mMaxInterferenceFixpointUnwindings,
				new AbstractInterferenceState<>(icfg.getCfgSmtToolkit().getProcedures()));
		mParams = (FixpointEngineParameters<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC>) params
				.setDomain((IAbstractDomain<UNDERLYINGSTATE, ACTION>) mDomain);
		mTransitionProvider = mParams.getTransitionProvider();
		mStateStorage = mParams.getStorage();
		mVarProvider = mParams.getVariableProvider();
		mSummaryMap = new SummaryMap<>(mTransitionProvider, mLogger);
		mFixpointEngineFactory = (IFixpointEngineFactory<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC>) factory;
		mAnalyzer = new ConcurrentIcfgAnalyzer<>(icfg);
		mPrinter = new FixpointPrintHelper<>(mMaxUnwindings, mMaxInterferenceFixpointUnwindings, mMaxParallelStates,
				mLogger);
		mLocationAbstractionType = threadModPrefs.locationAbstraction();
		mInterferenceWideningOperator = new InterferenceWideningOperator<>(mDomain.getWideningOperator());
	}

	private record concStatistics(int postOpCalls, int totalInnerIterations, int maxStatesOneItf) {
	}

	@Override
	public AbsIntResult<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> run(
			final Collection<? extends LOC> initialNodes, final Script script) {

		mLogger.info("Starting fixpoint engine with domain " + mDomain.getClass().getSimpleName() + " (maxUnwinding="
				+ mMaxUnwindings + ", maxParallelStates=" + mMaxParallelStates + "location abstraction: "
				+ mLocationAbstractionType + ")");
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
		var stats = new concStatistics(0, 0, 0);
		final var reachableErrorLocations = new LinkedHashSet<LOC>();
		var interferences = new AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC>(
				mIfcg.getCfgSmtToolkit().getProcedures());
		while (true) {
//			mLogger.info("\n");
			mLogger.info("Starting thread modular fixpoint engine iteration " + mIteration);
			// TODO: for debugging, remove later
//			final Map<String, AbsIntResult<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC>> resultSet = new LinkedHashMap<>();
			for (final String procedure : mAnalyzer.getTopologicalProcedureOrder()) {
				final var fixpointEngine = createNewUnderlyingFixpointEngine(procedure, interferences);
				final var threadResult = fixpointEngine.run(Set.of(mEntryLocs.get(procedure)), script);
				stats = new concStatistics(stats.postOpCalls + GuardedInterferenceDomain.postoperatorCalls,
						stats.totalInnerIterations + GuardedInterferenceDomain.totalInnerInterferenceIterations,
						stats.maxStatesOneItf + GuardedInterferenceDomain.maxStatesInOneItf);
//				resultSet.put(procedure, threadResult);
				updateStateStorageAndCounterexamples(threadResult, reachableErrorLocations);
			}

			final var newInterferences = computeNewInterferences();
			final var newMaybeWidened = updateOrWidenInterferences(interferences, newInterferences);
			final boolean fixpointReached = newMaybeWidened.isSubsetOf(interferences);
			if (fixpointReached) {
//				mPrinter.printResults(mLogger, mIteration, resultSet, mEntryLocs, mDomain.getAbstractLocationMap(),
//						script);
				mLogger.info("maxStates used: " + mMaxParallelStates);
				for (final String thread : mEntryLocs.keySet()) {
					mLogger.info("thread: " + thread + "maxother: "
							+ mLocationAbstraction.maxParallelOtherLocationsOf(thread));
				}
				mLogger.info("Interference postOp calls:" + stats.postOpCalls());
				mLogger.info("Total inner interference Iterations:" + stats.totalInnerIterations());
				mLogger.info("max states explored dduring one ITF fixpoint: " + stats.maxStatesOneItf());
				break;
			}
			interferences = newMaybeWidened;
//			printInterferenceLog(interferences);
			mIteration++;
		}
	}

	private IFixpointEngine<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> createNewUnderlyingFixpointEngine(
			final String procedure, final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> interferences) {
		final var newDomain = new GuardedInterferenceDomain<>(mIfcg, mUnderlyingDomain, mLogger, mLocationAbstraction,
				mMaxParallelStates, mMaxInterferenceFixpointUnwindings, interferences);
		if (mIteration > mMaxUnwindings) {
			newDomain.mWiden = true;
		}
		final var initialFactory = new DisjunctiveGuardedStateFactory<>(mStateStorage, mAnalyzer, mMaxParallelStates,
				newDomain, null, mEntryLocs);
		final var paramsWithInterferences = mParams.setStorage(mStateStorage.copy())
				.setVariableProvider(
						new InterferingVariableProvider<>(mVarProvider, initialFactory.getInitialState(procedure)))
				.setDomain(newDomain);
		final var fixpointEngine = mFixpointEngineFactory.constructFixpointEngine(paramsWithInterferences);
		return fixpointEngine;
	}

	private void updateStateStorageAndCounterexamples(
			final AbsIntResult<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> threadResult,
			final Set<LOC> reachableErrorLocations) {
		threadResult.getLoc2States().forEach((k, v) -> mStateStorage.addAbstractState(k,
				DisjunctiveAbstractState.createDisjunction(v, mMaxParallelStates)));
		for (final var counterExample : threadResult.getCounterexamples()) {
			final var execution = counterExample.getAbstractExecution();
			final var errorLocation = execution.get(execution.size() - 1).getSecond();
			if (reachableErrorLocations.add(errorLocation)) {
				mResult.addCounterexample(counterExample);
			}
		}
	}

	private AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> computeNewInterferences() {
		final var newInterferences = InterferenceCreator.computeInterferences(mEntryLocs, mIfcg, mStateStorage,
				mTransitionProvider, mMaxParallelStates, mLocationAbstraction, mLocationAbstractionCalculator,
				mThreadModPrefs.interferencePrestatePrecision());
		return newInterferences;
	}

	private AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> updateOrWidenInterferences(
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> interferences,
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> newInterferences) {
		if (mIteration > mMaxUnwindings) {
			mLogger.info("Applying widenning to the interferences.");
			return mInterferenceWideningOperator.calcWidenedInterferences(interferences, newInterferences,
					mIfcg.getCfgSmtToolkit().getProcedures(), mMaxParallelStates);
		}
		return newInterferences;
	}

	private void printInterferenceLog(
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> newInterferenceState) {
		mLogger.error("new Interference Set");
		for (final String termString : newInterferenceState.interferenceStrings()) {
			mLogger.error(termString);
		}
	}
}
