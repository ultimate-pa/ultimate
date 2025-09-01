package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
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

public class FixpointEngineConcurrent<UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, VARDECL, LOC extends IcfgLocation>
		implements IFixpointEngine<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> {

	private final ILogger mLogger;
	private final int mMaxUnwindings;
	private final int mMaxInterferenceFixpointUnwindings;
	private final int mMaxParallelStates;
	private int mIteration = 0;

	private final String mLocationAbstractionType;
	private final Map<String, ? extends LOC> mEntryLocs;
	private final ITransitionProvider<ACTION, LOC> mTransitionProvider;
	private final IAbstractStateStorage<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mStateStorage;
	private final InterferenceDomain<UNDERLYINGSTATE, ACTION, LOC> mDomain;
	private final IAbstractDomain<UNDERLYINGSTATE, ACTION> mUnderlyingDomain;
	private final IVariableProvider<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION> mVarProvider;
	private final IFixpointEngineFactory<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> mFixpointEngineFactory;
	private final FixpointEngineParameters<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> mParams;
	private final ConcurrentIcfgAnalyzer<ACTION, LOC> mAnalyzer;
	private final FixpointPrintHelper<UNDERLYINGSTATE, ACTION, LOC> mPrinter;
	private AbsIntResult<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mResult;
	private final SummaryMap<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mSummaryMap;
	private final IIcfg<? extends LOC> mCfg;
	private final StaticAbstractLocationMap<LOC> mLocationAbstraction;
	private final LocationAbstraction<LOC> mLocationAbstractionCalculator;
	private final InterferenceWideningOperator<UNDERLYINGSTATE, ACTION, LOC> mInterferenceWideningOperator;
	private final InterferenceCache<UNDERLYINGSTATE, ACTION, LOC> mCache;

	public FixpointEngineConcurrent(final IUltimateServiceProvider services,
			final FixpointEngineParameters<UNDERLYINGSTATE, ACTION, VARDECL, LOC> params,
			final IFixpointEngineFactory<UNDERLYINGSTATE, ACTION, VARDECL, LOC> factory,
			final IIcfg<? extends LOC> icfg, final ThreadModularAbsintPrefs threadModPrefs) {
		if (params == null || !params.isValid()) {
			throw new IllegalArgumentException("invalid params");
		}
		mUnderlyingDomain = params.getAbstractDomain();
		mLogger = params.getLogger();
		mEntryLocs = icfg.getProcedureEntryNodes();
		mMaxInterferenceFixpointUnwindings = threadModPrefs.maxItf();
		InterferenceFIxpoint.iterationsReached = 0;
		InterferenceFIxpoint.postOnly = false;
		mCfg = icfg;
		mLocationAbstractionCalculator = new LocationAbstraction<>();
		final StaticAbstractLocationMap<LOC> absMap = mLocationAbstractionCalculator
				.computeLocationAbstraction(threadModPrefs.locationAbstraction(), services, icfg);
		mLocationAbstraction = absMap;
		if (threadModPrefs.locationAbstraction().equals("Split at Guard Entry and Exit")) {
			mMaxParallelStates = 4;
			mMaxUnwindings = 4;
		} else if (threadModPrefs.locationAbstraction().equals("Split at all Guard variable occurences")) {
			mMaxParallelStates = 1000;
			mMaxUnwindings = 1000;
		} else if (threadModPrefs.locationAbstraction().equals("Non-relational Singleton")) {
			mMaxParallelStates = 1;
			mMaxUnwindings = 1;
			InterferenceFIxpoint.postOnly = true;
		} else {
			mMaxParallelStates = 1;
			mMaxUnwindings = 1;
		}

		params.setMaxParallelStates(1);
		mCache = new InterferenceCache<>();
		mDomain = new InterferenceDomain<>(mCfg, mUnderlyingDomain, mLogger, mLocationAbstraction, mMaxParallelStates,
				mMaxInterferenceFixpointUnwindings,
				new AbstractInterferenceState<>(icfg.getCfgSmtToolkit().getProcedures()), mCache);
		mParams = (FixpointEngineParameters<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC>) params
				.setDomain((IAbstractDomain<UNDERLYINGSTATE, ACTION>) mDomain);
		mTransitionProvider = mParams.getTransitionProvider();
		mStateStorage = mParams.getStorage();
		mVarProvider = mParams.getVariableProvider();
		mSummaryMap = new SummaryMap<>(mTransitionProvider, mLogger);
		mFixpointEngineFactory = (IFixpointEngineFactory<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC>) factory;
		mAnalyzer = new ConcurrentIcfgAnalyzer<>(icfg);
		mPrinter = new FixpointPrintHelper<>(mMaxUnwindings, mMaxInterferenceFixpointUnwindings, mMaxParallelStates,
				mLogger);
		mLocationAbstractionType = threadModPrefs.locationAbstraction();
		mInterferenceWideningOperator = new InterferenceWideningOperator<>(mDomain.getWideningOperator());
	}

	private record ConcStatistics(int postOpCalls, int postOpCacheHits, int applierCacheHits, int totalInnerIterations,
			int maxStatesOneItf) {
	}

	@Override
	public AbsIntResult<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> run(
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
				(IAbstractInterpretationResult<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC>) mResult);

		return mResult;
	}

	private void calculateFixpoint(final Script script) {
		mIteration = 1;
		var stats = new ConcStatistics(0, 0, 0, 0, 0);
		final var reachableErrorLocations = new LinkedHashSet<LOC>();
		var interferences = new AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC>(
				mCfg.getCfgSmtToolkit().getProcedures());
		while (true) {
			final var interferenceCount = interferences.getAllInterferences().size();
			mLogger.info("Starting thread modular fixpoint engine iteration " + mIteration);
			mLogger.info("Amount of interferences going to be used in this iteration : " + interferenceCount);
			// TODO: for debugging, remove later
			final Map<String, AbsIntResult<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC>> resultSet = new LinkedHashMap<>();
			for (final String procedure : mAnalyzer.getTopologicalProcedureOrder()) {
				final var fixpointEngine = createNewUnderlyingFixpointEngine(procedure, interferences);
				final var threadResult = fixpointEngine.run(Set.of(mEntryLocs.get(procedure)), script);
				stats = updateStatistics(stats);
				resultSet.put(procedure, threadResult);
				updateStateStorageAndCounterexamples(threadResult, reachableErrorLocations);
			}

			final var newInterferences = computeNewInterferences();
			final var newMaybeWidened = updateOrWidenInterferences(interferences, newInterferences);
			final SubsetResult fixpointReached = newMaybeWidened.isSubsetOf(interferences);
			if (fixpointReached != SubsetResult.NONE) {
				printResultSTatistics(resultSet, script, stats);
				break;
			}
			interferences = newMaybeWidened;
			mIteration++;
		}
	}

	private IFixpointEngine<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> createNewUnderlyingFixpointEngine(
			final String procedure, final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> interferences) {
		final var newDomain = new InterferenceDomain<>(mCfg, mUnderlyingDomain, mLogger, mLocationAbstraction,
				mMaxParallelStates, mMaxInterferenceFixpointUnwindings, interferences, mCache);
		if (mIteration > mMaxUnwindings) {
			newDomain.mWiden = true;
		}
		final var initialFactory = new InitialStateFactory<>(mStateStorage, mAnalyzer, mMaxParallelStates, newDomain,
				mEntryLocs, mCache);
		final var paramsWithInterferences = mParams.setStorage(mStateStorage.copy())
				.setVariableProvider(
						new InterferingVariableProvider<>(mVarProvider, initialFactory.createInitialStates(procedure)))
				.setDomain(newDomain);
		final var fixpointEngine = mFixpointEngineFactory.constructFixpointEngine(paramsWithInterferences);
		return fixpointEngine;
	}

	private void updateStateStorageAndCounterexamples(
			final AbsIntResult<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> threadResult,
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
		final var itfCreator = new InterferenceCreator<UNDERLYINGSTATE, ACTION, LOC>();
		final var newInterferences = itfCreator.computeInterferences(mEntryLocs, mCfg, mStateStorage,
				mTransitionProvider, mLocationAbstraction);
		return newInterferences;
	}

	private AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> updateOrWidenInterferences(
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> interferences,
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> newInterferences) {
		if (mIteration > mMaxUnwindings) {
			mLogger.info("Applying widenning to the interferences.");
			return mInterferenceWideningOperator.calcWidenedInterferences(interferences, newInterferences,
					mCfg.getCfgSmtToolkit().getProcedures());
		}
		return newInterferences;
	}

	private ConcStatistics updateStatistics(final ConcStatistics stats) {
		return new ConcStatistics(stats.postOpCalls + InterferenceDomain.postoperatorCalls,
				stats.postOpCacheHits + InterferenceDomain.postOpCacheHits,
				stats.applierCacheHits + InterferenceDomain.applierCacheHits,
				stats.totalInnerIterations + InterferenceDomain.totalInnerInterferenceIterations,
				stats.maxStatesOneItf + InterferenceDomain.maxStatesInOneItf);
	}

	private void printResultSTatistics(
			final Map<String, AbsIntResult<InterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC>> resultSet,
			final Script script, final ConcStatistics stats) {
		mPrinter.printResults(mLogger, mIteration, resultSet, mEntryLocs, mDomain.getAbstractLocationMap(), script);
		mLogger.info("maxStates used: " + mMaxParallelStates);
		mLogger.info("Interference postOp calls:" + stats.postOpCalls());
		mLogger.info("DisjState cache hits:" + stats.postOpCacheHits());
		mLogger.info("Applier cache hits(no diff, addvars):" + stats.applierCacheHits());
		mLogger.info("Total inner interference Iterations:" + stats.totalInnerIterations());
		mLogger.info("max states explored dduring one ITF fixpoint: " + stats.maxStatesOneItf());
	}
}
