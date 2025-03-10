package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbsIntResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IFixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IFixpointEngineFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.SummaryMap;

public class FixpointEngineRelationalConcurrent<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, VARDECL, LOC extends IcfgLocation>
		implements IFixpointEngine<STATE, ACTION, VARDECL, LOC> {
	private final int mMaxUnwindings;
	private final int mMaxParallelStates;

	private final ITransitionProvider<ACTION, LOC> mTransitionProvider;
	private final IAbstractStateStorage<STATE, ACTION, LOC> mStateStorage;
	private final IAbstractDomain<STATE, ACTION> mDomain;
	private final IVariableProvider<STATE, ACTION> mVarProvider;
	private final ILogger mLogger;

	private AbsIntResult<STATE, ACTION, LOC> mResult;
	private final SummaryMap<STATE, ACTION, LOC> mSummaryMap;

	private final IFixpointEngineFactory<STATE, ACTION, VARDECL, LOC> mFixpointEngineFactory;
	private final Map<String, ? extends LOC> mEntryLocs;
	private final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> mParams;
	private final ConcurrentIcfgAnalyzer<ACTION, LOC> mAnalyzer;
	private final FixpointPrintHelper<STATE, ACTION, LOC> mPrinter;

	public FixpointEngineRelationalConcurrent(final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> params,
			final IFixpointEngineFactory<STATE, ACTION, VARDECL, LOC> factory, final IIcfg<? extends LOC> icfg) {
		if (params == null || !params.isValid()) {
			throw new IllegalArgumentException("invalid params");
		}
		mParams = params;
		mLogger = params.getLogger();
		mTransitionProvider = params.getTransitionProvider();
		mStateStorage = params.getStorage();
		mDomain = params.getAbstractDomain();
		mVarProvider = params.getVariableProvider();
		mMaxUnwindings = params.getMaxUnwindings();
		mMaxParallelStates = params.getMaxParallelStates();
		mSummaryMap = new SummaryMap<>(mTransitionProvider, mLogger);
		mFixpointEngineFactory = factory;
		mEntryLocs = icfg.getProcedureEntryNodes();
		mAnalyzer = new ConcurrentIcfgAnalyzer<>(icfg);
		mPrinter = new FixpointPrintHelper<>();
	}

	@Override
	public AbsIntResult<STATE, ACTION, LOC> run(final Collection<? extends LOC> initialNodes, final Script script) {
		mLogger.info("Starting fixpoint engine with domain " + mDomain.getClass().getSimpleName() + " (maxUnwinding="
				+ mMaxUnwindings + ", maxParallelStates=" + mMaxParallelStates + ")");
		mResult = new AbsIntResult<>(script, mDomain, mTransitionProvider, mVarProvider);
		mDomain.beforeFixpointComputation(mResult.getBenchmark());
		calculateFixpoint(script);
		mResult.saveRootStorage(mStateStorage);
		mResult.saveSummaryStorage(mSummaryMap);
		mLogger.debug("Fixpoint computation completed");
		mDomain.afterFixpointComputation(mResult);
		assert areStatesInterferenceFree();
		return mResult;
	}

	// TODO: replace with more precise version mirroring our method of interferences,
	// as this should fail when we get more precise
	private boolean areStatesInterferenceFree() {
		final Map<LOC, DisjunctiveAbstractState<STATE>> loc2States =
				mResult.getLoc2States().entrySet().stream().collect(
						Collectors.toMap(Entry::getKey, x -> DisjunctiveAbstractState.createDisjunction(x.getValue())));
		for (final Entry<LOC, DisjunctiveAbstractState<STATE>> entry : loc2States.entrySet()) {
			final DisjunctiveAbstractState<STATE> state = removeLocalVars(entry.getValue());
			for (final ACTION interfering : mAnalyzer.getInterferingWrites(entry.getKey())) {
				final DisjunctiveAbstractState<STATE> preInterfering =
						loc2States.get(mTransitionProvider.getSource(interfering));
				if (preInterfering == null) {
					continue;
				}
				if (!mParams.getDebugHelper().isInterferenceFree(state, preInterfering, interfering)) {
					return false;
				}
			}
		}
		return true;
	}

	private void calculateFixpoint(final Script script) {
		int iteration = 1;
		final Set<LOC> reachableErrorLocations = new HashSet<>();
		while (true) {
			mLogger.error("\n");
			mLogger.error("Starting thread modular fixpoint engine iteration " + iteration);
			final var interferenceState = new AbstractInterferenceState<STATE, ACTION>(
					((RelationalInterferingDomain) mDomain).interferenceState());
			mLogger.error("Interference Set:");
			for (final String termString : interferenceState.interferenceStrings()) {
				mLogger.error(termString);
			}
			final Map<String, AbsIntResult<STATE, ACTION, LOC>> resultSet = new HashMap<>();
			for (final String procedure : mAnalyzer.getTopologicalProcedureOrder()) {
				mLogger.warn("\n");
				mLogger.warn("Analysing thread " + procedure);
				final DisjunctiveAbstractState<STATE> initialState = getInitialState(procedure);
				final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> paramsWithInterferences =
						mParams.setStorage(mStateStorage.copy())
								.setVariableProvider(new InterferingVariableProvider<>(mVarProvider, initialState));
				final IFixpointEngine<STATE, ACTION, VARDECL, LOC> fixpointEngine =
						mFixpointEngineFactory.constructFixpointEngine(paramsWithInterferences);
				final AbsIntResult<STATE, ACTION, LOC> threadResult =
						fixpointEngine.run(Set.of(mEntryLocs.get(procedure)), script);

				// TODO: for debugging, remove later
				resultSet.put(procedure, threadResult);

				// Merge mStateStorage and result.getLoc2States
				threadResult.getLoc2States().forEach(
						(k, v) -> mStateStorage.addAbstractState(k, DisjunctiveAbstractState.createDisjunction(v)));
				// Add present counterexamples
				for (final var counterExample : threadResult.getCounterexamples()) {
					final var execution = counterExample.getAbstractExecution();
					final var errorLocation = execution.get(execution.size() - 1).getSecond();
					if (reachableErrorLocations.add(errorLocation)) {
						mResult.addCounterexample(counterExample);
					}
				}
			}

			final AbstractInterferenceState<STATE, ACTION> newInterferenceState =
					((RelationalInterferingDomain) mDomain).interferenceState();

			// interference fixpoint reached
			if (newInterferenceState.isSubsetOf(interferenceState)) {
				mPrinter.printCfgResults(mLogger, newInterferenceState, newInterferenceState, iteration, resultSet);
				break;
			}
			mLogger.warn(newInterferenceState.interferenceStrings());
			mLogger.warn("doesnt imply");
			mLogger.warn(interferenceState.interferenceStrings());
			if (iteration >= mMaxUnwindings) {
				newInterferenceState
						.changeInterferences(calcWidenedInterferences(interferenceState, newInterferenceState));
				mLogger.error("DID WIDENING ON INTERFERENCES.");
			}
			iteration++;
		}

	}

	private Map<String, Map<ACTION, STATE>> calcWidenedInterferences(
			final AbstractInterferenceState<STATE, ACTION> oldInterference,
			final AbstractInterferenceState<STATE, ACTION> newInterference) {
		final Map<String, Map<ACTION, STATE>> widenedInterferenceMap = new HashMap<>();

		final Map<String, Map<ACTION, STATE>> oldMap = oldInterference.getInterferenceMapHashRelation();
		final Map<String, Map<ACTION, STATE>> newMap = newInterference.getInterferenceMapHashRelation();
		final Set<String> threadNames = new HashSet<>(oldMap.keySet());
		threadNames.addAll(newMap.keySet());

		for (final String threadName : threadNames) {
			final Map<ACTION, STATE> oldTransitionMap = oldMap.getOrDefault(threadName, Collections.emptyMap());
			final Map<ACTION, STATE> newTransitionMap = newMap.getOrDefault(threadName, Collections.emptyMap());

			final Set<ACTION> actions = new HashSet<>(oldTransitionMap.keySet());
			actions.addAll(newTransitionMap.keySet());

			final Map<ACTION, STATE> resultMap = new HashMap<>();
			for (final ACTION action : actions) {
				final STATE widenedState = combineStates(oldTransitionMap.get(action), newTransitionMap.get(action));
				if (widenedState != null) {
					resultMap.put(action, widenedState);
				}
			}
			widenedInterferenceMap.put(threadName, resultMap);
		}
		return widenedInterferenceMap;
	}

	private STATE combineStates(final STATE state1, final STATE state2) {
		if (state1 == null && state2 == null) {
			return null;
		}
		if (state1 == null) {
			return state2;
		}
		if (state2 == null) {
			return state1;
		}
		return (STATE) ((RelationalInterferingDomain) mDomain).getUnderlyingDomain().getWideningOperator().apply(state1,
				state2);
	}

	private DisjunctiveAbstractState<STATE> getInitialState(final String procedure) {
		int forks = 0;
		final Set<String> forkingThreads =
				((RelationalInterferingDomain) mDomain).interferenceState().getActiveIfActive().getImage(procedure);
		DisjunctiveAbstractState<STATE> result = null;
		// collect states which fork this thread
		for (final LOC loc : mAnalyzer.getForkLocations(procedure)) {
			final DisjunctiveAbstractState<STATE> state = mStateStorage.getAbstractState(loc);
			if (state == null) {
				result = null;
				break;
			}
			forks++;
			final DisjunctiveAbstractState<STATE> clearedState = removeLocalVars(state);
			result = result == null ? clearedState : result.union(clearedState);
		}
		// combine forking states
		if (result != null) {
			final STATE forkedInitialState = constructForkedInitialState(result, forkingThreads, procedure, forks);
			return new DisjunctiveAbstractState<>(mMaxParallelStates, forkedInitialState);
		}

		// no forking threads, construct fresh state (must be main-thread)
		var bottomState = (STATE) ((RelationalInterferingDomain) mDomain).createBottomPreconditionState();
		bottomState = (STATE) ((RelationalInterferingState) bottomState).incrementThread(procedure);
		return new DisjunctiveAbstractState<>(mMaxParallelStates, bottomState);
	}

	private STATE constructForkedInitialState(final DisjunctiveAbstractState<STATE> result,
			final Set<String> forkingThreads, final String procedure, final int forks) {
		final Set<STATE> forkStates = result.getStates();
		STATE unionState = forkStates.iterator().next();
		for (final STATE forkState : forkStates) {
			if (unionState != unionState) {
				unionState = FixpointEngineConcurrentUtils.unionOnSharedVariables(unionState, forkState);
			}
		}
		for (final String thread : forkingThreads) {
			((RelationalInterferingState) unionState).getThreadInstanceState().setActive(thread);
		}
		if (forks > 1) {
			((RelationalInterferingState) unionState).getThreadInstanceState().setInf(procedure);
		}
		final STATE afterInterferences =
				(STATE) ((RelationalInterferingPostOperator) ((RelationalInterferingDomain) mDomain).getPostOperator())
						.stateAfterInterferences((RelationalInterferingState) unionState, procedure);
		return afterInterferences;
	}

	private DisjunctiveAbstractState<STATE> removeLocalVars(final DisjunctiveAbstractState<STATE> state) {
		final List<IProgramVarOrConst> varsToRemove =
				state.getVariables().stream().filter(ILocalProgramVar.class::isInstance).collect(Collectors.toList());
		return state.removeVariables(varsToRemove);
	}

}
