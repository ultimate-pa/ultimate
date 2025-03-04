package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
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
	}

	@Override
	public AbsIntResult<STATE, ACTION, LOC> run(final Collection<? extends LOC> initialNodes, final Script script) {
		mLogger.info("Starting fixpoint engine with domain " + mDomain.getClass().getSimpleName() + " (maxUnwinding="
				+ mMaxUnwindings + ", maxParallelStates=" + mMaxParallelStates + ")");
		mResult = new AbsIntResult<>(script, mDomain, mTransitionProvider, mVarProvider);
		// mDomain.beforeFixpointComputation(mResult.getBenchmark());
		calculateFixpoint(script);
		mResult.saveRootStorage(mStateStorage);
		mResult.saveSummaryStorage(mSummaryMap);
		mLogger.debug("Fixpoint computation completed");
		// mDomain.afterFixpointComputation(mResult);
		assert areStatesInterferenceFree();
		return mResult;
	}

	// TODO: make it custom with our interference methods
	private boolean areStatesInterferenceFree() {
		final Map<LOC, DisjunctiveAbstractState<STATE>> loc2States = mResult.getLoc2States().entrySet().stream()
				.collect(
						Collectors.toMap(Entry::getKey, x -> DisjunctiveAbstractState.createDisjunction(x.getValue())));
		for (final Entry<LOC, DisjunctiveAbstractState<STATE>> entry : loc2States.entrySet()) {
			final DisjunctiveAbstractState<STATE> state = removeLocalVars(entry.getValue());
			for (final ACTION interfering : mAnalyzer.getInterferingWrites(entry.getKey())) {
				final DisjunctiveAbstractState<STATE> preInterfering = loc2States
						.get(mTransitionProvider.getSource(interfering));
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
//		AbstractInterferenceState<STATE, ACTION> interferenceState;
		int iteration = 1;
		final Set<LOC> reachableErrorLocations = new HashSet<>();
		while (true) {
			mLogger.error("Starting thread modular fixpoint engine iteration " + iteration);
//			interferenceState = new AbstractInterferenceState<STATE, ACTION>(
//					((RelationalInterferingDomain) mDomain).interferenceState());
			final var interferenceState = new AbstractInterferenceState<STATE, ACTION>(
					((RelationalInterferingDomain) mDomain).interferenceState());
			mLogger.warn("OLD:" + interferenceState.interferenceStrings());
			mLogger.error("\n");
			mLogger.error("Interference Set:");
			for (final String termString : interferenceState.interferenceStrings()) {
				mLogger.error(termString);
			}
			mLogger.error("\n");
			final Map<String, AbsIntResult<STATE, ACTION, LOC>> resultSet = new HashMap<>();
			for (final String procedure : mAnalyzer.getTopologicalProcedureOrder()) {
				mLogger.error("Analysing thread " + procedure);
				final DisjunctiveAbstractState<STATE> initialState = getInitialState(procedure);
				final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> paramsWithInterferences = mParams
						.setStorage(mStateStorage.copy())
						.setVariableProvider(new InterferingVariableProvider<>(mVarProvider, initialState));
				final IFixpointEngine<STATE, ACTION, VARDECL, LOC> fixpointEngine = mFixpointEngineFactory
						.constructFixpointEngine(paramsWithInterferences);
				final AbsIntResult<STATE, ACTION, LOC> threadResult = fixpointEngine
						.run(Set.of(mEntryLocs.get(procedure)), script);

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

			final AbstractInterferenceState<STATE, ACTION> newInterferenceState = ((RelationalInterferingDomain) mDomain)
					.interferenceState();

			// interference fixpoint reached
			if (newInterferenceState.isSubsetOf(interferenceState)) {
				mLogger.error("\n");
				mLogger.error("\n");
				mLogger.error("Fixpoint after " + iteration + " iterations found.");
				mLogger.error(newInterferenceState.interferenceStrings());
				mLogger.error("implies");
				mLogger.error(interferenceState.interferenceStrings());
				mLogger.error("\n");
				mLogger.error("\n");
				printResultCfgAnnotations(resultSet);
				break;
			}
			mLogger.error(newInterferenceState.interferenceStrings());
			mLogger.error("doesnt imply");
			mLogger.error(interferenceState.interferenceStrings());
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
		final var oldMap = oldInterference.getInterferenceMapHashRelation();
		final var newMap = newInterference.getInterferenceMapHashRelation();
		for (final String threadName : oldMap.keySet()) {
			widenedInterferenceMap.put(threadName, new HashMap<>());
			final var oldTransitionMap = oldMap.get(threadName);
			final var newTransitionMap = newMap.get(threadName);
			if (oldTransitionMap == null && newTransitionMap == null) {
				continue;
			}
			if (oldTransitionMap == null) {
				for (final ACTION action : newTransitionMap.keySet()) {
					widenedInterferenceMap.get(threadName).put(action, newTransitionMap.get(action));
				}
				continue;
			}
			if (newTransitionMap == null) {
				for (final ACTION action : oldTransitionMap.keySet()) {
					widenedInterferenceMap.get(threadName).put(action, oldTransitionMap.get(action));
				}
				continue;
			}
			for (final ACTION interferenceTransition : oldTransitionMap.keySet()) {
				final boolean firstNull = oldTransitionMap.get(interferenceTransition) == null;
				final boolean secondNull = newTransitionMap.get(interferenceTransition) == null;
				if (firstNull && secondNull) {
					continue;
				}
				if (!firstNull && secondNull) {
					widenedInterferenceMap.get(threadName).put(interferenceTransition,
							newTransitionMap.get(interferenceTransition));
					continue;
				}
				if (firstNull && !secondNull) {
					widenedInterferenceMap.get(threadName).put(interferenceTransition,
							oldTransitionMap.get(interferenceTransition));
					continue;
				}
				widenedInterferenceMap.get(threadName).put(interferenceTransition,
						(STATE) ((RelationalInterferingDomain) mDomain).getUnderlyingDomain().getWideningOperator()
								.apply(oldTransitionMap.get(interferenceTransition),
										newTransitionMap.get(interferenceTransition)));
			}
		}
		return widenedInterferenceMap;
	}

	private DisjunctiveAbstractState<STATE> getInitialState(final String procedure) {
		final Set<String> forkingThreads = ((RelationalInterferingDomain) mDomain).interferenceState()
				.getActiveIfActive().getImage(procedure);
		DisjunctiveAbstractState<STATE> result = null;
		for (final LOC loc : mAnalyzer.getForkLocations(procedure)) {
			final DisjunctiveAbstractState<STATE> state = mStateStorage.getAbstractState(loc);
			if (state == null) {
				result = null;
				break;
			}
			final DisjunctiveAbstractState<STATE> clearedState = removeLocalVars(state);
			result = result == null ? clearedState : result.union(clearedState);
		}
		if (result != null) {

			final Set<STATE> forkStates = result.getStates();
//			STATE bottomState = mDomain.createBottomState();
			STATE unionState = forkStates.iterator().next();
			for (final STATE forkState : forkStates) {
				unionState = FixpointEngineConcurrentUtils.unionOnSharedVariables(unionState, forkState);
			}
			((RelationalInterferingState) unionState).getThreadInstanceState().reset();

			for (final String thread : forkingThreads) {
				((RelationalInterferingState) unionState).getThreadInstanceState().setActive(thread);
			}
			for (int i = 0; i < (int) ((RelationalInterferingDomain) mDomain).interferenceState()
					.getActiveThreadInstances().get(procedure) - 1; i++) {
				((RelationalInterferingState) unionState).getThreadInstanceState().incrementThread(procedure);
			}
			final STATE afterInterferences = (STATE) ((RelationalInterferingPostOperator) ((RelationalInterferingDomain) mDomain)
					.getPostOperator()).stateAfterInterferences((RelationalInterferingState) unionState, procedure);

			return new DisjunctiveAbstractState<>(mMaxParallelStates, afterInterferences);
		}

		final var bottomState = (STATE) ((RelationalInterferingDomain) mDomain).createBottomPreconditionState();
		((RelationalInterferingState) bottomState).getThreadInstanceState().incrementThread(procedure);
		return new DisjunctiveAbstractState<>(mMaxParallelStates, bottomState);
	}

	private DisjunctiveAbstractState<STATE> removeLocalVars(final DisjunctiveAbstractState<STATE> state) {
		// TODO: Is it safe to remove all not IProgramNonOldVar, or should we just
		// remove the ILocalProgramVars?
		final List<IProgramVarOrConst> varsToRemove = state.getVariables().stream()
				.filter(x -> !(x instanceof IProgramNonOldVar)).collect(Collectors.toList());
		return state.removeVariables(varsToRemove);
	}

	private void printResultCfgAnnotations(final Map<String, AbsIntResult<STATE, ACTION, LOC>> resultSet) {
		final Set<IcfgLocation> seenLocs = new HashSet<>();
		for (final String thread : resultSet.keySet()) {
			mLogger.error("\n");
			mLogger.error("\n");
			mLogger.error("Annotated CFG for " + thread);
			final var result = resultSet.get(thread);
			for (final LOC location : result.getLoc2Term().keySet()) {
				final var incoming = location.getIncomingNodes();
				if (incoming.size() == 0) {
					printCfgTree(location, result, seenLocs);
				}
			}
		}
	}

	private void printCfgTree(final IcfgLocation loc, final AbsIntResult<STATE, ACTION, LOC> result,
			final Set<IcfgLocation> seenLocs) {
		if (seenLocs.contains(loc)) {
			return;
		}
		seenLocs.add(loc);
		final var terms = result.getLoc2Term().get(loc);
		if (terms != null) {
			mLogger.error("[STATE: " + terms + "]");
			mLogger.error("[THREADS: " + ((RelationalInterferingState) result.getLoc2SingleStates().get(loc))
					.getThreadInstanceState().toString() + "]");
//			if (loc.getOutgoingNodes().getFirst().getOutgoingNodes().isEmpty()) {
//				return;
//			}
			if (loc.getOutgoingEdges().size() != 0) {
				mLogger.error("|");
				mLogger.error(loc.getOutgoingEdges());
				mLogger.error("|");
				mLogger.error("v");
			}
		}
		for (final IcfgLocation childLoc : loc.getOutgoingNodes()) {
			printCfgTree(childLoc, result, seenLocs);
		}
	}
}
