package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
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
		// assert areStatesInterferenceFree();
		return mResult;
	}

	private void calculateFixpoint(final Script script) {
		RelationalInterferenceState interferenceState;
		// Map<LOC, DisjunctiveAbstractState<STATE>> interferences = new HashMap<>();
		int iteration = 1;
		int fix = 0;
		final Set<LOC> reachableErrorLocations = new HashSet<>();
		while (true) {
			mLogger.info("Starting thread modular fixpoint engine iteration " + iteration);
			interferenceState = new RelationalInterferenceState(
					((RelationalInterferingDomain) mDomain).interferenceState().getInterferenceMapHashRelation(),
					((RelationalInterferingDomain) mDomain).interferenceState().getManagedScript());
			mLogger.info("\n");
			mLogger.info("Interference Set:");
			for (final String termString : interferenceState.termStrings()) {
				mLogger.info(termString);
			}
			mLogger.info("\n");
			final Map<String, AbsIntResult<STATE, ACTION, LOC>> resultSet = new HashMap<>();
			for (final String procedure : mAnalyzer.getTopologicalProcedureOrder()) {
				final DisjunctiveAbstractState<STATE> initialState = getInitialState(procedure);
				final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> paramsWithInterferences =
						mParams.setStorage(mStateStorage.copy())
								.setVariableProvider(new InterferingVariableProvider<>(mVarProvider, initialState));
				// TODO: why do we reassign this? needed ?
				// .setDomain((IAbstractDomain<STATE, ACTION>) new RelInterferingDomain(mDomain,
				// mTransitionProvider, interferences));
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

			final RelationalInterferenceState newInterferenceState =
					((RelationalInterferingDomain) mDomain).interferenceState();

			if (interferenceState.implies(newInterferenceState)) {
				fix++;
				if (fix == 2) {
					mLogger.info("Fixpoint after " + iteration + " iterations found.");
					printResultCfgAnnotations(resultSet);
					break;
				}
			} else {
				fix = 0;
			}
			// TODO: Add widening in similar manner
			// Compute the new interferences. Use the newly computed or widen them if necessary.
			// if (iteration < mMaxUnwindings) {
			// interferences = newInterferences;
			// } else {
			// mLogger.info("Applying widenning to the interferences.");
			// interferences = widenInterferences(interferences, newInterferences);
			// }
			iteration++;
		}
	}

	private DisjunctiveAbstractState<STATE> getInitialState(final String procedure) {
		DisjunctiveAbstractState<STATE> result = null;
		for (final LOC loc : mAnalyzer.getForkLocations(procedure)) {
			final DisjunctiveAbstractState<STATE> state = mStateStorage.getAbstractState(loc);
			// TODO: Why ?
			if (state == null) {
				result = null;
				break;
			}
			final DisjunctiveAbstractState<STATE> clearedState = removeLocalVars(state);
			result = result == null ? clearedState : result.union(clearedState);
		}

		// TODO: Clean this up, should be able to reduce the logic here
		final var bottomState = (STATE) ((RelationalInterferingDomain) mDomain).createBottomPreconditionState();
		final var forkingThreads =
				((RelationalInterferingDomain) mDomain).threadInstanceCounterFactory().computeForkingThreads(procedure);
		for (final String thread : forkingThreads) {
			((RelationalInterferingState) bottomState).getThreadInstanceState().incrementThread(thread);
		}
		((RelationalInterferingState) bottomState).getThreadInstanceState().incrementThread(procedure);

		if (result != null) {
			final DisjunctiveAbstractState<STATE> disjBottomState =
					new DisjunctiveAbstractState<>(mMaxParallelStates, bottomState);
			final DisjunctiveAbstractState<STATE> compatibleState = removeLocalVars(disjBottomState);
			result = result.intersect(compatibleState);
		}

		// final STATE initialStateWithPrecondition =
		// (STATE) ((RelInterferingDomain) mDomain).createBottomPreconditionState();
		return result != null ? result : new DisjunctiveAbstractState<>(mMaxParallelStates, bottomState);
	}

	private DisjunctiveAbstractState<STATE> removeLocalVars(final DisjunctiveAbstractState<STATE> state) {
		// TODO: Is it safe to remove all not IProgramNonOldVar, or should we just remove the ILocalProgramVars?
		final List<IProgramVarOrConst> varsToRemove = state.getVariables().stream()
				.filter(x -> !(x instanceof IProgramNonOldVar)).collect(Collectors.toList());
		return state.removeVariables(varsToRemove);
	}

	private void printResultCfgAnnotations(final Map<String, AbsIntResult<STATE, ACTION, LOC>> resultSet) {
		for (final String thread : resultSet.keySet()) {
			mLogger.warn("Annotated CFG for " + thread);
			final var result = resultSet.get(thread);
			for (final LOC location : result.getLoc2Term().keySet()) {
				final var incoming = location.getIncomingNodes();
				if (incoming.size() == 0) {
					printCfgTree(location, result);
				}
			}
		}
	}

	private void printCfgTree(final IcfgLocation loc, final AbsIntResult<STATE, ACTION, LOC> result) {
		final var terms = result.getLoc2Term().get(loc);
		if (terms != null) {
			mLogger.error("[STATE: " + terms + "]");
			mLogger.error("[THREADS: " + ((RelationalInterferingState) result.getLoc2SingleStates().get(loc))
					.getThreadInstanceState().toString() + "]");
			if (loc.getOutgoingEdges().size() != 0) {
				mLogger.error("|");
				mLogger.error(loc.getOutgoingEdges());
				mLogger.error("|");
				mLogger.error("v");
			}
		}
		for (final IcfgLocation childLoc : loc.getOutgoingNodes()) {
			printCfgTree(childLoc, result);
		}
	}
}
