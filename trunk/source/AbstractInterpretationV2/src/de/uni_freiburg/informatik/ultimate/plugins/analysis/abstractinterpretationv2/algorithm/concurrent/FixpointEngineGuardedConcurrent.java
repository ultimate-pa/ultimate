package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ForkThreadCurrent;

// TODO: fix nondeterminism caused by random union orders and/or widening!
public class FixpointEngineGuardedConcurrent<UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, VARDECL, LOC extends IcfgLocation>
		implements IFixpointEngine<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> {

	private final int mMaxUnwindings;
	private final int mMaxInterferenceFixpointUnwindings;
	private final int mMaxParallelStates;

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
	private final Map<String, Integer> mPerThreadLocationCounterMap = new HashMap<>();
	private int mIteration = 0;

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
		final AbstractLocationMap<LOC> absMap = computeLocationAbstraction(locationAbstraction, services, icfg);
		mUnderlyingDomain = params.getAbstractDomain();
		mDomain = new GuardedInterferenceDomain<>(icfg, mUnderlyingDomain, params.getLogger(), absMap,
				mMaxParallelStates, mMaxInterferenceFixpointUnwindings);
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
		mPrinter = new FixpointPrintHelper<>();
		mLocationAbstraction = locationAbstraction;
		final var applier = ((GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain
				.getPostOperator()).getItfApplier();
		mItfApplier = applier;
	}

	private int getAndIncrementThreadLocationCounter(final String thread) {
		final int counter = mPerThreadLocationCounterMap.getOrDefault(thread, 0);
		mPerThreadLocationCounterMap.put(thread, counter + 1);
		return counter;
	}

	private AbstractLocationMap<LOC> computeLocationAbstraction(final String locationAbstraction,
			final IUltimateServiceProvider services, final IIcfg<? extends LOC> icfg) {
		// TODO: enum for setting strings
		// TODO: parametrize countervalues
		final HeuristicLocationAbstraction<LOC> heuristicsAbstraction = new HeuristicLocationAbstraction<>(services,
				icfg);
		final AbstractLocationMap<LOC> absMap = switch (locationAbstraction) {
		case "Singleton" -> new AbstractLocationMap<>((l -> 1), mEntryLocs);
		case "Fully precise" ->
			new AbstractLocationMap<>((l -> getAndIncrementThreadLocationCounter(l.getProcedure())), mEntryLocs);
		case "Heuristic splitting" -> heuristicsAbstraction.computeLocationAbstraction();
		default -> new AbstractLocationMap<>((l -> 1), mEntryLocs);
		};
		return absMap;

	}

	@Override
	public AbsIntResult run(final Collection<? extends LOC> initialNodes, final Script script) {

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
		assert areStatesInterferenceFree();
		return mResult;
	}

	// TODO: replace with more precise version mirroring our method of
	// interferences,
	// as this should fail when we get more precise
	private boolean areStatesInterferenceFree() {
		final Map<LOC, DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>>> loc2States = mResult
				.getLoc2States().entrySet().stream().collect(
						Collectors.toMap(Entry::getKey, x -> DisjunctiveAbstractState.createDisjunction(x.getValue())));
		for (final Entry<LOC, DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>>> entry : loc2States
				.entrySet()) {
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> state = removeLocalVars(
					entry.getValue());
			for (final ACTION interfering : mAnalyzer.getInterferingWrites(entry.getKey())) {
				final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> preInterfering = loc2States
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
		mIteration = 1;
		final Set<LOC> reachableErrorLocations = new HashSet<>();
		while (true) {
			mLogger.error("\n");
			mLogger.error("Starting thread modular fixpoint engine iteration " + mIteration);
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> oldInterferenceState = mItfApplier
					.getInterferences();

			mLogger.error("Interference Set we will use:");
			for (final String termString : oldInterferenceState.interferenceStrings()) {
				mLogger.error(termString);
			}
			final Map<String, AbsIntResult<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC>> resultSet = new HashMap<>();
			for (final String procedure : mAnalyzer.getTopologicalProcedureOrder()) {
				final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> initialState = getInitialState(
						procedure);
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
			if (newInterferenceState.isSubsetOf(oldInterferenceState)) {
				mPrinter.printCfgResults(mLogger, newInterferenceState, newInterferenceState, mIteration, resultSet,
						mEntryLocs, mDomain.getAbstractLocationMap(), script);
				// debug info for precision losses
				if (GuardedInterferenceApplier.iterationsReached > mMaxInterferenceFixpointUnwindings) {
					mLogger.warn(
							"Possible precision loss, widened during one or more interference fixpoint(s). Iterations: "
									+ GuardedInterferenceApplier.iterationsReached + ", with max being: "
									+ mMaxInterferenceFixpointUnwindings);
				}
				if (mIteration > mMaxUnwindings) {
					mLogger.warn("Possible precision loss, widened interferences because iterations were: " + mIteration
							+ " with max being: " + mMaxUnwindings);
				}
				if (mPrinter.mMaxStatesReached > mMaxParallelStates) {
					mLogger.warn("Used more states than max parallel allowed: " + mPrinter.mMaxStatesReached
							+ " with max being: " + mMaxParallelStates);
				}
				break;
			}
			if (mIteration > mMaxUnwindings) {
				mItfApplier.setInterferences(calcWidenedInterferences(oldInterferenceState, newInterferenceState));
				mLogger.error("DID WIDENING ON INTERFERENCES.");
			}
			mIteration++;
		}
	}

	private AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> calcWidenedInterferences(
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> oldI,
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> newI) {

		final Set<String> allThreads = new HashSet<>(oldI.getInterferenceMapHashRelation().keySet());
		allThreads.addAll(newI.getInterferenceMapHashRelation().keySet());
		final Map<ACTION, Set<Interference<UNDERLYINGSTATE, ACTION, LOC>>> oldMap = oldI.getIdentifyMap();
		final Map<ACTION, Set<Interference<UNDERLYINGSTATE, ACTION, LOC>>> newMap = newI.getIdentifyMap();

		final Set<ACTION> allActions = new HashSet<>(oldMap.keySet());
		allActions.addAll(newMap.keySet());
		final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> result = new AbstractInterferenceState<>(
				allThreads);
		for (final ACTION act : allActions) {

			final Set<Interference<UNDERLYINGSTATE, ACTION, LOC>> oldSet = oldMap.getOrDefault(act,
					Collections.emptySet());
			final Set<Interference<UNDERLYINGSTATE, ACTION, LOC>> newSet = newMap.getOrDefault(act,
					Collections.emptySet());
			if (oldSet.isEmpty() && newSet.isEmpty()) {
				continue;
			}
			final UNDERLYINGSTATE oldAggState = joinAllStates(oldSet);
			final UNDERLYINGSTATE newAggState = joinAllStates(newSet);

			final ThreadInstanceCounter oldAggCnt = joinAllCounters(oldSet);
			final ThreadInstanceCounter newAggCnt = joinAllCounters(newSet);

			UNDERLYINGSTATE widenedState;
			ThreadInstanceCounter widenedCnt;

			if (oldSet.isEmpty()) {
				widenedState = newAggState;
				widenedCnt = newAggCnt;

			} else if (newSet.isEmpty()) {
				widenedState = oldAggState;
				widenedCnt = oldAggCnt;

			} else {
				widenedState = combineStates(oldAggState, newAggState);
				widenedCnt = oldAggCnt.union(newAggCnt);
			}

			result.addInterference(act.getSource().getProcedure(), act, widenedState, widenedCnt);
		}

		return result;
	}

	private UNDERLYINGSTATE joinAllStates(final Set<Interference<UNDERLYINGSTATE, ACTION, LOC>> set) {
		UNDERLYINGSTATE acc = null;
		for (final Interference<UNDERLYINGSTATE, ACTION, LOC> it : set) {
			acc = (acc == null) ? it.state() : acc.union(it.state());
		}
		return acc;
	}

	private ThreadInstanceCounter joinAllCounters(final Set<Interference<UNDERLYINGSTATE, ACTION, LOC>> set) {
		ThreadInstanceCounter acc = null;
		for (final Interference<UNDERLYINGSTATE, ACTION, LOC> it : set) {
			acc = (acc == null) ? it.threadcounter() : acc.union(it.threadcounter());
		}
		return acc;
	}

	private UNDERLYINGSTATE combineStates(final UNDERLYINGSTATE state1, final UNDERLYINGSTATE state2) {
		if (state1 == null && state2 == null) {
			return null;
		}
		if (state1 == null) {
			return state2;
		}
		if (state2 == null) {
			return state1;
		}
		return mDomain.getUnderlyingDomain().getWideningOperator().apply(state1, state2);
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> getInitialState(
			final String procedure) {
		final var allForkLocs = new HashSet<LOC>();
		var result = combineForkingStates(procedure, allForkLocs);
		if (result != null) {
			final boolean multipleThreads = wasForkedMultipleTimes(allForkLocs);
			if (multipleThreads) {
				result = GuardedStateTransformer.setThreadsInf(List.of(procedure), result);
			} else {
				result = GuardedStateTransformer.setThreadsActive(List.of(procedure), result);
			}
			final var forkedInitialState = constructForkedInitialState(result, procedure, multipleThreads);
			return forkedInitialState;
		}
		// no forking threads, construct fresh state (must be main/start-thread)
		return mainThreadEntryState(procedure);
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> combineForkingStates(
			final String procedure, final HashSet<LOC> allForkLocs) {
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> forkStates = new HashSet<>();
		for (final LOC loc : mAnalyzer.getForkLocations(procedure)) {
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> state = mStateStorage
					.getAbstractState(loc);
			if (state == null) {
				return null;
			}
			allForkLocs.add(loc);
			final var movedState = translateForkLocIntoInitialState(loc, state, procedure);
			final var clearedState = removeLocalVars(movedState);
			forkStates.addAll(clearedState.getStates());
		}
		if (forkStates.isEmpty()) {
			return null;
		}
		return DisjunctiveAbstractState.createDisjunction(forkStates, mMaxParallelStates);
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> translateForkLocIntoInitialState(
			final LOC loc,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> inputState,
			final String procedure) {
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> translateDomainStates = new HashSet<>();
		final var globalImmutableMap = inputState.getStates().iterator().next().abstractLocationState()
				.getLocationMap();
		final var proceduresEntryLoc = globalImmutableMap.getEntryLoc(procedure);
		for (final var singleState : inputState.getStates()) {
			final var afterForkLocation = globalImmutableMap
					.getAbstractLocation((LOC) loc.getOutgoingNodes().getFirst());
			final var executedFork = singleState.movedTo(loc.getProcedure(), afterForkLocation);
			final var movedOwnershipLocation = new AbstractLocationState<>(proceduresEntryLoc,
					executedFork.abstractLocationState());
			final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> movedOwnership = new GuardedInterferenceDomainState<>(
					executedFork.state(), executedFork.threadCounter(), movedOwnershipLocation);
			translateDomainStates.add(movedOwnership);
		}
		return DisjunctiveAbstractState.createDisjunction(translateDomainStates, mMaxParallelStates);
	}

	private boolean wasForkedMultipleTimes(final HashSet<LOC> allForkLocs) {
		int forks = 0;
		boolean isCircular = false;
		for (final LOC forkLoc : allForkLocs) {
			forks++;
			for (final IcfgEdge forkEdge : forkLoc.getOutgoingEdges()) {
				if (forkEdge instanceof final ForkThreadCurrent fork1) {
					final boolean circular = ((GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain
							.getPostOperator()).isCircular(fork1);
					if (circular) {
						isCircular = true;
					}
				}
			}

		}
		if (forks > 1 || isCircular) {
			return true;
		}
		return false;
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> mainThreadEntryState(
			final String procedure) {
		var bottomState = mDomain.createBottomPreconditionState();
		bottomState = bottomState.setThreadsActive(List.of(procedure));
		final var locMap = mDomain.getAbstractLocationMap();
		final var entryLoc = mEntryLocs.get(procedure);
		bottomState = bottomState.initializeLocation(entryLoc, locMap,
				mAnalyzer.getTopologicalProcedureOrder().stream().collect(Collectors.toSet()));
		return new DisjunctiveAbstractState<>(mMaxParallelStates, bottomState);
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> constructForkedInitialState(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> result,
			final String procedure, final boolean multipleThreads) {
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> forkStates = result.getStates();
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> initialStates = new HashSet<>();
		for (final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> forkState : forkStates) {
			// filter only states from forking threads whwere forked thread still at start position
			// (we would do self interference by proxy otherwise
			final var entryLoc = forkState.abstractLocationState().getTracker().getLocationForThread(procedure);
			final var globalMap = forkState.abstractLocationState().getLocationMap();
			if (entryLoc.contains(globalMap.getAbstractLocation(mEntryLocs.get(procedure)))) {
				initialStates.add(removeLocalVars(forkState));
			} else if (multipleThreads) {
				initialStates.add(removeLocalVars(forkState));
			}
		}
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> interferenceDomainStates = new LinkedHashSet<>();
		for (final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> guardedInterferenceDomainState : result
				.getStates()) {
			interferenceDomainStates
					.addAll(mItfApplier.stateAfterInterferences(guardedInterferenceDomainState, procedure));
			interferenceDomainStates.add(guardedInterferenceDomainState);
		}
		final var statesCopy = new HashSet<>(interferenceDomainStates);
		for (final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> guardedInterferenceDomainState : statesCopy) {
			interferenceDomainStates
					.addAll(mItfApplier.stateAfterInterferences(guardedInterferenceDomainState, procedure));
			interferenceDomainStates.add(guardedInterferenceDomainState);
		}
		return DisjunctiveAbstractState.createDisjunction(interferenceDomainStates, mMaxParallelStates);
	}

	private GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> removeLocalVars(
			final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> singleStateRecord) {
		final List<IProgramVarOrConst> varsToRemove = singleStateRecord.state().getVariables().stream()
				.filter(ILocalProgramVar.class::isInstance).collect(Collectors.toList());
		if (varsToRemove.isEmpty()) {
			return singleStateRecord;
		}
		return new GuardedInterferenceDomainState<>(singleStateRecord.state().removeVariables(varsToRemove),
				singleStateRecord.threadCounter(), singleStateRecord.abstractLocationState());
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> removeLocalVars(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> state) {
		final List<IProgramVarOrConst> varsToRemove = state.getVariables().stream()
				.filter(ILocalProgramVar.class::isInstance).collect(Collectors.toList());
		if (varsToRemove.isEmpty()) {
			return state;
		}
		return state.removeVariables(varsToRemove);
	}
}
