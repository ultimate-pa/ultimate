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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
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
		implements
		IFixpointEngine<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> {

	private final int mMaxUnwindings;
	private final int mMaxInterferenceFixpointUnwindings;
	private final int mMaxParallelStates;

	private final ITransitionProvider<ACTION, LOC> mTransitionProvider;
	private final IAbstractStateStorage<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mStateStorage;
	private final GuardedInterferenceDomain<UNDERLYINGSTATE, ACTION, LOC> mDomain;
	private final IAbstractDomain<UNDERLYINGSTATE, ACTION> mUnderlyingDomain;
	private final IVariableProvider<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION> mVarProvider;
	private final ILogger mLogger;

	private AbsIntResult<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mResult;
	private final SummaryMap<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> mSummaryMap;

	private final IFixpointEngineFactory<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> mFixpointEngineFactory;
	private final Map<String, ? extends LOC> mEntryLocs;
	private final FixpointEngineParameters<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> mParams;
	private final ConcurrentIcfgAnalyzer<ACTION, LOC> mAnalyzer;
	private final FixpointPrintHelper<UNDERLYINGSTATE, ACTION, LOC> mPrinter;
	private final String mLocationAbstraction;
	private final GuardedInterferenceApplier<UNDERLYINGSTATE, ACTION, LOC> mItfApplier;
	int locationCounter = 0;

	public FixpointEngineGuardedConcurrent(final FixpointEngineParameters<UNDERLYINGSTATE, ACTION, VARDECL, LOC> params,
			final IFixpointEngineFactory<UNDERLYINGSTATE, ACTION, VARDECL, LOC> factory,
			final IIcfg<? extends LOC> icfg, final String locationAbstraction) {
		if (params == null || !params.isValid()) {
			throw new IllegalArgumentException("invalid params");
		}
//		mMaxUnwindings = mParams.getMaxUnwindings();
//		mMaxParallelStates = mParams.getMaxParallelStates();
		mMaxUnwindings = 8;
		mMaxInterferenceFixpointUnwindings = 16;
		mMaxParallelStates = 1000;
		GuardedInterferenceApplier.iterationsReached = 0;
		GuardedInterferenceDomainStateDisj.maxSizeReached = 0;
		mEntryLocs = icfg.getProcedureEntryNodes();
		final AbstractLocationMap<LOC> absMap = computeLocationAbstraction(locationAbstraction);
		mDomain = new GuardedInterferenceDomain<>(icfg, params.getAbstractDomain(), params.getLogger(), absMap,
				mMaxParallelStates, mMaxInterferenceFixpointUnwindings);
		mUnderlyingDomain = params.getAbstractDomain();
		// TODO: not sure this is sound
		mParams = (FixpointEngineParameters<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC>) params
				.setDomain((IAbstractDomain<UNDERLYINGSTATE, ACTION>) mDomain);

		mLogger = mParams.getLogger();
		mTransitionProvider = mParams.getTransitionProvider();
		mStateStorage = mParams.getStorage();
		mVarProvider = mParams.getVariableProvider();
		mSummaryMap = new SummaryMap<>(mTransitionProvider, mLogger);

		mFixpointEngineFactory = (IFixpointEngineFactory<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC>) factory;

		mAnalyzer = new ConcurrentIcfgAnalyzer<>(icfg);
		mPrinter = new FixpointPrintHelper<>();
		mLocationAbstraction = locationAbstraction;
		final var applier = ((GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain
				.getPostOperator()).getItfApplier();
		mItfApplier = applier;
	}

	private AbstractLocationMap<LOC> computeLocationAbstraction(final String locationAbstraction) {
		// TODO: enum for setting strings
		// TODO: parametrize countervalues
		final AbstractLocationMap<LOC> absMap = switch (locationAbstraction) {
		case "Singleton" -> new AbstractLocationMap<>((l -> 1), mEntryLocs);
		case "Fully precise" -> new AbstractLocationMap<>((l -> locationCounter++), mEntryLocs);
		case "Heuristic splitting" -> new AbstractLocationMap<>(l -> {
			final var incoming = l.getIncomingEdges();
			for (final IcfgEdge icfgEdge : incoming) {
				if (shouldDifferentiate(icfgEdge.getTransformula())) {
					return locationCounter++;
				}
			}
			return locationCounter;
		}, mEntryLocs);
		default -> new AbstractLocationMap<>((l -> 1), mEntryLocs);
		};
		return absMap;
	}

	private static boolean shouldDifferentiate(final UnmodifiableTransFormula tf) {
		if (tf.isInfeasible() == UnmodifiableTransFormula.Infeasibility.INFEASIBLE) {
			return false;
		}
		if (!tf.getBranchEncoders().isEmpty()) {
			return true;
		}
		final Set<IProgramVar> assigned = tf.getAssignedVars();
		if (assigned.isEmpty()) {
			return true;
		}
		return false;
	}

	@Override
	public AbsIntResult<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> run(
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
				(IAbstractInterpretationResult<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC>) mResult);

		// TODO: to weak right now, make stronger
		// assert areStatesInterferenceFree();
		return mResult;
	}

	// TODO: replace with more precise version mirroring our method of
	// interferences,
	// as this should fail when we get more precise
	private boolean areStatesInterferenceFree() {
		final Map<LOC, DisjunctiveAbstractState<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>>> loc2States = mResult
				.getLoc2States().entrySet().stream().collect(
						Collectors.toMap(Entry::getKey, x -> DisjunctiveAbstractState.createDisjunction(x.getValue())));
		for (final Entry<LOC, DisjunctiveAbstractState<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>>> entry : loc2States
				.entrySet()) {
			final DisjunctiveAbstractState<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>> state = removeLocalVars(
					entry.getValue());
			for (final ACTION interfering : mAnalyzer.getInterferingWrites(entry.getKey())) {
				final DisjunctiveAbstractState<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>> preInterfering = loc2States
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
		int iteration = 1;
		final Set<LOC> reachableErrorLocations = new HashSet<>();
		int fix = 0;
		while (true) {
			mLogger.error("\n");
			mLogger.error("Starting thread modular fixpoint engine iteration " + iteration);
//			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> oldInterferenceState = ((GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain
//					.getPostOperator()).getInterferences();
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> oldInterferenceState = mItfApplier
					.getInterferences();

			mLogger.error("Interference Set we will use:");
			for (final String termString : oldInterferenceState.interferenceStrings()) {
				mLogger.error(termString);
			}
			final Map<String, AbsIntResult<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC>> resultSet = new HashMap<>();
			for (final String procedure : mAnalyzer.getTopologicalProcedureOrder()) {
				final DisjunctiveAbstractState<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>> initialState = getInitialState(
						procedure);
				final FixpointEngineParameters<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> paramsWithInterferences = mParams
						.setStorage(mStateStorage.copy())
						.setVariableProvider(new InterferingVariableProvider<>(mVarProvider, initialState));
				final IFixpointEngine<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, VARDECL, LOC> fixpointEngine = mFixpointEngineFactory
						.constructFixpointEngine(paramsWithInterferences);
				final AbsIntResult<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>, ACTION, LOC> threadResult = fixpointEngine
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

//			((GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain.getPostOperator())
//					.updateInterferences();
			mItfApplier.updateInterferences();
//			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> newInterferenceState = ((GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain
//					.getPostOperator()).getInterferences();
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> newInterferenceState = mItfApplier
					.getInterferences();

			// interference fixpoint reached
			if (newInterferenceState.isSubsetOf(oldInterferenceState)) {
				fix++;
				if (fix == 3) {
					mPrinter.printCfgResults(mLogger, newInterferenceState, newInterferenceState, iteration, resultSet,
							mEntryLocs, mDomain.getAbstractLocationMap(), script);
					mLogger.error("max ITF fixpoint iterations: " + GuardedInterferenceApplier.iterationsReached);
					break;
				}
			} else {
				fix = 1;
			}
			if (iteration > mMaxUnwindings) {
//				((GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain.getPostOperator())
//						.setInterferences(calcWidenedInterferences(oldInterferenceState, newInterferenceState));
				mItfApplier.setInterferences(calcWidenedInterferences(oldInterferenceState, newInterferenceState));
				mLogger.error("DID WIDENING ON INTERFERENCES.");
			}
			iteration++;
		}
	}

	private AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> calcWidenedInterferences(
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> oldInterference,
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> newInterference) {
		// 1) union of all threadNames
		final Set<String> allThreads = new HashSet<>(oldInterference.getInterferenceMapHashRelation().keySet());
		allThreads.addAll(newInterference.getInterferenceMapHashRelation().keySet());

		// 2) union of all actions
		final Map<ACTION, Interference<UNDERLYINGSTATE, ACTION, LOC>> oldMap = oldInterference.getIdentifyMap();
		final Map<ACTION, Interference<UNDERLYINGSTATE, ACTION, LOC>> newMap = newInterference.getIdentifyMap();
		final Set<ACTION> allActions = new HashSet<>(oldMap.keySet());
		allActions.addAll(newMap.keySet());

		// 3) new result
		final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> resultInterferenceState = new AbstractInterferenceState<>(
				allThreads);

		// 4) for each action in union
		for (final ACTION action : allActions) {
			final Interference<UNDERLYINGSTATE, ACTION, LOC> oldI = oldMap.get(action);
			final Interference<UNDERLYINGSTATE, ACTION, LOC> newI = newMap.get(action);

			UNDERLYINGSTATE widened = null;
			ThreadInstanceCounter combinedThreads = null;
			if (oldI == null && newI != null) {
				widened = newI.state();
				combinedThreads = newI.threadcounter();
			} else if (oldI != null && newI == null) {
				widened = oldI.state();
				combinedThreads = oldI.threadcounter();
			} else if (oldI != null && newI != null) {
				widened = combineStates(oldI.state(), newI.state());
				combinedThreads = oldI.threadcounter().union(newI.threadcounter());
			}

			if (widened == null) {
				continue;
			}

			resultInterferenceState.addInterference(action.getSource().getProcedure(), action, widened,
					combinedThreads);
		}

		return resultInterferenceState;
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

	private DisjunctiveAbstractState<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>> getInitialState(
			final String procedure) {
		DisjunctiveAbstractState<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>> result = null;
		final var allForkLocs = new HashSet<LOC>();
		for (final LOC loc : mAnalyzer.getForkLocations(procedure)) {
			final DisjunctiveAbstractState<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>> state = mStateStorage
					.getAbstractState(loc);
			if (state == null) {
				result = null;
				break;
			}
			allForkLocs.add(loc);
			final var clearedState = removeLocalVars(state);
			result = (result == null) ? clearedState : result.union(clearedState);
		}
		// combine forking states
		if (result != null) {
			int forks = 0;
			boolean isCircular = false;
			boolean multipleThreads = false;
			for (final LOC forkLoc : allForkLocs) {
				forks++;
				for (final IcfgEdge forkEdge : forkLoc.getOutgoingEdges()) {
					if (forkEdge instanceof final ForkThreadCurrent fork1) {
						final boolean circular = ((GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain
								.getPostOperator()).isCircular(fork1, fork1.getSource().getIncomingEdges(), 0);
						if (circular) {
							isCircular = true;
						}
					}
				}

			}
			if (forks > 1 || isCircular) {
				multipleThreads = true;
			}
			final GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC> forkedInitialState = constructForkedInitialState(
					result, procedure, multipleThreads);
			GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC> initialState = null;
			if (multipleThreads) {
				initialState = forkedInitialState.setThreadsInf(List.of(procedure));
			} else {
				initialState = forkedInitialState.setThreadsActive(List.of(procedure));
			}
			// TODO:
			return new DisjunctiveAbstractState<>(mMaxParallelStates, initialState);
		}

		// no forking threads, construct fresh state (must be main/start-thread)
		var bottomState = mDomain.createBottomPreconditionState();
		bottomState = bottomState.setThreadsActive(List.of(procedure));
		final var locMap = mDomain.getAbstractLocationMap();
		final var entryLoc = mEntryLocs.get(procedure);
		bottomState = bottomState.initializeLocation(entryLoc, locMap,
				mAnalyzer.getTopologicalProcedureOrder().stream().collect(Collectors.toSet()));
		return new DisjunctiveAbstractState<>(bottomState.maxSize(), bottomState);
	}

	private GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC> constructForkedInitialState(
			final DisjunctiveAbstractState<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>> result,
			final String procedure, final boolean multipleThreads) {
		final Set<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>> forkStates = result.getStates();
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> initialStates = new HashSet<>();
		for (final GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC> forkState : forkStates) {
			// filter only states from forking threads whwere forked thread still at start position
			// (we would do self interference by proxy otherwise
			for (final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> singleStateRecord : forkState
					.getStates()) {
				final var entryLoc = singleStateRecord.abstractLocationState().getTracker()
						.getLocationForThread(procedure);
				final var globalMap = singleStateRecord.abstractLocationState().getLocationMap();
				if (entryLoc.contains(globalMap.getAbstractLocation(mEntryLocs.get(procedure)))) {
					initialStates.add(removeLocalVars(singleStateRecord));
				} else if (multipleThreads) {
					initialStates.add(removeLocalVars(singleStateRecord));
				}
			}
		}
		// TODO: unify them into one state
		final GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC> initialDisj = new GuardedInterferenceDomainStateDisj<>(
				mUnderlyingDomain, initialStates, mMaxParallelStates);
		final var debugState = initialDisj.getSingleState();
		if (initialDisj.getSingleState() == null) {
			return initialDisj;
		}
//		final GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC> afterInterferences = ((GuardedInterferenceDomainPostOperator<UNDERLYINGSTATE, ACTION, LOC>) mDomain
//				.getPostOperator()).stateAfterInterferences(initialDisj, procedure);
		final GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC> afterInterferences = mItfApplier
				.stateAfterInterferences(initialDisj, procedure);

		final var debugState2 = afterInterferences.getSingleState();
		return afterInterferences;
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

	private DisjunctiveAbstractState<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>> removeLocalVars(
			final DisjunctiveAbstractState<GuardedInterferenceDomainStateDisj<UNDERLYINGSTATE, ACTION, LOC>> state) {
		final List<IProgramVarOrConst> varsToRemove = state.getVariables().stream()
				.filter(ILocalProgramVar.class::isInstance).collect(Collectors.toList());
		if (varsToRemove.isEmpty()) {
			return state;
		}
		return state.removeVariables(varsToRemove);
	}
}
