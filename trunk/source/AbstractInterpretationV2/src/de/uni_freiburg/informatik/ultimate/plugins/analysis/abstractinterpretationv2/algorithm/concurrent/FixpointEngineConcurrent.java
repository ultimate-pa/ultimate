package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiPredicate;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbsIntResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IFixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.SummaryMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class FixpointEngineConcurrent<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, VARDECL, LOC extends IcfgLocation>
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
	private final HashRelation<ACTION, IProgramVarOrConst> mSharedWrites;
	private final List<String> mTopologicalOrder;
	private final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> mParams;
	private final ConcurrentCfgInformation<ACTION, LOC> mInfo;
	private final BiPredicate<LOC, ACTION> mIsInterfering;
	private final DisjunctiveAbstractState<STATE> mTopState;

	public FixpointEngineConcurrent(final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> params,
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
		mInfo = new ConcurrentCfgInformation<>(icfg);
		mSharedWrites = mInfo.getSharedWrites();
		mTopologicalOrder = mInfo.getTopologicalProcedureOrder();
		// TODO: There can be multiple variants of this predicate (e.g. full flow-senstive analysis)
		// This should be probably an argument or setting.
		mIsInterfering = (loc, action) -> mInfo.getInterferingThreads(loc).contains(action.getPrecedingProcedure());
		mTopState = new DisjunctiveAbstractState<>(mMaxParallelStates, mDomain.createTopState());
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
		return mResult;
	}

	private void calculateFixpoint(final Script script) {
		Map<LOC, DisjunctiveAbstractState<STATE>> interferences = new HashMap<>();
		int iteration = 1;
		final Set<LOC> addedErrorLocations = new HashSet<>();
		while (true) {
			mLogger.info("Starting outer Fixpoint iteration number " + iteration);
			for (final String procedure : mTopologicalOrder) {
				final DisjunctiveAbstractState<STATE> initialState = getInitialState(procedure);
				final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> paramsWithInterferences =
						mParams.setStorage(mStateStorage.copy())
								.setVariableProvider(new InterferingVariableProvider<>(mVarProvider, initialState))
								.setDomain(new InterferingDomain<>(mDomain, mTransitionProvider, interferences));
				final IFixpointEngine<STATE, ACTION, VARDECL, LOC> fixpointEngine =
						mFixpointEngineFactory.constructFixpointEngine(paramsWithInterferences);
				final AbsIntResult<STATE, ACTION, LOC> threadResult =
						fixpointEngine.run(Set.of(mEntryLocs.get(procedure)), script);

				// Merge mStateStorage and result.getLoc2States
				for (final var locAndStates : threadResult.getLoc2States().entrySet()) {
					mStateStorage.addAbstractState(locAndStates.getKey(),
							DisjunctiveAbstractState.createDisjunction(locAndStates.getValue()));
				}
				// Add present counterexamples
				for (final var counterExample : threadResult.getCounterexamples()) {
					final var execution = counterExample.getAbstractExecution();
					final var errorLocation = execution.get(execution.size() - 1).getSecond();
					if (addedErrorLocations.add(errorLocation)) {
						mResult.addCounterexample(counterExample);
					}
				}
			}

			final Map<ACTION, DisjunctiveAbstractState<STATE>> relevantPostStates =
					getRelevantPostStates(mSharedWrites);
			final Map<LOC, DisjunctiveAbstractState<STATE>> newInterferences =
					computeNewInterferences(relevantPostStates);

			if (interferencesAreEqual(interferences, newInterferences)) {
				break;
			}
			// Compute the new interferences. Use the newly computed or widen them if necessary.
			interferences =
					iteration < mMaxUnwindings ? newInterferences : widenInterferences(interferences, newInterferences);
			iteration++;
		}
	}

	private Map<LOC, DisjunctiveAbstractState<STATE>> widenInterferences(
			final Map<LOC, DisjunctiveAbstractState<STATE>> interferences1,
			final Map<LOC, DisjunctiveAbstractState<STATE>> interferences2) {
		final IAbstractStateBinaryOperator<STATE> widenOp = mDomain.getWideningOperator();
		final Map<LOC, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
		for (final LOC loc : DataStructureUtils.union(interferences1.keySet(), interferences2.keySet())) {
			final DisjunctiveAbstractState<STATE> state1 = interferences1.get(loc);
			final DisjunctiveAbstractState<STATE> state2 = interferences2.get(loc);
			if (state1 == null) {
				result.put(loc, state2);
			} else if (state2 == null) {
				result.put(loc, state1);
			} else {
				result.put(loc, state1.widen(widenOp, state2));
			}
		}
		return result;
	}

	private DisjunctiveAbstractState<STATE> unionStates(final Stream<DisjunctiveAbstractState<STATE>> states,
			final DisjunctiveAbstractState<STATE> defaultValue) {
		return states.reduce(DisjunctiveAbstractState::union).orElse(defaultValue);
	}

	private DisjunctiveAbstractState<STATE> getInitialState(final String procedure) {
		return unionStates(mInfo.getForkLocations(procedure).stream().map(mStateStorage::getAbstractState), mTopState);
	}

	private Map<LOC, DisjunctiveAbstractState<STATE>>
			computeNewInterferences(final Map<ACTION, DisjunctiveAbstractState<STATE>> relevantPostStates) {
		final Map<LOC, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
		for (final LOC entryLoc : mEntryLocs.values()) {
			new IcfgLocationIterator<>(entryLoc).forEachRemaining(loc -> {
				final DisjunctiveAbstractState<STATE> interferingState = getInterferingState(loc, relevantPostStates);
				if (interferingState != null) {
					result.put(loc, interferingState);
				}
			});
		}
		return result;
	}

	private DisjunctiveAbstractState<STATE> getInterferingState(final LOC loc,
			final Map<ACTION, DisjunctiveAbstractState<STATE>> relevantPostStates) {
		return unionStates(relevantPostStates.keySet().stream().filter(x -> mIsInterfering.test(loc, x))
				.map(relevantPostStates::get), null);
	}

	private Map<ACTION, DisjunctiveAbstractState<STATE>>
			getRelevantPostStates(final HashRelation<ACTION, IProgramVarOrConst> sharedWrites) {
		final Map<ACTION, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
		for (final Entry<ACTION, HashSet<IProgramVarOrConst>> entry : sharedWrites.entrySet()) {
			final ACTION write = entry.getKey();
			final DisjunctiveAbstractState<STATE> preState =
					mStateStorage.getAbstractState(mTransitionProvider.getSource(write));
			final DisjunctiveAbstractState<STATE> postState;
			if (preState == null) {
				// If the source is not present in mStateStorage, fall back to the target
				// TODO: Is it possible that neither the source nor the target are present?
				postState = mStateStorage.getAbstractState(mTransitionProvider.getTarget(write));
			} else {
				postState = preState.apply(mDomain.getPostOperator(), write);
			}
			final Set<IProgramVarOrConst> varsToRemove =
					DataStructureUtils.difference(postState.getVariables(), entry.getValue());
			result.put(write, postState.removeVariables(varsToRemove));
		}
		return result;
	}

	private boolean interferencesAreEqual(final Map<LOC, DisjunctiveAbstractState<STATE>> oldInts,
			final Map<LOC, DisjunctiveAbstractState<STATE>> newInts) {
		if (oldInts.size() != newInts.size()) {
			return false;
		}
		return oldInts.keySet().stream().allMatch(x -> oldInts.get(x).isEqualTo(newInts.get(x)));
	}
}
