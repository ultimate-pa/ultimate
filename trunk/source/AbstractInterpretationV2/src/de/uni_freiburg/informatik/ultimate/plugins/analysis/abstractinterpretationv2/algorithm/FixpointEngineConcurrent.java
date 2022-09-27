package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class FixpointEngineConcurrent<STATE extends IAbstractState<STATE>, ACTION, VARDECL, LOC>
		implements IFixpointEngine<STATE, ACTION, VARDECL, LOC> {
	private final int mMaxUnwindings;
	private final int mMaxParallelStates;

	private final ITransitionProvider<ACTION, LOC> mTransitionProvider;
	private final IAbstractStateStorage<STATE, ACTION, LOC> mStateStorage;
	private final IAbstractDomain<STATE, ACTION> mDomain;
	private final IVariableProvider<STATE, ACTION> mVarProvider;
	private final IDebugHelper<STATE, ACTION, VARDECL, LOC> mDebugHelper;
	private final IProgressAwareTimer mTimer;
	private final ILogger mLogger;

	private AbsIntResult<STATE, ACTION, LOC> mResult;
	private final SummaryMap<STATE, ACTION, LOC> mSummaryMap;

	private final IFixpointEngine<STATE, ACTION, VARDECL, LOC> mFixpointEngine;
	private final Map<String, LOC> mEntryLocs;

	public FixpointEngineConcurrent(final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> params,
			final Map<String, LOC> entryLocs, final IFixpointEngine<STATE, ACTION, VARDECL, LOC> fxpe) {
		if (params == null || !params.isValid()) {
			throw new IllegalArgumentException("invalid params");
		}
		mTimer = params.getTimer();
		mLogger = params.getLogger();
		mTransitionProvider = params.getTransitionProvider();
		mStateStorage = params.getStorage();
		mDomain = params.getAbstractDomain();
		mVarProvider = params.getVariableProvider();
		mDebugHelper = params.getDebugHelper();
		mMaxUnwindings = params.getMaxUnwindings();
		mMaxParallelStates = params.getMaxParallelStates();
		mSummaryMap = new SummaryMap<>(mTransitionProvider, mLogger);
		mFixpointEngine = fxpe;
		mEntryLocs = entryLocs;
	}

	@Override
	public AbsIntResult<STATE, ACTION, LOC> run(final Collection<? extends LOC> initialNodes, final Script script) {
		mLogger.info("Starting fixpoint engine with domain " + mDomain.getClass().getSimpleName() + " (maxUnwinding="
				+ mMaxUnwindings + ", maxParallelStates=" + mMaxParallelStates + ")");
		mResult = new AbsIntResult<>(script, mDomain, mTransitionProvider, mVarProvider);
		mDomain.beforeFixpointComputation(mResult.getBenchmark());
		calculateFixpoint(mEntryLocs, script);
		mResult.saveRootStorage(mStateStorage);
		mResult.saveSummaryStorage(mSummaryMap);
		mLogger.debug("Fixpoint computation completed");
		mDomain.afterFixpointComputation(mResult);
		return mResult;
	}

	private void calculateFixpoint(final Map<String, LOC> entryLocs, final Script script) {
		Map<LOC, DisjunctiveAbstractState<STATE>> interferences = new HashMap<>();
		int iteration = 1;
		final Set<LOC> addedErrorLocations = new HashSet<>();
		while (true) {
			mLogger.info("Starting outer Fixpoint iteration number " + iteration);
			final Map<LOC, DisjunctiveAbstractState<STATE>> newInterferences = new HashMap<>(interferences);
			for (final Entry<String, LOC> entry : entryLocs.entrySet()) {
				final AbsIntResult<STATE, ACTION, LOC> result =
						mFixpointEngine.runWithInterferences(Set.of(entry.getValue()), script, interferences);

				// Merge mStateStorage and result.getLoc2States
				for (final var locAndStates : result.getLoc2States().entrySet()) {
					mStateStorage.addAbstractState(locAndStates.getKey(),
							DisjunctiveAbstractState.createDisjunction(locAndStates.getValue()));
				}

				// TODO: Compute new interferences

				for (final var counterExample : result.getCounterexamples()) {
					final var execution = counterExample.getAbstractExecution();
					final var errorLocation = execution.get(execution.size() - 1).getSecond();
					if (!addedErrorLocations.add(errorLocation)) {
						mResult.addCounterexample(counterExample);
					}
				}
			}

			if (interferencesAreEqual(interferences, newInterferences)) {
				break;
			}
			interferences = newInterferences;
			iteration++;
		}
	}

	private Map<ACTION, DisjunctiveAbstractState<STATE>>
			getRelevantPostStates(final HashRelation<ACTION, IProgramVarOrConst> sharedWritesToVars) {
		final Map<ACTION, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
		final Map<LOC, Set<DisjunctiveAbstractState<STATE>>> loc2States = mStateStorage.computeLoc2States();
		for (final Entry<ACTION, HashSet<IProgramVarOrConst>> entry : sharedWritesToVars.entrySet()) {
			// TODO: Previously we applied the post-operator to the pre-state, why?
			final ACTION write = entry.getKey();
			final DisjunctiveAbstractState<STATE> stateAfterWrite =
					flattenAbstractStates(loc2States.get(mTransitionProvider.getTarget(write)));
			final Set<IProgramVarOrConst> varsToRemove =
					DataStructureUtils.difference(stateAfterWrite.getVariables(), entry.getValue());
			result.put(write, stateAfterWrite.removeVariables(varsToRemove));
		}
		return result;
	}

	private DisjunctiveAbstractState<STATE>
			flattenAbstractStates(final Set<DisjunctiveAbstractState<STATE>> setOfStates) {
		if (setOfStates == null || setOfStates.isEmpty()) {
			return new DisjunctiveAbstractState<>();
		}

		final Iterator<DisjunctiveAbstractState<STATE>> iterator = setOfStates.iterator();
		DisjunctiveAbstractState<STATE> result = iterator.next();
		while (iterator.hasNext()) {
			result = unionIfNonEmpty(result, iterator.next());
		}
		return result;
	}

	private DisjunctiveAbstractState<STATE> unionIfNonEmpty(final DisjunctiveAbstractState<STATE> stateOne,
			final DisjunctiveAbstractState<STATE> stateTwo) {
		if (stateOne.getStates().isEmpty()) {
			return stateTwo;
		}
		if (stateTwo.getStates().isEmpty()) {
			return stateOne;
		}
		return stateOne.union(stateTwo);
	}

	private boolean interferencesAreEqual(final Map<LOC, DisjunctiveAbstractState<STATE>> oldInts,
			final Map<LOC, DisjunctiveAbstractState<STATE>> newInts) {
		if (oldInts.size() != newInts.size()) {
			return false;
		}
		return oldInts.keySet().stream().allMatch(x -> oldInts.get(x).isEqualTo(newInts.get(x)));
	}

	@Override
	public AbsIntResult<STATE, ACTION, LOC> runWithInterferences(final Collection<? extends LOC> start,
			final Script script, final Map<LOC, DisjunctiveAbstractState<STATE>> interferences) {
		throw new UnsupportedOperationException(
				getClass().getSimpleName() + " cannot be used inside concurrent abstract interpretation.");
	}
}
