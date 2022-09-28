package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
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

	private final IFixpointEngine<STATE, ACTION, VARDECL, LOC> mFixpointEngine;
	private final Map<String, LOC> mEntryLocs;
	private final HashRelation<ACTION, IProgramVar> mSharedWrites;

	public FixpointEngineConcurrent(final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> params,
			final IFixpointEngine<STATE, ACTION, VARDECL, LOC> fxpe, final IIcfg<LOC> icfg) {
		if (params == null || !params.isValid()) {
			throw new IllegalArgumentException("invalid params");
		}
		mLogger = params.getLogger();
		mTransitionProvider = params.getTransitionProvider();
		mStateStorage = params.getStorage();
		mDomain = params.getAbstractDomain();
		mVarProvider = params.getVariableProvider();
		mMaxUnwindings = params.getMaxUnwindings();
		mMaxParallelStates = params.getMaxParallelStates();
		mSummaryMap = new SummaryMap<>(mTransitionProvider, mLogger);
		mFixpointEngine = fxpe;
		mEntryLocs = icfg.getProcedureEntryNodes();
		mSharedWrites = new WriteExtractor<ACTION>(icfg).getWritesToSharedVariables();
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
			// TODO: Iterate in a topological order instead (w.r.t. the forks) to be more precise after the forks
			for (final Entry<String, LOC> entry : mEntryLocs.entrySet()) {
				// TODO: Should we just use run, but with a modified IAbstractPostOperator
				// (that wraps the other one and considers interferences?)
				// Similarly we could have a new IVariableProvider-wrapper that adds a more precise initial state
				// (after the fork)
				final AbsIntResult<STATE, ACTION, LOC> threadResult =
						mFixpointEngine.runWithInterferences(Set.of(entry.getValue()), script, interferences);

				// Merge mStateStorage and result.getLoc2States
				for (final var locAndStates : threadResult.getLoc2States().entrySet()) {
					mStateStorage.addAbstractState(locAndStates.getKey(),
							DisjunctiveAbstractState.createDisjunction(locAndStates.getValue()));
				}
				// Add present counterexamples
				for (final var counterExample : threadResult.getCounterexamples()) {
					final var execution = counterExample.getAbstractExecution();
					final var errorLocation = execution.get(execution.size() - 1).getSecond();
					if (!addedErrorLocations.add(errorLocation)) {
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
			interferences = newInterferences;
			iteration++;
		}
	}

	private Map<LOC, DisjunctiveAbstractState<STATE>>
			computeNewInterferences(final Map<ACTION, DisjunctiveAbstractState<STATE>> relevantPostStates) {
		final Map<LOC, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
		for (final Entry<String, LOC> entry : mEntryLocs.entrySet()) {
			final DisjunctiveAbstractState<STATE> interferingState =
					getInterferingState(entry.getKey(), relevantPostStates);
			if (interferingState != null) {
				new IcfgLocationIterator<>(entry.getValue()).forEachRemaining(x -> result.put(x, interferingState));
			}
		}
		return result;
	}

	private DisjunctiveAbstractState<STATE> getInterferingState(final String procedure,
			final Map<ACTION, DisjunctiveAbstractState<STATE>> relevantPostStates) {
		final Iterator<DisjunctiveAbstractState<STATE>> postStatesOfOtherThreads = relevantPostStates.keySet().stream()
				.filter(x -> !x.getPrecedingProcedure().equals(procedure)).map(relevantPostStates::get).iterator();
		if (!postStatesOfOtherThreads.hasNext()) {
			return null;
		}
		DisjunctiveAbstractState<STATE> state = postStatesOfOtherThreads.next();
		while (postStatesOfOtherThreads.hasNext()) {
			state = state.union(postStatesOfOtherThreads.next());
		}
		return state;
	}

	private Map<ACTION, DisjunctiveAbstractState<STATE>>
			getRelevantPostStates(final HashRelation<ACTION, IProgramVar> sharedWritesToVars) {
		final Map<ACTION, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
		final Map<LOC, Set<DisjunctiveAbstractState<STATE>>> loc2States = mStateStorage.computeLoc2States();
		for (final Entry<ACTION, HashSet<IProgramVar>> entry : sharedWritesToVars.entrySet()) {
			// TODO: Previously we applied the post-operator to the pre-state, why?
			final ACTION write = entry.getKey();
			final DisjunctiveAbstractState<STATE> stateAfterWrite =
					flattenAbstractStates(loc2States.get(mTransitionProvider.getTarget(write)));
			// TODO: The new HashSet<> is just needed for type conversion, is there a better way?
			final Set<IProgramVarOrConst> varsToRemove =
					DataStructureUtils.difference(stateAfterWrite.getVariables(), new HashSet<>(entry.getValue()));
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
