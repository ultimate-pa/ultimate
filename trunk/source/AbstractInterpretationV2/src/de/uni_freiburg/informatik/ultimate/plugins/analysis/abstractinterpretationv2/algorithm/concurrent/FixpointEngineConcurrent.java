package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbsIntResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IFixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.SummaryMap;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.WriteExtractor;
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
	private final List<String> mTopologicalOrder;
	private final HashRelation<String, LOC> mInverseForkRelation;

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
		mTopologicalOrder = InterferenceUtils.getTopologicalProcedureOrder(icfg);
		mInverseForkRelation = constructInverseForkRelation(icfg);
	}

	private HashRelation<String, LOC> constructInverseForkRelation(final IIcfg<LOC> icfg) {
		final HashRelation<String, LOC> result = new HashRelation<>();
		icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap()
				.forEach((x, y) -> result.addPair(x.getNameOfForkedProcedure(), (LOC) x.getSource()));
		return result;
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
			for (final String procedure : mTopologicalOrder) {
				// TODO: Should we just use run, but with a modified IAbstractPostOperator
				// (that wraps the other one and considers interferences?)
				// Similarly we could have a new IVariableProvider-wrapper that adds a more precise initial state
				// (after the fork)
				final DisjunctiveAbstractState<STATE> initialState = getInitialState(procedure);
				final AbsIntResult<STATE, ACTION, LOC> threadResult = mFixpointEngine
						.runWithInterferences(Set.of(mEntryLocs.get(procedure)), script, interferences, initialState);

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

	private DisjunctiveAbstractState<STATE> getInitialState(final String procedure) {
		final Iterator<LOC> locs = mInverseForkRelation.getImage(procedure).iterator();
		if (!locs.hasNext()) {
			return new DisjunctiveAbstractState<>(mMaxParallelStates, mDomain.createTopState());
		}
		DisjunctiveAbstractState<STATE> state = mStateStorage.getAbstractState(locs.next());
		while (locs.hasNext()) {
			state = state.union(mStateStorage.getAbstractState(locs.next()));
		}
		return state;
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
		// TODO: Considering only the other procedures is unsound for unbounded threads!
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
		for (final Entry<ACTION, HashSet<IProgramVar>> entry : sharedWritesToVars.entrySet()) {
			// TODO: Previously we applied the post-operator to the pre-state, why?
			final ACTION write = entry.getKey();
			final DisjunctiveAbstractState<STATE> stateAfterWrite =
					mStateStorage.getAbstractState(mTransitionProvider.getTarget(write));
			// TODO: The new HashSet<> is just needed for type conversion, is there a better way?
			final Set<IProgramVarOrConst> varsToRemove =
					DataStructureUtils.difference(stateAfterWrite.getVariables(), new HashSet<>(entry.getValue()));
			result.put(write, stateAfterWrite.removeVariables(varsToRemove));
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

	@Override
	public AbsIntResult<STATE, ACTION, LOC> runWithInterferences(final Collection<? extends LOC> start,
			final Script script, final Map<LOC, DisjunctiveAbstractState<STATE>> interferences,
			final DisjunctiveAbstractState<STATE> initialState) {
		throw new UnsupportedOperationException(
				getClass().getSimpleName() + " cannot be used inside concurrent abstract interpretation.");
	}
}
