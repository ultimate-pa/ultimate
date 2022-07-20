/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer.AbstractInterpretationConcurrent;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 * @author Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 *
 */

public class FixpointEngineConcurrent<STATE extends IAbstractState<STATE>, ACTION, VARDECL, LOC>
		implements IFixpointEngine<STATE, ACTION, VARDECL, LOC> {

	private final int mMaxUnwindings;
	private final int mMaxParallelStates;

	private final ITransitionProvider<ACTION, LOC> mTransitionProvider;
	private final IAbstractStateStorage<STATE, ACTION, LOC> mStateStorage;
	private final IAbstractDomain<STATE, ACTION> mDomain;
	private final IVariableProvider<STATE, ACTION> mVarProvider;
	private final ILoopDetector<ACTION> mLoopDetector;
	private final IDebugHelper<STATE, ACTION, VARDECL, LOC> mDebugHelper;
	private final IProgressAwareTimer mTimer;
	private final ILogger mLogger;

	private AbsIntResult<STATE, ACTION, LOC> mResult;
	private final SummaryMap<STATE, ACTION, LOC> mSummaryMap;
	private final boolean mUseHierachicalPre;

	private final IIcfg<?> mIcfg;
	private final FixpointEngine<STATE, ACTION, VARDECL, LOC> mFixpointEngine;

	private final int mIterationsBeforeWidening;
	private final FixpointEngineConcurrentUtils<STATE, ACTION, LOC> mFecUtils;

	private final Map<LOC, DisjunctiveAbstractState<STATE>> mErrors;

	private final AbstractInterpretationConcurrent mVersion;

	public FixpointEngineConcurrent(final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> params,
			final IIcfg<?> icfg, final FixpointEngine<STATE, ACTION, VARDECL, LOC> fxpe,
			final AbstractInterpretationConcurrent version, final int iterations) {
		if (params == null || !params.isValid()) {
			throw new IllegalArgumentException("invalid params");
		}
		mTimer = params.getTimer();
		mLogger = params.getLogger();
		mTransitionProvider = params.getTransitionProvider();
		mStateStorage = params.getStorage();
		mDomain = params.getAbstractDomain();
		mVarProvider = params.getVariableProvider();
		mLoopDetector = params.getLoopDetector();
		mDebugHelper = params.getDebugHelper();
		mMaxUnwindings = params.getMaxUnwindings();
		mMaxParallelStates = params.getMaxParallelStates();
		mSummaryMap = new SummaryMap<>(mTransitionProvider, mLogger);
		mUseHierachicalPre = mDomain.useHierachicalPre();
		mIcfg = icfg;
		mFixpointEngine = fxpe;

		mIterationsBeforeWidening = iterations;

		mFecUtils = new FixpointEngineConcurrentUtils<>(mIcfg, mTransitionProvider);

		mErrors = new HashMap<>();

		mVersion = version;
	}

	@Override
	public AbsIntResult<STATE, ACTION, LOC> run(final Collection<? extends LOC> initialNodes, final Script script) {
		mLogger.info("Starting fixpoint engine with domain " + mDomain.getClass().getSimpleName() + " (maxUnwinding="
				+ mMaxUnwindings + ", maxParallelStates=" + mMaxParallelStates + ")");
		mResult = new AbsIntResult<>(script, mDomain, mTransitionProvider, mVarProvider);
		mDomain.beforeFixpointComputation(mResult.getBenchmark());
		calculateFixpoint(mIcfg.getProcedureEntryNodes(), script);
		mResult.saveRootStorage(mStateStorage);
		mResult.saveSummaryStorage(mSummaryMap);
		mLogger.debug("Fixpoint computation completed");
		mDomain.afterFixpointComputation(mResult);
		return mResult;
	}

	@Override
	public AbsIntResult<STATE, ACTION, LOC> runWithInterferences(final Collection<? extends LOC> initialNodes,
			final Script script, final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences,
			final Set<ACTION> readsProcedureintern) {
		throw new UnsupportedOperationException("Operation not supported for FixpointEngineConcurrent");
	}

	private void calculateFixpoint(final Map<String, ? extends IcfgLocation> entryNodes, final Script script) {
		Map<ACTION, DisjunctiveAbstractState<STATE>> interferences = new HashMap<>();
		int iteration = 0;
		final List<String> analysingOrder = mFecUtils.computeTopologicalOrder(entryNodes.keySet());
		final Set<LOC> addedErrorLocations = new HashSet<>();
		// get Set of Reads which should also read thread-intern
		final Map<String, Set<ACTION>> readsProcedureIntern = getReadsReadingProcedureIntern(entryNodes);
		while (true) {
			final Map<ACTION, DisjunctiveAbstractState<STATE>> tempInterferences =
					FixpointEngineConcurrentUtils.copyMap(interferences);
			for (final String procedure : analysingOrder) {
				final Set<Map<ACTION, DisjunctiveAbstractState<STATE>>> interferencesMaps =
						computeProcedureInterferences(entryNodes.get(procedure), interferences);

				for (final var procedureInterferences : interferencesMaps) {
					// runWithInterferences needs a Collection
					final Collection<LOC> entryCollection = new ArrayList<>();
					entryCollection.add((LOC) entryNodes.get(procedure));
					final AbsIntResult<STATE, ACTION, LOC> result = mFixpointEngine.runWithInterferences(
							entryCollection, script, procedureInterferences, readsProcedureIntern.get(procedure));

					// merge mStateStorage and result.getLoc2States
					for (final var locAndStates : result.getLoc2States().entrySet()) {
						final DisjunctiveAbstractState<STATE> state =
								DisjunctiveAbstractState.createDisjunction(locAndStates.getValue());
						mStateStorage.addAbstractState(locAndStates.getKey(), state);
					}

					tempInterferences.putAll(
							computeNewInterferences(procedure, tempInterferences, procedureInterferences, iteration));

					for (final var counterExample : result.getCounterexamples()) {
						final var execution = counterExample.getAbstractExecution();
						final var errorLocation = execution.get(execution.size() - 1).getSecond();
						if (!addedErrorLocations.contains(errorLocation)) {
							addedErrorLocations.add(errorLocation);
							mResult.addCounterexample(counterExample);
						}
					}
				}
			}

			iteration++;

			// Check if Fixpoint is reached
			if (interferences.equals(tempInterferences)) {
				break;
			}
			interferences = tempInterferences;
		}

		areAbStractStatesSound(mStateStorage.computeLoc2States());
	}

	private boolean areAbStractStatesSound(final Map<LOC, Set<DisjunctiveAbstractState<STATE>>> loc2States) {
		boolean result = true;
		for (final Entry<LOC, Set<DisjunctiveAbstractState<STATE>>> entry : loc2States.entrySet()) {
			final Collection<ACTION> actions = mTransitionProvider.getSuccessorActions(entry.getKey());
			final var preState = flattenAbstractStates(entry.getValue());
			if (preState == null) {
				continue;
			}
			for (final ACTION action : actions) {
				final IAbstractPostOperator<STATE, ACTION> postOp = mDomain.getPostOperator();
				final DisjunctiveAbstractState<STATE> postState = preState.apply(postOp, action);
				final var loc2StatesAfterAction = loc2States.get(mTransitionProvider.getTarget(action));
				final DisjunctiveAbstractState<STATE> stateAfterAction = flattenAbstractStates(loc2StatesAfterAction);
				if (stateAfterAction != null && postState != null
						&& postState.isSubsetOf(stateAfterAction) == SubsetResult.NONE) {
					result = false;
				}
			}
		}
		return result;
	}

	/**
	 *
	 * @param entryNode
	 *            The entry node in the Icfg of the procedure for which the interferences should be computed
	 * @param interferences
	 * @return A Map that sorts every read of a shared variable in this procedure to a {@link DisjunctiveAbstractState}
	 *         that contains only the shared variables that are read.
	 */
	private Set<Map<ACTION, DisjunctiveAbstractState<STATE>>> computeProcedureInterferences(
			final IcfgLocation entryNode, final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences) {
		if (interferences.isEmpty()) {
			final Set<Map<ACTION, DisjunctiveAbstractState<STATE>>> procedureInterferences = new HashSet<>();
			final Map<ACTION, DisjunctiveAbstractState<STATE>> map = new HashMap<>();
			if (!mStateStorage.computeLoc2States().isEmpty()) {
				map.putAll(handlingForks(entryNode.getProcedure(),
						mTransitionProvider.getSuccessorActions((LOC) entryNode)));
			}
			procedureInterferences.add(map);
			return procedureInterferences;
		}

		if (mVersion == AbstractInterpretationConcurrent.FLOW_INSENSITIV) {
			return unionOverInterferences(interferences, entryNode);
		}

		if (mVersion == AbstractInterpretationConcurrent.FLOW_SENSITIV) {
			return filteredCrossProduct(entryNode, interferences, x -> true);
		}

		if (mVersion == AbstractInterpretationConcurrent.FLOW_SENSITIV_PLUS_CONSTRAINTS) {
			throw new UnsupportedOperationException("Filter is not implemented yet");
		}

		throw new UnsupportedOperationException("Unvalid Version option selected");
	}

	/**
	 * Version 1: Union over all procedures
	 *
	 * @param entryNode
	 * @param interferences
	 * @return
	 */
	private Set<Map<ACTION, DisjunctiveAbstractState<STATE>>> unionOverInterferences(
			final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences, final IcfgLocation entryNode) {
		final Set<Map<ACTION, DisjunctiveAbstractState<STATE>>> result = new HashSet<>();
		final Map<LOC, Set<DisjunctiveAbstractState<STATE>>> loc2States = mStateStorage.computeLoc2States();
		final String currentProcedure = entryNode.getProcedure();
		final Set<ACTION> reads = mFecUtils.getReads(currentProcedure);
		final Map<ACTION, DisjunctiveAbstractState<STATE>> statesForForks =
				handlingForks(currentProcedure, mTransitionProvider.getSuccessorActions((LOC) entryNode));
		if (reads == null) {
			result.add(statesForForks);
			return result;
		}
		final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterference = new HashMap<>();
		procedureInterference.putAll(statesForForks);
		for (final ACTION read : reads) {
			DisjunctiveAbstractState<STATE> newInterferences = null;
			for (final ACTION write : mFecUtils.getPossibleWrites(read)) {
				final DisjunctiveAbstractState<STATE> interference = interferences.get(write);
				if (interference != null) {
					if (newInterferences != null) {
						newInterferences = mergeStates(newInterferences, interference);
						continue;
					}
					newInterferences = interference;
				}
			}

			if (newInterferences != null) {
				newInterferences = removeNonSharedVariables(newInterferences, mFecUtils.getReadVars(read));
				final DisjunctiveAbstractState<STATE> oldInterferences = procedureInterference.get(read);
				if (oldInterferences != null) {
					procedureInterference.put(read, mergeStates(oldInterferences, newInterferences));
				} else {
					procedureInterference.put(read, newInterferences);
				}
			}
		}
		result.add(procedureInterference);
		return result;
	}

	/**
	 * Version 2: filter procedures + special cross product
	 *
	 * @param entryNode
	 * @param interferences
	 * @return
	 */
	private Set<Map<ACTION, DisjunctiveAbstractState<STATE>>> filteredCrossProduct(final IcfgLocation entryNode,
			final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences,
			final Predicate<Map<LOC, Set<ACTION>>> combinationIsFeasable) {
		final Set<Map<ACTION, DisjunctiveAbstractState<STATE>>> procedureInterferences = new HashSet<>();
		final String procedure = entryNode.getProcedure();
		// change to Set<ACTION>
		final Set<Map<LOC, Set<ACTION>>> crossProduct = mFecUtils.getCrossProduct(combinationIsFeasable, procedure);
		final Map<ACTION, DisjunctiveAbstractState<STATE>> readsInLoopsAndForks = new HashMap<>();
		readsInLoopsAndForks.putAll(handlingLoops(procedure, interferences));
		readsInLoopsAndForks.putAll(handlingForks(procedure, mTransitionProvider.getSuccessorActions((LOC) entryNode)));

		final Set<ACTION> reads = mFecUtils.getReads(procedure);
		for (final var map : crossProduct) {
			final Map<ACTION, DisjunctiveAbstractState<STATE>> combination = new HashMap<>();
			combination.putAll(readsInLoopsAndForks);
			for (final var entry : map.entrySet()) {
				for (final var write : entry.getValue()) {
					if (write == null) {
						// read should read procedure intern, should be unnecessary
						continue;
					}

					for (final ACTION read : mTransitionProvider.getSuccessorActions(entry.getKey())) {
						if (!reads.contains(read)) {
							continue;
						}
						DisjunctiveAbstractState<STATE> state = interferences.get(write);
						if (state == null) {
							state = new DisjunctiveAbstractState<>(mDomain.createTopState());
							for (final IProgramVarOrConst variable : mFecUtils.getReadVars(read)) {
								state = state.addVariable(variable);
							}
						}
						final DisjunctiveAbstractState<STATE> currentState = combination.get(read);
						if (currentState != null) {
							combination.put(read, mergeStates(currentState, state));
						} else {
							combination.put(read, state);
						}
					}
				}
			}
			if (!combination.isEmpty()) {
				procedureInterferences.add(combination);
			}
		}

		return procedureInterferences;
	}

	private Map<ACTION, DisjunctiveAbstractState<STATE>> handlingLoops(final String procedure,
			final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences) {
		final Map<ACTION, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
		for (final ACTION read : mFecUtils.getSelfReachableReads(procedure)) {
			DisjunctiveAbstractState<STATE> state = null;
			for (final ACTION write : mFecUtils.getPossibleWrites(read)) {
				final var interference = interferences.get(write);
				if (interference == null) {
					continue;
				}
				if (state != null) {
					state = mergeStates(state, interference);
					continue;
				}
				state = interference;
			}
			if (state != null) {
				result.put(read, state);
			}
		}
		return result;
	}

	private Map<ACTION, DisjunctiveAbstractState<STATE>> handlingForks(final String procedure,
			final Collection<ACTION> initialActions) {
		final Map<LOC, Set<DisjunctiveAbstractState<STATE>>> loc2States = mStateStorage.computeLoc2States();
		final Map<ACTION, DisjunctiveAbstractState<STATE>> result = new HashMap<>();

		final Set<IProgramVarOrConst> globalVariables = mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable()
				.getModifiedBoogieVars(procedure).stream().collect(Collectors.toSet());
		DisjunctiveAbstractState<STATE> state = null;
		for (final LOC forkLocation : mFecUtils.forkedAt(procedure)) {
			DisjunctiveAbstractState<STATE> forkedState = flattenAbstractStates(loc2States.get(forkLocation));
			if (forkedState == null) {
				continue;
			}
			forkedState = forkedState
					.removeVariables(DataStructureUtils.difference(forkedState.getVariables(), globalVariables));
			if (state != null) {
				state = mergeStates(state, forkedState);
				continue;
			}
			state = forkedState;
		}
		if (state != null) {
			for (final ACTION action : initialActions) {
				result.put(action, state);
			}
		}

		return result;
	}

	private Map<ACTION, DisjunctiveAbstractState<STATE>> computeNewInterferences(final String procedure,
			final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences,
			final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterferences, final int iteration) {
		Map<ACTION, DisjunctiveAbstractState<STATE>> result = FixpointEngineConcurrentUtils.copyMap(interferences);
		final Set<ACTION> actions = mFecUtils.getWrites(procedure);
		if (actions == null) {
			return result;
		}
		final Map<LOC, Set<DisjunctiveAbstractState<STATE>>> loc2States = mStateStorage.computeLoc2States();
		for (final ACTION write : actions) {
			final LOC loc = mTransitionProvider.getSource(write);
			final Set<DisjunctiveAbstractState<STATE>> states = loc2States.get(loc);
			DisjunctiveAbstractState<STATE> preState;
			if (states == null && !mIcfg.getProcedureEntryNodes().get(procedure).equals(loc)) {
				// location is not in loc2States but not EntryNode
				final DisjunctiveAbstractState<STATE> bottomState =
						new DisjunctiveAbstractState<>(mDomain.createBottomState());
				// for (final IProgramVarOrConst variable : mFecUtils.getWrittenVars(write)) {
				// bottomState = bottomState.addVariable(variable);
				// }
				result = combineInterferences(result, write, bottomState);
				continue;
			}
			if (states == null && !procedureInterferences.containsKey(write)) {
				preState = new DisjunctiveAbstractState<>(mDomain.createTopState());
				preState = preState.addVariables(mFecUtils.getVarsForBuildingState(write));
			} else {
				preState = flattenAbstractStates(states);
			}

			final DisjunctiveAbstractState<STATE> interference = procedureInterferences.get(write);
			if (interference != null) {
				if (preState != null) {
					preState = mergeStates(preState, interference);
				} else {
					preState = interference;
					preState = preState.addVariables(DataStructureUtils
							.difference(mFecUtils.getVarsForBuildingState(write), interference.getVariables()));
				}
			}
			final IAbstractPostOperator<STATE, ACTION> postOp = mDomain.getPostOperator();
			DisjunctiveAbstractState<STATE> postState = preState.apply(postOp, write);
			if (iteration > mIterationsBeforeWidening && interferences.containsKey(write)) {
				final IAbstractStateBinaryOperator<STATE> wideningOp = mDomain.getWideningOperator();
				postState = interferences.get(write).widen(wideningOp, postState);
			}
			// TODO: relational Domain -> will remove relations between variables
			// TODO: should Variables really be removed
			postState = removeNonSharedVariables(postState, mFecUtils.getWrittenVars(write));
			result = combineInterferences(result, write, postState);
		}
		return result;
	}

	private Map<ACTION, DisjunctiveAbstractState<STATE>> combineInterferences(
			final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences, final ACTION key,
			final DisjunctiveAbstractState<STATE> postState) {
		if (interferences.containsKey(key)) {
			final DisjunctiveAbstractState<STATE> oldInterferences = interferences.get(key);
			interferences.put(key, unionIfNonEmpty(oldInterferences, postState));
		} else {
			interferences.put(key, postState);
		}
		return interferences;
	}

	private DisjunctiveAbstractState<STATE>
			flattenAbstractStates(final Set<DisjunctiveAbstractState<STATE>> setOfStates) {
		if (setOfStates == null || setOfStates.isEmpty()) {
			return null;
		}

		final Iterator<DisjunctiveAbstractState<STATE>> iterator = setOfStates.iterator();
		DisjunctiveAbstractState<STATE> result = iterator.next();
		while (iterator.hasNext()) {
			result = unionIfNonEmpty(result, iterator.next());
		}
		return result;
	}

	/**
	 *
	 * @param state
	 * @param variables
	 * @return copy of state without the variables that are <b>not</b> in variables
	 */
	private DisjunctiveAbstractState<STATE> removeNonSharedVariables(final DisjunctiveAbstractState<STATE> state,
			final Set<IProgramVarOrConst> variables) {
		// filter variables out
		final Set<IProgramVarOrConst> variablesCasted = variables.stream().collect(Collectors.toSet());
		DisjunctiveAbstractState<STATE> tempState = state;
		final Set<IProgramVarOrConst> variablesToRemove =
				DataStructureUtils.difference(state.getVariables(), variablesCasted);
		for (final IProgramVarOrConst variable : variablesToRemove) {
			if (tempState.containsVariable(variable)) {
				tempState = tempState.removeVariable(variable);
			}
		}
		return tempState;
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

	private Map<String, Set<ACTION>>
			getReadsReadingProcedureIntern(final Map<String, ? extends IcfgLocation> entryNodes) {
		if (mVersion == AbstractInterpretationConcurrent.FLOW_INSENSITIV) {
			// all reads except if they are entryActions
			final Map<String, Set<ACTION>> result = new HashMap<>();
			for (final var entry : entryNodes.entrySet()) {
				final String procedure = entry.getKey();
				final var reads = mFecUtils.getReads(procedure);
				if (reads != null) {
					final Set<ACTION> entryActions = mTransitionProvider.getSuccessorActions((LOC) entry.getValue())
							.stream().collect(Collectors.toSet());
					result.put(procedure, DataStructureUtils.difference(reads, entryActions));
				} else {
					result.put(procedure, Set.of());
				}
			}
			return result;
		}

		if (mVersion == AbstractInterpretationConcurrent.FLOW_SENSITIV
				|| mVersion == AbstractInterpretationConcurrent.FLOW_SENSITIV_PLUS_CONSTRAINTS) {
			final Map<String, Set<ACTION>> result = new HashMap<>();
			for (final var procedure : entryNodes.keySet()) {
				final var reads = mFecUtils.getSelfReachableReads(procedure);
				if (reads != null) {
					result.put(procedure, reads);
				} else {
					result.put(procedure, Set.of());
				}
			}
			return result;
		}

		throw new UnsupportedOperationException("Unvalid Version option selected");
	}

	private DisjunctiveAbstractState<STATE> mergeStates(final DisjunctiveAbstractState<STATE> oldState,
			final DisjunctiveAbstractState<STATE> newState) {
		return oldState.patch(newState).union(oldState);
	}
}
