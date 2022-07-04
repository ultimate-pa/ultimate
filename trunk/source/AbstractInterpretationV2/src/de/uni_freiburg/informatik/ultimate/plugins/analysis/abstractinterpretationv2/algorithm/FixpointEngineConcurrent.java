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
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
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

	private final int mMaxIterations;
	private final FixpointEngineConcurrentUtils<STATE, ACTION, LOC> mFecUtils;

	private final Map<LOC, DisjunctiveAbstractState<STATE>> mErrors;

	public FixpointEngineConcurrent(final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> params,
			final IIcfg<?> icfg, final FixpointEngine<STATE, ACTION, VARDECL, LOC> fxpe) {
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

		mMaxIterations = 3;

		mFecUtils = new FixpointEngineConcurrentUtils<>(mIcfg, mTransitionProvider);

		mErrors = new HashMap<>();
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
			final Script script, final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences) {
		throw new UnsupportedOperationException("Operation not supported for FixpointEngineConcurrent");
	}

	private void calculateFixpoint(final Map<String, ? extends IcfgLocation> entryNodes, final Script script) {
		Map<ACTION, DisjunctiveAbstractState<STATE>> interferences = new HashMap<>();
		int iteration = 0;
		while (true) {
			final Map<ACTION, DisjunctiveAbstractState<STATE>> tempInterferences =
					FixpointEngineConcurrentUtils.copyMap(interferences);
			for (final Map.Entry<String, ? extends IcfgLocation> entry : entryNodes.entrySet()) {
				// TODO: Change such that procedureInterferences returns Set<Map<...>>
				final Set<Map<ACTION, DisjunctiveAbstractState<STATE>>> interferencesMaps =
						computeProcedureInterferences(entry.getValue(), interferences);

				for (final var procedureInterferences : interferencesMaps) {
					// runWithInterferences needs a Collection
					final Collection<LOC> entryCollection = new ArrayList<>();
					entryCollection.add((LOC) entry.getValue());
					final AbsIntResult<STATE, ACTION, LOC> result =
							mFixpointEngine.runWithInterferences(entryCollection, script, procedureInterferences);

					// merge mStateStorage and result.getLoc2States
					for (final var locAndStates : result.getLoc2States().entrySet()) {
						final DisjunctiveAbstractState<STATE> state =
								DisjunctiveAbstractState.createDisjunction(locAndStates.getValue());
						mStateStorage.addAbstractState(locAndStates.getKey(), state);
					}

					tempInterferences.putAll(computeNewInterferences(entry.getKey(), tempInterferences,
							procedureInterferences, iteration));
				}

				iteration++;

			}
			// Check if Fixpoint is reached
			if (interferences.equals(tempInterferences)) {
				break;
			}
			interferences = tempInterferences;
		}
		final var loc2States = mStateStorage.computeLoc2States();
		// add Errors (just for convenience -> not final solution for showing results of analysis)
		for (final Entry<LOC, Set<DisjunctiveAbstractState<STATE>>> entry : loc2States.entrySet()) {
			if (mTransitionProvider.isErrorLocation(entry.getKey())) {
				mErrors.put(entry.getKey(), flattenAbstractStates(entry.getValue()));
			}
		}
		// areAbStractStatesSound(loc2States);
	}

	private boolean areAbStractStatesSound(final Map<LOC, Set<DisjunctiveAbstractState<STATE>>> loc2States) {
		for (final Entry<LOC, Set<DisjunctiveAbstractState<STATE>>> entry : loc2States.entrySet()) {
			final Collection<ACTION> actions = mTransitionProvider.getSuccessorActions(entry.getKey());
			for (final ACTION action : actions) {
				final IAbstractPostOperator<STATE, ACTION> postOp = mDomain.getPostOperator();
				final DisjunctiveAbstractState<STATE> postState =
						flattenAbstractStates(entry.getValue()).apply(postOp, action);
				final var states = loc2States.get(mTransitionProvider.getTarget(action));
				final DisjunctiveAbstractState<STATE> temp = flattenAbstractStates(states);
				if (states != null && temp.isSubsetOf(postState) == SubsetResult.NONE) {
					return false;
				}
			}
		}
		return true;
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
			final Set<Map<ACTION, DisjunctiveAbstractState<STATE>>> result = new HashSet<>();
			result.add(new HashMap<>());
			return result;
		}
		return versionOne(mFecUtils.filterProcedures(entryNode.getProcedure(), interferences),
				entryNode.getProcedure());
	}

	/**
	 * Version 1: Union over all procedures
	 *
	 * @param entryNode
	 * @param interferences
	 * @return
	 */
	private Set<Map<ACTION, DisjunctiveAbstractState<STATE>>> versionOne(
			final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences, final String currentProcedure) {
		final Set<Map<ACTION, DisjunctiveAbstractState<STATE>>> result = new HashSet<>();
		final Map<LOC, Set<DisjunctiveAbstractState<STATE>>> loc2States = mStateStorage.computeLoc2States();
		final Set<ACTION> reads = mFecUtils.getReads(currentProcedure);
		if (reads == null) {
			result.add(new HashMap<>());
			return result;
		}
		final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterference = new HashMap<>();
		for (final ACTION read : reads) {
			for (final Map.Entry<ACTION, DisjunctiveAbstractState<STATE>> interference : interferences.entrySet()) {
				final Set<IProgramVarOrConst> variables = interference.getValue().getVariables();
				if (canReadFrom(read, interference.getKey())
						&& DataStructureUtils.haveNonEmptyIntersection(variables, mFecUtils.getReadVars(read))) {
					final DisjunctiveAbstractState<STATE> currentInterferences = procedureInterference.get(read);
					if (currentInterferences != null) {
						// TODO: Test if patch ist hier notwendig
						// -> sollten immer dieselben Variablen beinhalten
						final DisjunctiveAbstractState<STATE> tempState =
								currentInterferences.patch(interference.getValue());
						procedureInterference.put(read, unionIfNonEmpty(currentInterferences, interference.getValue()));
					} else {
						DisjunctiveAbstractState<STATE> tempState =
								flattenAbstractStates(loc2States.get(mTransitionProvider.getSource(read)));
						tempState = removeNonSharedVariables(tempState, variables);
						procedureInterference.put(read, unionIfNonEmpty(tempState, interference.getValue()));
					}
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
	private Map<ACTION, DisjunctiveAbstractState<STATE>> versionTwo(final IcfgLocation entryNode,
			final Map<LOC, DisjunctiveAbstractState<STATE>> interferences) {
		// get crossproduct from mFecUtils
		// if not computed already, compute it now -> mFecUtils.computeCrossProduct(Predicate)
		// Then go through every entry and match every read with the to the write corresponding state in interferences

		final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterferences = new HashMap<>();
		return procedureInterferences;
	}

	/**
	 * Version 3: filter procedures + special cross product + feasibility check
	 *
	 * @param entryNode
	 * @param interferences
	 * @return
	 */
	private Map<ACTION, DisjunctiveAbstractState<STATE>> versionThree(final IcfgLocation entryNode,
			final Map<LOC, DisjunctiveAbstractState<STATE>> interferences) {
		final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterferences = new HashMap<>();
		return procedureInterferences;
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
			if (states != null) {
				preState = flattenAbstractStates(states);
			} else {
				preState = new DisjunctiveAbstractState<>(mDomain.createTopState());
				for (final IProgramVarOrConst variable : mFecUtils.getVarsForBuildingState(write)) {
					preState = preState.addVariable(variable);
				}
			}
			final DisjunctiveAbstractState<STATE> interference = procedureInterferences.get(write);
			if (interference != null) {
				preState.union(interference);
			}
			final IAbstractPostOperator<STATE, ACTION> postOp = mDomain.getPostOperator();
			DisjunctiveAbstractState<STATE> postState = preState.apply(postOp, write);
			if (iteration > mMaxIterations && interferences.containsKey(write)) {
				final IAbstractStateBinaryOperator<STATE> wideningOp = mDomain.getWideningOperator();
				postState = interferences.get(write).widen(wideningOp, postState);
			}
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
			return new DisjunctiveAbstractState<>();
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

	private boolean canReadFrom(final ACTION read, final ACTION write) {
		// same procedure or prcedures running parallel
		return mTransitionProvider.getProcedureName(read).equals(mTransitionProvider.getProcedureName(write))
				|| mFecUtils.canReadFromInterference(read, write);
	}
}
