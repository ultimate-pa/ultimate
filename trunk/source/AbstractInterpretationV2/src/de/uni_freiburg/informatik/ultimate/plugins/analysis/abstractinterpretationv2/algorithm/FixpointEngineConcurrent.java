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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
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
			for (final Map.Entry<String, ? extends IcfgLocation> entry : entryNodes.entrySet()) {
				final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterferences =
						computeProcedureInterferences(entry.getValue(), interferences);

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
			}
			// Check if Fixpoint is reached
			iteration++;
			final Map<ACTION, DisjunctiveAbstractState<STATE>> tempInterferences =
					computeNewInterferences(interferences, iteration);
			if (interferences.equals(tempInterferences)) {
				break;
			}
			interferences = tempInterferences;
		}
	}

	private void checkReachedError(final WorklistItem<STATE, ACTION, VARDECL, LOC> currentItem,
			final DisjunctiveAbstractState<STATE> postState, final Set<ACTION> reachedErrors) {
		final ACTION currentAction = currentItem.getAction();
		final LOC postLoc = mTransitionProvider.getTarget(currentAction);
		if (!mTransitionProvider.isErrorLocation(postLoc) || postState.isBottom()
				|| !reachedErrors.add(currentAction)) {
			// no new error reached
			return;
		}
		// TODO: Find a way to add reached Errors
		// mResult.reachedError(mTransitionProvider, currentItem, postState);
	}

	/**
	 *
	 * @param entryNode
	 *            The entry node in the Icfg of the procedure for which the interferences should be computed
	 * @param interferences
	 * @return A Map that sorts every read of a shared variable in this procedure to a {@link DisjunctiveAbstractState}
	 *         that contains only the shared variables that are read.
	 */
	private Map<ACTION, DisjunctiveAbstractState<STATE>> computeProcedureInterferences(final IcfgLocation entryNode,
			final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences) {
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
	private Map<ACTION, DisjunctiveAbstractState<STATE>> versionOne(
			final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences, final String currentProcedure) {
		Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterference = new HashMap<>();
		for (final Map.Entry<ACTION, Set<IProgramVar>> read : mFecUtils.getSharedReadIterable()) {
			if (!mTransitionProvider.getProcedureName(read.getKey()).equals(currentProcedure)) {
				continue;
			}
			for (final Map.Entry<ACTION, DisjunctiveAbstractState<STATE>> interference : interferences.entrySet()) {
				if (canReadFrom(read.getKey(), interference.getKey())) {
					final Set<IProgramVar> variables = mFecUtils.getWrittenVars(interference.getKey());
					if (DataStructureUtils.haveNonEmptyIntersection(variables, read.getValue())) {
						procedureInterference =
								addInterference(procedureInterference, interference.getValue(), read.getKey());
					}
				}
			}
		}
		return procedureInterference;
	}

	private Map<ACTION, DisjunctiveAbstractState<STATE>> addInterference(
			final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterference,
			final DisjunctiveAbstractState<STATE> interference, final ACTION action) {
		for (final ACTION key : mFecUtils.getActionsToPatchInto(action)) {
			if (procedureInterference.containsKey(key)) {
				DisjunctiveAbstractState<STATE> currentState = procedureInterference.get(key);
				final Set<IProgramVarOrConst> sharedVars =
						DataStructureUtils.intersection(interference.getVariables(), currentState.getVariables());
				currentState = currentState.patch(interference.removeVariables(sharedVars));
				final DisjunctiveAbstractState<STATE> tempState = currentState.patch(interference);
				procedureInterference.put(key, unionIfNonEmpty(currentState, tempState));
			} else {
				procedureInterference.put(key, interference);
			}
		}
		return procedureInterference;
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

	private Map<ACTION, DisjunctiveAbstractState<STATE>> computeNewInterferences(
			final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences, final int iteration) {
		Map<ACTION, DisjunctiveAbstractState<STATE>> result = FixpointEngineConcurrentUtils.copyMap(interferences);
		final Map<LOC, Set<DisjunctiveAbstractState<STATE>>> loc2States = mStateStorage.computeLoc2States();
		for (final Entry<ACTION, Set<IProgramVar>> entry : mFecUtils.getSharedWriteIterable()) {
			final LOC loc = mTransitionProvider.getSource(entry.getKey());
			DisjunctiveAbstractState<STATE> preState;
			if (loc2States.containsKey(loc)) {
				preState = flattenAbstractState(loc2States.get(loc));
			} else {
				preState = new DisjunctiveAbstractState<>(mDomain.createTopState());
				// TODO: maybe I have to add all variable from the procedure
				for (final IProgramVar variable : entry.getValue()) {
					preState = preState.addVariable(variable);
				}
			}
			final IAbstractPostOperator<STATE, ACTION> postOp = mDomain.getPostOperator();
			DisjunctiveAbstractState<STATE> postState = preState.apply(postOp, entry.getKey());
			if (iteration > mMaxIterations && interferences.containsKey(entry.getKey())) {
				final IAbstractStateBinaryOperator<STATE> wideningOp = mDomain.getWideningOperator();
				postState = interferences.get(entry.getKey()).widen(wideningOp, postState);
			}
			postState = removeNonSharedVariables(postState, entry.getValue());
			result = combineInterferences(result, entry.getKey(), postState);
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
			flattenAbstractState(final Set<DisjunctiveAbstractState<STATE>> setOfStates) {
		if (!setOfStates.isEmpty()) {
			final Iterator<DisjunctiveAbstractState<STATE>> iterator = setOfStates.iterator();
			DisjunctiveAbstractState<STATE> result = iterator.next();
			while (iterator.hasNext()) {
				result = unionIfNonEmpty(result, iterator.next());
			}
			return result;
		}
		return new DisjunctiveAbstractState<>();
	}

	/**
	 *
	 * @param state
	 * @param variables
	 * @return copy of state without the variables that are <b>not</b> in variables
	 */
	private DisjunctiveAbstractState<STATE> removeNonSharedVariables(final DisjunctiveAbstractState<STATE> state,
			final Set<IProgramVar> variables) {
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
				|| mFecUtils.canReadFromInterference(read, mTransitionProvider.getProcedureName(write));
	}
}
