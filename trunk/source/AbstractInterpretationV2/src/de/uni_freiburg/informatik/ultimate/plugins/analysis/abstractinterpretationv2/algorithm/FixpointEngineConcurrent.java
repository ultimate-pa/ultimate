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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
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
	private final Map<LOC, Set<IProgramVar>> mSharedWrites;
	private final Map<LOC, Set<IProgramVar>> mSharedReads;
	private final Map<LOC, String> mProcedures;
	private final Map<LOC, ACTION> mActions;

	private final FixpointEngine<STATE, ACTION, VARDECL, LOC> mFixpointEngine;

	private final FixpointEngineFactory<STATE, ACTION, VARDECL, LOC> mFixpointEngineFactory;

	public FixpointEngineConcurrent(final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> params,
			final IIcfg<?> icfg, final FixpointEngine<STATE, ACTION, VARDECL, LOC> fxpe,
			final FixpointEngineFactory factory) {
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
		mSharedWrites = new HashMap<>();
		mSharedReads = new HashMap<>();
		mProcedures = new HashMap<>();
		mActions = new HashMap<>();

		mFixpointEngineFactory = factory;
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
		preComputations(entryNodes);
		/*
		 * TODO: case for empty InterferenceLocations can be analyzed as normal
		 */

		Map<LOC, DisjunctiveAbstractState<STATE>> interferences = new HashMap<>();

		while (true) {
			// TODO: implement buildEngine Method
			// mFixpointEngine = mFixpointEngineFactory.buildEngine();

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
			final Map<LOC, DisjunctiveAbstractState<STATE>> tempInterferences = computeNewInterferences(interferences);
			if (interferences.equals(tempInterferences)) {
				break;
			}
			interferences = tempInterferences;
		}
	}

	/**
	 *
	 * @param entryNode
	 *            The entry node in the icfg of the procedure for which the interferences should be computed
	 * @param interferences
	 * @return Map of shared reads to the DisjunctiveAbstractStates the read should read from in this iteration.
	 */
	private Map<ACTION, DisjunctiveAbstractState<STATE>> computeProcedureInterferences(final IcfgLocation entryNode,
			final Map<LOC, DisjunctiveAbstractState<STATE>> interferences) {
		return versionOne(entryNode, interferences);
	}

	/**
	 * Version 1: Union over all procedures
	 *
	 * @param entryNode
	 * @param interferences
	 * @return
	 */
	private Map<ACTION, DisjunctiveAbstractState<STATE>> versionOne(final IcfgLocation entryNode,
			final Map<LOC, DisjunctiveAbstractState<STATE>> interferences) {
		final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterference = new HashMap<>();
		for (final Map.Entry<LOC, Set<IProgramVar>> read : mSharedReads.entrySet()) {
			// procedureInterference.put(mActions.get(read.getKey()), new DisjunctiveAbstractState<>());
			for (final Map.Entry<LOC, DisjunctiveAbstractState<STATE>> interference : interferences.entrySet()) {
				// mSharedWrites.get(interference.getKey()) should be equal to interference.getValue().getVariables()
				// except for different type
				final Set<IProgramVar> variables = mSharedWrites.get(interference.getKey());
				if (DataStructureUtils.haveNonEmptyIntersection(variables, read.getValue())) {
					if (procedureInterference.containsKey(mActions.get(read.getKey()))) {
						final DisjunctiveAbstractState<STATE> tempState =
								procedureInterference.get(mActions.get(read.getKey()));
						procedureInterference.put(mActions.get(read.getKey()),
								unionIfNonEmpty(tempState, interference.getValue()));
					} else {
						procedureInterference.put(mActions.get(read.getKey()), interference.getValue());
					}
				}
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

	/**
	 * Checks whether the key of pos(sible)Interferences is read. And then adds only the read variable to the
	 * interferences
	 *
	 * @param read
	 * @param posInterferences
	 * @param procedureInterferences
	 */
	private void computePossibleUnion(final Entry<ACTION, Set<IProgramVar>> read,
			final Entry<IProgramNonOldVar, DisjunctiveAbstractState<STATE>> posInterferences,
			final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterferences) {
		if (read.getValue().contains(posInterferences.getKey())) {
			// filter out not shared variables
			final DisjunctiveAbstractState<STATE> reducedState = posInterferences.getValue();
			for (final var variable : posInterferences.getValue().getVariables()) {
				if (!read.getValue().contains(variable)) {
					reducedState.removeVariable(variable);
				}
			}
			procedureInterferences.put(read.getKey(),
					unionIfNonEmpty(procedureInterferences.get(read.getKey()), reducedState));
		}
	}

	/**
	 * pre computation over the icfg: shared write locations and share read locations
	 *
	 * @param entryNodes
	 */
	private void preComputations(final Map<String, ? extends IcfgLocation> entryNodes) {
		final Set<IProgramVar> variables = new HashSet<>();
		entryNodes.forEach((procedure, location) -> variables
				.addAll(mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable().getModifiedBoogieVars(procedure)));

		for (final var entry : entryNodes.entrySet()) {
			final IcfgEdgeIterator iterator = new IcfgEdgeIterator(entry.getValue().getOutgoingEdges());
			iterator.asStream().forEach(edge -> computationsPerEdge(entry.getKey(), edge, variables));
		}
	}

	private void computationsPerEdge(final String procedure, final IcfgEdge edge, final Set<IProgramVar> variables) {
		boolean accepted = false;
		// TODO: mSharedReads & mSharedReads only add global variables

		// SharedWrites & mProcedures
		if (DataStructureUtils.haveNonEmptyIntersection(edge.getTransformula().getAssignedVars(), variables)) {
			accepted = true;
			mSharedWrites.put((LOC) edge.getSource(), new HashSet<>());
			edge.getTransformula().getAssignedVars().forEach(var -> mSharedWrites.get(edge.getSource()).add(var));
			mProcedures.put((LOC) edge.getSource(), edge.getPrecedingProcedure());
		}
		// SharedReads
		if (DataStructureUtils.haveNonEmptyIntersection(edge.getTransformula().getInVars().keySet(), variables)) {
			accepted = true;
			mSharedReads.put((LOC) edge.getSource(), new HashSet<>());
			DataStructureUtils.intersection(edge.getTransformula().getInVars().keySet(), variables)
					.forEach(var -> mSharedReads.get(edge.getSource()).add(var));
		}

		// mActions
		if (accepted) {
			mActions.put((LOC) edge.getSource(), (ACTION) edge);
		}
	}

	private Map<LOC, DisjunctiveAbstractState<STATE>>
			computeNewInterferences(final Map<LOC, DisjunctiveAbstractState<STATE>> interferences) {
		Map<LOC, DisjunctiveAbstractState<STATE>> result = copy(interferences);
		for (final Entry<LOC, Set<DisjunctiveAbstractState<STATE>>> entry : mStateStorage.computeLoc2States()
				.entrySet()) {
			if (mSharedWrites.containsKey(entry.getKey())) {
				final DisjunctiveAbstractState<STATE> preState =
						flattenAndReduceAbstractState(entry.getValue(), mSharedWrites.get(entry.getKey()));

				final IAbstractPostOperator<STATE, ACTION> postOp = mDomain.getPostOperator();
				final DisjunctiveAbstractState<STATE> postState = preState.apply(postOp, mActions.get(entry.getKey()));
				// result = combineInterferences(result, entry.getKey(),
				// removeNonSharedVariables(postState, mSharedWrites.get(entry.getKey())));
				result = combineInterferences(result, entry.getKey(), postState);
			}
		}
		return result;
	}

	private Map<LOC, DisjunctiveAbstractState<STATE>> combineInterferences(
			final Map<LOC, DisjunctiveAbstractState<STATE>> interferences, final LOC key,
			final DisjunctiveAbstractState<STATE> postState) {
		if (interferences.containsKey(key)) {
			final DisjunctiveAbstractState<STATE> oldInterferences = interferences.get(key);
			interferences.put(key, unionIfNonEmpty(oldInterferences, postState));
		} else {
			interferences.put(key, postState);
		}
		return interferences;

	}

	private DisjunctiveAbstractState<STATE> flattenAndReduceAbstractState(
			final Set<DisjunctiveAbstractState<STATE>> setOfStates, final Set<IProgramVar> variables) {
		DisjunctiveAbstractState<STATE> result = new DisjunctiveAbstractState<>();

		for (final var state : setOfStates) {
			result = unionIfNonEmpty(result, removeNonSharedVariables(state, variables));
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

	private Map<LOC, DisjunctiveAbstractState<STATE>> filterProcedures(final String name,
			final Map<LOC, DisjunctiveAbstractState<STATE>> interferences) {
		// TODO: check nicer way via .collect ???
		final Map<LOC, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
		interferences.entrySet().stream().filter(a -> mProcedures.get(a.getKey()) == (name))
				.forEach(b -> result.put(b.getKey(), b.getValue()));
		return result;
	}

	private Map<LOC, DisjunctiveAbstractState<STATE>>
			copy(final Map<LOC, DisjunctiveAbstractState<STATE>> interferences) {
		final Map<LOC, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
		interferences.forEach((a, b) -> result.put(a, b));
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
}
