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
 *//*
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

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

	private final Map<String, Set<IcfgLocation>> mInterferenceLocations;
	private final Map<ACTION, Set<IProgramVar>> mSharedReads;
	private final IIcfg<?> mIcfg;

	private final FixpointEngine<STATE, ACTION, VARDECL, LOC> mFixpointEngine;

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
		mInterferenceLocations = new HashMap<>();
		mSharedReads = new HashMap<>();
		mFixpointEngine = fxpe;
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

		// Check for correct type to use for interferences
		final NestedMap2<String, IProgramNonOldVar, DisjunctiveAbstractState<STATE>> interferences = new NestedMap2<>();
		NestedMap2<String, IProgramNonOldVar, DisjunctiveAbstractState<STATE>> interferencesOld = new NestedMap2<>();

		while (!interferences.equals(interferencesOld) || interferences.isEmpty()) {
			interferencesOld = interferences;

			for (final Map.Entry<String, ? extends IcfgLocation> entry : entryNodes.entrySet()) {
				final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterferences =
						computeInterferences(entry.getValue(), interferences);

				// runWithInterferences needs a Collection
				final Collection<LOC> collection = new ArrayList<>();
				collection.add((LOC) entry.getValue());

				final AbsIntResult<STATE, ACTION, LOC> result =
						mFixpointEngine.runWithInterferences(collection, script, procedureInterferences);

				/*
				 * TODO: merge result with overall mResult compute getLoc2States over both AbsIntResult possible but how
				 * do we compute a new AbsIntResult out of the Map -> write merge function for AbsIntResult???
				 */
			}

			for (final Map.Entry<String, Set<IcfgLocation>> entry : mInterferenceLocations.entrySet()) {
				/*
				 * TODO: compute new Interferences Set iterate over all shared writes: new State <= State in mResult
				 * ("+" old State)
				 */
			}

			// not implemented yet
			break;
		}
	}

	/**
	 *
	 * @param entryNode
	 *            The entry node in the icfg of the procedure for which the interferences should be computed
	 * @param interferences
	 * @return Map of shared reads to the DisjunctiveAbstractStates the read should read from in this iteration.
	 */
	private Map<ACTION, DisjunctiveAbstractState<STATE>> computeInterferences(final IcfgLocation entryNode,
			final NestedMap2<String, IProgramNonOldVar, DisjunctiveAbstractState<STATE>> interferences) {

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
			final NestedMap2<String, IProgramNonOldVar, DisjunctiveAbstractState<STATE>> interferences) {

		final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterferences = new HashMap<>();

		for (final Map.Entry<ACTION, Set<IProgramVar>> read : mSharedReads.entrySet()) {
			procedureInterferences.put(read.getKey(), new DisjunctiveAbstractState<>());
			for (final String procedure : interferences.keySet()) {
				for (final Map.Entry<IProgramNonOldVar, DisjunctiveAbstractState<STATE>> state : interferences
						.get(procedure).entrySet()) {
					computePossibleUnion(read, state, procedureInterferences);
				}
			}
		}

		/*
		 * TODO: maybe add only the write from the own thread which it can read from
		 *
		 * add writes from own procedure & remove variables from State that are not read in the read Statement
		 */

		return procedureInterferences;
	}

	/**
	 * Version 2: filter procedures + special cross product
	 *
	 * @param entryNode
	 * @param interferences
	 * @return
	 */
	private Map<ACTION, DisjunctiveAbstractState<STATE>> versionTwo(final IcfgLocation entryNode,
			final NestedMap2<String, IProgramNonOldVar, DisjunctiveAbstractState<STATE>> interferences) {
		final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterferences = new HashMap<>();

		// Filter procedures
		final Set<String> keys = interferences.keySet().stream().filter(k -> !entryNode.getProcedure().equals(k))
				.collect(Collectors.toSet());
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
			final NestedMap2<String, IProgramNonOldVar, DisjunctiveAbstractState<STATE>> interferences) {
		final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterferences = new HashMap<>();

		// Filter procedures
		final Set<String> keys = interferences.keySet().stream().filter(k -> !entryNode.getProcedure().equals(k))
				.collect(Collectors.toSet());
		return procedureInterferences;
	}

	private void computePossibleUnion(final Entry<ACTION, Set<IProgramVar>> read,
			final Entry<IProgramNonOldVar, DisjunctiveAbstractState<STATE>> state,
			final Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterferences) {
		if (read.getValue().contains(state.getKey())) {
			/*
			 * TODO: check whether filtering should be done here
			 */
			final DisjunctiveAbstractState<STATE> result = state.getValue();
			for (final var variable : state.getValue().getVariables()) {
				if (!read.getValue().contains(variable)) {
					result.removeVariable(variable);
				}
			}
			procedureInterferences.get(read.getKey()).union(state.getValue());
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
			mInterferenceLocations.put(entry.getKey(), new HashSet<>());

			final IcfgEdgeIterator iterator = new IcfgEdgeIterator(entry.getValue().getOutgoingEdges());
			iterator.asStream().forEach(edge -> computationsPerEdge(entry.getKey(), edge, variables));
		}
	}

	private void computationsPerEdge(final String procedure, final IcfgEdge edge, final Set<IProgramVar> variables) {
		// compute SharedWrites
		if (DataStructureUtils.haveNonEmptyIntersection(edge.getTransformula().getAssignedVars(), variables)) {
			mInterferenceLocations.get(procedure).add(edge.getSource());
		}

		if (DataStructureUtils.haveNonEmptyIntersection(edge.getTransformula().getInVars().keySet(), variables)) {
			mSharedReads.put((ACTION) edge, new HashSet<>());
			edge.getTransformula().getInVars().keySet().forEach(var -> mSharedReads.get(edge).add(var));
		}
	}
}
