/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbsIntResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IFixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.SummaryMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Fixpoint engine for a thread modular approach using another {@code IFixpointEngine}.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 */
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
	private final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> mParams;
	private final ConcurrentIcfgAnalyzer<ACTION, LOC> mAnalyzer;

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
		mAnalyzer = new ConcurrentIcfgAnalyzer<>(icfg);
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
		final Set<LOC> reachableErrorLocations = new HashSet<>();
		while (true) {
			mLogger.info("Starting outer Fixpoint iteration number " + iteration);
			for (final String procedure : mAnalyzer.getTopologicalProcedureOrder()) {
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
				threadResult.getLoc2States().forEach(
						(k, v) -> mStateStorage.addAbstractState(k, DisjunctiveAbstractState.createDisjunction(v)));
				// Add present counterexamples
				for (final var counterExample : threadResult.getCounterexamples()) {
					final var execution = counterExample.getAbstractExecution();
					final var errorLocation = execution.get(execution.size() - 1).getSecond();
					if (reachableErrorLocations.add(errorLocation)) {
						mResult.addCounterexample(counterExample);
					}
				}
			}

			final Map<LOC, DisjunctiveAbstractState<STATE>> newInterferences =
					computeNewInterferences(getPostStatesOnSharedVariables());

			if (interferencesAreEqual(interferences, newInterferences)) {
				mLogger.info("Fixpoint after " + iteration + " iterations found.");
				break;
			}
			// Compute the new interferences. Use the newly computed or widen them if necessary.
			if (iteration < mMaxUnwindings) {
				interferences = newInterferences;
			} else {
				mLogger.info("Applying widenning to the interferences.");
				interferences = widenInterferences(interferences, newInterferences);
			}
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
		DisjunctiveAbstractState<STATE> result = null;
		for (final LOC loc : mAnalyzer.getForkLocations(procedure)) {
			final DisjunctiveAbstractState<STATE> state = mStateStorage.getAbstractState(loc);
			if (state == null) {
				result = null;
				break;
			}
			// TODO: Is it safe to remove all not IProgramNonOldVar, or should we just remove the ILocalProgramVars?
			final List<IProgramVarOrConst> varsToRemove = state.getVariables().stream()
					.filter(x -> !(x instanceof IProgramNonOldVar)).collect(Collectors.toList());
			final DisjunctiveAbstractState<STATE> clearedState = state.removeVariables(varsToRemove);
			result = result == null ? clearedState : result.union(clearedState);
		}
		return result != null ? result : new DisjunctiveAbstractState<>(mMaxParallelStates, mDomain.createTopState());
	}

	private Map<LOC, DisjunctiveAbstractState<STATE>>
			computeNewInterferences(final Map<ACTION, DisjunctiveAbstractState<STATE>> postStatesOnSharedVariables) {
		final Map<LOC, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
		for (final LOC entryLoc : mEntryLocs.values()) {
			new IcfgLocationIterator<>(entryLoc).forEachRemaining(loc -> {
				final DisjunctiveAbstractState<STATE> interferingState =
						getInterferingState(loc, postStatesOnSharedVariables);
				if (interferingState != null) {
					result.put(loc, interferingState);
				}
			});
		}
		return result;
	}

	private DisjunctiveAbstractState<STATE> getInterferingState(final LOC loc,
			final Map<ACTION, DisjunctiveAbstractState<STATE>> postStates) {
		final Set<ACTION> interferingWrites = mAnalyzer.getInterferingWrites(loc);
		return postStates.keySet().stream().filter(interferingWrites::contains).map(postStates::get)
				.reduce(FixpointEngineConcurrentUtils::unionOnSharedVariables).orElse(null);
	}

	private Map<ACTION, DisjunctiveAbstractState<STATE>> getPostStatesOnSharedVariables() {
		return mAnalyzer.getSharedWrites().entrySet().stream()
				.collect(Collectors.toMap(Entry::getKey, x -> getStateAfterWrite(x.getKey(), x.getValue())));
	}

	private DisjunctiveAbstractState<STATE> getStateAfterWrite(final ACTION write,
			final Set<IProgramVarOrConst> variables) {
		final DisjunctiveAbstractState<STATE> preState =
				mStateStorage.getAbstractState(mTransitionProvider.getSource(write));
		final DisjunctiveAbstractState<STATE> postState;
		if (preState == null) {
			// If the source is not present in mStateStorage, fall back to the target
			postState = mStateStorage.getAbstractState(mTransitionProvider.getTarget(write));
		} else {
			// Otherwise apply the post operator
			postState = preState.apply(mDomain.getPostOperator(), write);
		}
		// If the post state is still null (i.e. neither source nor target are in mStateStorage), return a top state
		if (postState == null) {
			return new DisjunctiveAbstractState<>(mMaxParallelStates, mDomain.createTopState()).addVariables(variables);
		}
		return postState.removeVariables(DataStructureUtils.difference(postState.getVariables(), variables));
	}

	private boolean interferencesAreEqual(final Map<LOC, DisjunctiveAbstractState<STATE>> oldInts,
			final Map<LOC, DisjunctiveAbstractState<STATE>> newInts) {
		if (oldInts.size() != newInts.size()) {
			return false;
		}
		// TODO: Should we keep equal here or use isSubset instead?
		return oldInts.keySet().stream().allMatch(x -> oldInts.get(x).isEqualTo(newInts.get(x)));
	}
}
