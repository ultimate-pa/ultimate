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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RCFGLiteralCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.initializer.FixpointEngineParameterFactory;
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
	
	private Map<String, Set<IcfgLocation>> mInterferenceLocations;
	private Map<ACTION, Set<IProgramVar>> mSharedReads;
	private IIcfg<?> mIcfg;
	
	private final FixpointEngine<STATE, ACTION, VARDECL, LOC> mFixpointEngine;

	public FixpointEngineConcurrent(final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> params, IIcfg<?> icfg, 
			final FixpointEngine<STATE, ACTION, VARDECL, LOC> fxpe) {
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
	public AbsIntResult<STATE, ACTION, LOC> runWithInterferences(final Collection<? extends LOC> initialNodes, final Script script, 
			final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences) {
		throw new UnsupportedOperationException("Operation not supported for FixpointEngineConcurrent");
	}
	
	private void calculateFixpoint(final Map<String, ? extends IcfgLocation> entryNodes, final Script script) {
		preComputations(entryNodes);
		/*
		 *  TODO: case for empty InterferenceLocations
		 *  	can be analyzed as normal
		 */
		
		// Check for correct type to use for interferences
		NestedMap2<String, IProgramNonOldVar, DisjunctiveAbstractState<STATE>> interferences = new NestedMap2<>();
		NestedMap2<String, IProgramNonOldVar, DisjunctiveAbstractState<STATE>> interferencesOld = new NestedMap2<>();

		while (!interferences.equals(interferencesOld) || interferences.isEmpty()) {
			interferencesOld = interferences;
			
			entryNodes.forEach((procedure, entry) -> {
				Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterferences = computeInterferences(entry, interferences);
				
				Collection<LOC> collection = new ArrayList<>();
				
				
				// ugly cast !!!
				collection.add((LOC) entry);
				
				AbsIntResult<STATE, ACTION, LOC> result = mFixpointEngine.runWithInterferences(collection, script, procedureInterferences);
				
				/*
				 * TODO: merge result with overall mResult
				 * 		compute getLoc2States over both AbsIntResult possible
				 * 		but how do we compute a new AbsIntResult out of the Map
				 * 		-> write merge function for AbsIntResult???
				 */
			});
			
			mInterferenceLocations.forEach((procedure, location) -> {
				/*
				 * TODO: compute new Interferences Set
				 * 		iterate over all shared writes:
				 * 		new State <= State in mResult ("+" old State)
				 */
				
			});
			
			// not implemented yet
			break;
		}
	}
	
	/**
	 * 
	 * @param entryNode
	 * @param interferences
	 * @return Map of shared reads to the DisjunctiveAbstractStates this read should read from in this iteration.
	 */
	private Map<ACTION, DisjunctiveAbstractState<STATE>> computeInterferences(final IcfgLocation entryNode, 
			NestedMap2<String, IProgramNonOldVar, DisjunctiveAbstractState<STATE>> interferences) {
		Map<ACTION, DisjunctiveAbstractState<STATE>> procedureInterferences = new HashMap<>();
		
		/*
		 * TODO: implement the different versions
		 *  filter = filter out interferences from own procedure
		 * 	Version 1:
		 * 		filter + union
		 * 	Version 2:
		 * 		filter + special cross product
		 * 	Version 3:
		 * 		filter + special cross product + feasibility check
		 */
		
		// Filter
		Set<String> keys = interferences.keySet().stream().filter(k -> 
			entryNode.getProcedure().equals(k)).collect(Collectors.toSet());
		
		// Union
		mSharedReads.forEach((action, vars) -> {
			procedureInterferences.put(action, new DisjunctiveAbstractState<>());
			keys.forEach(procedure -> {
				interferences.get(procedure).forEach((var, state) -> {
					if (vars.contains(var)) {
						procedureInterferences.get(action).union(state);
					}
				});
			});
		});
		
		/*
		 * TODO: add writes from own procedure & remove variables from State that are not read in the read Statement
		 * 	add shared write if there is a way from the shared write to the share read with no other share write on it
		 * 	-> does not change, is possible to precompute
		 */	
		
		return procedureInterferences;
	}
	
	/**
	 * 
	 * @param entryNodes
	 */
	private void preComputations(final Map<String, ? extends IcfgLocation> entryNodes) {
		Set<IProgramNonOldVar> variables = new HashSet<>();
		entryNodes.forEach((procedure,location) -> 
			variables.addAll(mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable().getModifiedBoogieVars(procedure)));
		
		entryNodes.forEach((procedure,location) -> {
			IcfgEdgeIterator iterator = new IcfgEdgeIterator(location.getOutgoingEdges());
			
			// compute SharedWrites
			mInterferenceLocations.put(procedure, new HashSet<>());
			Set<IcfgEdge> tempInterferenceEdges = iterator.asStream().filter(edge -> 
				intersectionEmpty(edge.getTransformula().getAssignedVars(), variables)).collect(Collectors.toSet());
			tempInterferenceEdges.forEach(edge -> mInterferenceLocations.get(procedure).add(edge.getSource()));
			
			// compute SharedReads			
			Set<IcfgEdge> tempSharedReads = iterator.asStream().filter(edge -> 
				intersectionEmpty(edge.getTransformula().getInVars().keySet(), variables)).collect(Collectors.toSet());
			tempSharedReads.forEach(edge -> {
				
				// ugly cast!!!
			 	mSharedReads.put((ACTION) edge, new HashSet<>());
				edge.getTransformula().getInVars().keySet().forEach(var -> mSharedReads.get(edge).add(var));
			});
		});
	}
	
	/**
	 * 
	 * @param set1
	 * @param set2
	 * @return true if the intersection of set1 and set2 is not emtpy
	 */
	private boolean intersectionEmpty(Set<IProgramVar> set1, Set<IProgramNonOldVar> set2) {
		return !set1.stream().filter(x -> set2.contains(x)).collect(Collectors.toSet()).isEmpty();
	}
}
