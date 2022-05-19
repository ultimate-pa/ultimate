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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
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
	private IIcfg<?> mIcfg;

	public FixpointEngineConcurrent(final FixpointEngineParameters<STATE, ACTION, VARDECL, LOC> params, IIcfg<?> icfg) {
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
			final Map<IProgramNonOldVar, STATE> interferences) {
		/*
		 * TODO:
		 * 	Throw Exception
		 * 	Unsupported Operation
		 */
		return null;
	}
	
	private void calculateFixpoint(final Map<String, ? extends IcfgLocation> entryNodes, final Script script) {
		computeInterferenceLocations(entryNodes);
		// case for empty InterferenceLocations: can be analyzed as normal
		NestedMap2<String, IProgramNonOldVar, STATE> interferences = new NestedMap2<>();
		NestedMap2<String, IProgramNonOldVar, STATE> interferencesOld = new NestedMap2<>();
		

		// create FixpointEngine once for each procedure, reusable?
		// Falls nicht, dann einfach in der While Schleife erzeugen
		Map<String, FixpointEngine<STATE, ACTION, VARDECL, LOC>> fixpointEngineMap = createFixpointEngines();
		
		while (!interferences.equals(interferencesOld) || interferences.isEmpty()) {
			// save current interferences to check if something changed
			interferencesOld = interferences;
			
			entryNodes.forEach((procedure, entry) -> {
				Map<IProgramNonOldVar, STATE> procedureInterferences = computeInterferences(entry, interferences);
				
				/*
				 * TODO:
				 * 	compute AbsInt für procedure mit gefilterten interferences
				 */
				
				/*
				 * TODO:
				 * 	combine result with overall mResult
				 */				
			});
			
			mInterferenceLocations.forEach((procedure, location) -> {
				/*
				 * TODO:
				 * 	compute neues Interferences Set
				 * 		im ersten Schritt ist das die "Union" 
				 * 		über alle Abstract States der shared writes eines procedures
				 */
			});
			
			// not implemented yet
			break;
		}
	}
	
	private void computeInterferenceLocations(final Map<String, ? extends IcfgLocation> entryNodes) {
		Set<IProgramNonOldVar> variables = new HashSet<>();
		entryNodes.forEach((procedure,location) -> variables.addAll(mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable().getModifiedBoogieVars(procedure)));
		
		entryNodes.forEach((procedure,location) -> {
			mInterferenceLocations.put(procedure, new HashSet<>());
			IcfgEdgeIterator iterator = new IcfgEdgeIterator(location.getOutgoingEdges());
			
			Set<IcfgEdge> tempInterferenceEdges = iterator.asStream().filter(edge -> 
				checkSet(edge.getTransformula().getAssignedVars(), variables)).collect(Collectors.toSet());
			tempInterferenceEdges.forEach(edge -> mInterferenceLocations.get(procedure).add(edge.getSource()));
		});
	}
	
	private boolean checkSet(Set<IProgramVar> assignedVars, Set<IProgramNonOldVar> variables) {
		return !assignedVars.stream().filter(x -> variables.contains(x)).collect(Collectors.toSet()).isEmpty();
	}
	
	private Map<IProgramNonOldVar, STATE> computeInterferences(final IcfgLocation entryNode, NestedMap2<String, IProgramNonOldVar, STATE> interferences) {
		/*
		 * TODO:
		 * 	Version 1:
		 * 		filter + union
		 * 	Version 2:
		 * 		filter + special cross product
		 * 	Version 3:
		 * 		filter + special cross product + feasibility check
		 */
		
		// Filter
		Set<String> keys = interferences.keySet().stream().filter(k -> entryNode.getProcedure().equals(k)).collect(Collectors.toSet());
		Map<IProgramNonOldVar, STATE> procedureInterferences = new HashMap<>();
		keys.forEach(k -> procedureInterferences.putAll(interferences.get(k)));
		
		// Union der States einer Variable
		
		
		return procedureInterferences;
	}
	
	private Map<String, FixpointEngine<STATE, ACTION, VARDECL, LOC>> createFixpointEngines() {
		return null;
	}
}
