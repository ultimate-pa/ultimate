/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE HeapSeparator plug-in.
 *
 * The ULTIMATE HeapSeparator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE HeapSeparator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE HeapSeparator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE HeapSeparator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE HeapSeparator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.heapseparator;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.RCFGArrayIndexCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.ObserverDispatcher;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.ObserverDispatcherSequential;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.RCFGWalkerBreadthFirst;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class HsNonPlugin {
	
	private static final String ULTIMATE_START = "ULTIMATE.start";
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final ILogger mLogger;
	private final ReplacementVarFactory mReplacementVarFactory;

	public HsNonPlugin(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit, final ILogger logger) {
		
		mServices = services;
		mManagedScript = csToolkit.getManagedScript();
		mLogger = logger;
		mReplacementVarFactory = new ReplacementVarFactory(csToolkit.getManagedScript(), csToolkit.getSymbolTable());
	}
	
	public BoogieIcfgContainer separate(final BoogieIcfgContainer oldBoogieIcfg ) {
		/*
		 * obtain partitioning from equality domain abstract interpretation run
		 */
		
		//TODO taken from CodeCheck, what timer is suitable here?
		final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		final List<CodeBlock> initialEdges = getInitialEdges(oldBoogieIcfg);
		@SuppressWarnings("unchecked")
		final IAbstractInterpretationResult<VPState, CodeBlock, IProgramVar, ?> abstractInterpretationResult = 
				(IAbstractInterpretationResult<VPState, CodeBlock, IProgramVar, ?>) AbstractInterpreter
			        .runFutureEqualityDomain(oldBoogieIcfg, initialEdges, timer, mServices, false);
		
		final VPDomain vpDomain = (VPDomain) abstractInterpretationResult.getUsedDomain();
		
		printAIResult(abstractInterpretationResult);
		
		/*
		 * process AI result
		 *  - bring result into partition-form (if it is not yet)
		 *  - do sanity preprocessing: 
		 *    if, at any point in the program, two arrays are assigned to each other, then their partitionings
		 *    must be made compatible
		 *     (equal?, through union of partitions?)
		 */
		HeapSepPreAnalysisVisitor heapSepPreanalysis = null;
		{
			final ObserverDispatcher od = new ObserverDispatcherSequential(mLogger);
			final RCFGWalkerBreadthFirst walker = new RCFGWalkerBreadthFirst(od, mLogger);
			od.setWalker(walker);

			heapSepPreanalysis = new HeapSepPreAnalysisVisitor(mLogger);
			walker.addObserver(heapSepPreanalysis);
				
			walker.run(BoogieIcfgContainer.extractStartEdges(oldBoogieIcfg)); 
		}

		final NewArrayIdProvider newArrayIdProvider = 
				processAbstractInterpretationResult(abstractInterpretationResult, heapSepPreanalysis);
		
		/*
		 * do the transformation itself..
		 */
		
		final ObserverDispatcher od = new ObserverDispatcherSequential(mLogger);
		final RCFGWalkerBreadthFirst walker = new RCFGWalkerBreadthFirst(od, mLogger);
		od.setWalker(walker);

		final HeapSepRcfgVisitor hsv = new HeapSepRcfgVisitor(mLogger, newArrayIdProvider, mManagedScript, vpDomain);
		walker.addObserver(hsv);
		walker.run(BoogieIcfgContainer.extractStartEdges(oldBoogieIcfg));
	

		return null;
	}

	private void printAIResult(
			final IAbstractInterpretationResult<VPState, CodeBlock, IProgramVar, ?> abstractInterpretationResult) {
		mLogger.debug("equality domain result");
		for (Entry<?, Set<VPState>> en : abstractInterpretationResult.getLoc2States().entrySet()) {
			mLogger.debug(en.getKey());
			for (VPState vps : en.getValue()) {
				mLogger.debug("");
				mLogger.debug(vps);
			}
		}
	}

	/**
	 * 
	 * @param vpDomainResult
	 * @param hspav
	 * @return a map of the form (unseparated array --> index --> separated array)
	 */
	private NewArrayIdProvider processAbstractInterpretationResult(
			final IAbstractInterpretationResult<VPState, CodeBlock, IProgramVar, ?> vpDomainResult, 
			final HeapSepPreAnalysisVisitor hspav) {
		
		final VPDomain vpDomain = (VPDomain) vpDomainResult.getUsedDomain();
		
		/*
		 * Compute the mapping array to VPState:
		 * The HeapSepPreAnalysisVisitor can tell us which arrays are accessed at which locations.
		 * For each array take only the VPStates intro account that belong to a location directly
		 * before an access to that array. Those are disjoined.
		 */
		final Map<IProgramVarOrConst, VPState> arrayToVPState = new HashMap<>();
		for (final IProgramVarOrConst array : hspav.getArrayToAccessLocations().getDomain()) {
			VPState disjoinedState = vpDomain.getBottomState();
			for (final IcfgLocation loc : hspav.getArrayToAccessLocations().getImage(array)) {
				final Set<VPState> statesAtLoc = vpDomainResult.getLoc2States().get(loc);
				if (statesAtLoc == null) {
					//TODO: this probably should not happen once we support procedures
					continue;
				}
				for (final VPState state : statesAtLoc) {
					disjoinedState = vpDomain.getVpStateFactory().disjoin(disjoinedState, state);
					assert disjoinedState != null;
				}
			}
			arrayToVPState.put(array, disjoinedState);
		}
		
		/*
		 * Compute the actual partitioning for each array.
		 */
		final RCFGArrayIndexCollector vpPreAnalysis = ((VPDomain) vpDomainResult.getUsedDomain()).getPreAnalysis();
		final NewArrayIdProvider newArrayIdProvider = new NewArrayIdProvider(mManagedScript);
		for (final Entry<IProgramVarOrConst, VPState> en : arrayToVPState.entrySet()) {
			final IProgramVarOrConst currentArray = en.getKey();
			final VPState state = en.getValue();
			
			
			UnionFind<EqNode> uf = new UnionFind<>();
			for (EqNode accessingNode : vpPreAnalysis.getAccessingIndicesForArray(currentArray)) {
				uf.findAndConstructEquivalenceClassIfNeeded(accessingNode);
			}
			//TODO: optimization: compute partitioning on the equivalence class representatives instead
			//  of all nodes
			for (EqNode accessingNode1 : vpPreAnalysis.getAccessingIndicesForArray(currentArray)) {
				for (EqNode accessingNode2 : vpPreAnalysis.getAccessingIndicesForArray(currentArray)) {
					if (state.mayEqual(accessingNode1, accessingNode2)) {
						uf.union(accessingNode1, accessingNode2);
					}
				}
			}
			for (Set<EqNode> ec : uf.getAllEquivalenceClasses()) {
				newArrayIdProvider.registerEquivalenceClass(currentArray, ec);
			}
		}
			
//			/*
//			 * For an index i to be in its own partition (along with its =-equivalence class) for array
//			 * a, we have to know that it _must_ be different from all other indices (eq-class representatives)
//			 *   that are used for array a
//			 * 
//			 * (would be nice here, if the EQNodes in the disequality pairs would be only the 
//			 *  representatives of each equivalence class.)
//			 */
//			for (final EqNode ind1 : arrayToVPState.get(currentArray).getEquivalenceRepresentatives()) {
//				if (!vpPreAnalysis.isArrayAccessedAt(currentArray, ind1)) {
//					// we don't need an entry for ind1 in our partitioning map because 
//					// it is never used to access the currentArray
//					continue;
//				}
//
//				/*
//				 * 	Check if ind1 is known to be unequal to all the other indices (equality representatives) 
//				 * that the array "array" is accessed with?
//				 */
//				boolean indUneqAllOthers = true;
//				for (final EqNode ind2 : arrayToVPState.get(currentArray).getEquivalenceRepresentatives()) {
//					if (!vpPreAnalysis.isArrayAccessedAt(currentArray, ind2)) {
//						// the currentArray is never accessed at ind2
//						// --> it does not matter if ind2 may alias with ind1
//						continue;
//					}
//					if (ind2 == ind1) {
//						continue;
//					}
//					if (!state.getDisEqualitySet().contains(new VPDomainSymmetricPair<EqNode>(ind1, ind2))) {
//						// ind1 and ind2 may be equal
//						indUneqAllOthers = false;
//						break;
//					}
//				}
//				
//				if (indUneqAllOthers) {
//					// ind1 and all EqNodes that are known to be equal get 1 partition.
//					newArrayIdProvider.registerDisjunctSinglePointer(currentArray, ind1);
//				}
//			}
//		}
		
		return newArrayIdProvider;
	}

	/**
	 * copied from CodeCheck 
	 * TODO: ugly, right?..
	 * @param root
	 * @return
	 */
	private List<CodeBlock> getInitialEdges(final BoogieIcfgContainer root) {
		final Collection<IcfgEdge> startEdges = BoogieIcfgContainer.extractStartEdges(root);

		final Set<BoogieIcfgLocation> ultimateStartNodes = startEdges.stream().map(a -> a.getSource())
		        .filter(source -> source instanceof BoogieIcfgLocation
		                && ((BoogieIcfgLocation) source).getProcedure().equals(ULTIMATE_START))
		        .map(a -> (BoogieIcfgLocation) a).collect(Collectors.toSet());
		if (!ultimateStartNodes.isEmpty()) {
//			mLogger.info("Found entry method " + ULTIMATE_START);
			return ultimateStartNodes.stream().flatMap(a -> a.getOutgoingEdges().stream()).map(a -> (CodeBlock) a)
			        .collect(Collectors.toList());
		}
//		mLogger.info("Did not find entry method " + ULTIMATE_START + ", using library mode");
		return startEdges.stream().filter(a -> a instanceof CodeBlock).map(a -> (CodeBlock) a)
		        .collect(Collectors.toList());
	}
}
