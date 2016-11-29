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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.BoogieVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.RCFGArrayIndexCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPStateBottom;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.ObserverDispatcher;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.ObserverDispatcherSequential;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.RCFGWalkerBreadthFirst;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class HsNonPlugin {
	
	private static final String ULTIMATE_START = "ULTIMATE.start";
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final ILogger mLogger;
	private final ReplacementVarFactory mReplacementVarFactory;

	public HsNonPlugin(IUltimateServiceProvider services, ManagedScript ms, ILogger logger) {
		
		mServices = services;
		mManagedScript = ms;
		mLogger = logger;
		mReplacementVarFactory = new ReplacementVarFactory(ms);
	}
	
	public BoogieIcfgContainer separate(BoogieIcfgContainer oldBoogieIcfg ) {
		
		
		
		/*
		 * obtain partitioning from equality domain abstract interpretation run
		 */
		
		//TODO taken from CodeCheck, what timer is suitable here?
		final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		List<CodeBlock> initialEdges = getInitialEdges(oldBoogieIcfg);
		@SuppressWarnings("unchecked")
		final IAbstractInterpretationResult<VPState, CodeBlock, IProgramVar, ?> abstractInterpretationResult = 
				(IAbstractInterpretationResult<VPState, CodeBlock, IProgramVar, ?>) AbstractInterpreter
			        .runFutureEqualityDomain(oldBoogieIcfg, initialEdges, timer, mServices, false);
		
		VPDomain vpDomain = (VPDomain) abstractInterpretationResult.getUsedDomain();
		
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

		NewArrayIdProvider newArrayIdProvider = 
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

	/**
	 * 
	 * @param vpDomainResult
	 * @param hspav
	 * @return a map of the form (unseparated array --> index --> separated array)
	 */
	private NewArrayIdProvider processAbstractInterpretationResult(
			IAbstractInterpretationResult<VPState, CodeBlock, IProgramVar, ?> vpDomainResult, 
			HeapSepPreAnalysisVisitor hspav) {
		/*
		 * Compute the mapping array to VPState:
		 * The HeapSepPreAnalysisVisitor can tell us which arrays are accessed at which locations.
		 * For each array take only the VPStates intro account that belong to a location directly
		 * before an access to that array. Those are disjoined.
		 */
		Map<IProgramVarOrConst, VPState> arrayToVPState = new HashMap<>();
		for (IProgramVarOrConst array : hspav.getArrayToAccessLocations().getDomain()) {
			VPState disjoinedState = ((VPDomain) vpDomainResult.getUsedDomain()).getBottomState();
			for (IcfgLocation loc : hspav.getArrayToAccessLocations().getImage(array)) {
				Set<VPState> statesAtLoc = vpDomainResult.getLoc2States().get(loc);
				if (statesAtLoc == null) {
					//TODO: this probably should not happen once we support procedures
					continue;
				}
				for (VPState state : statesAtLoc) {
					disjoinedState = disjoinedState.disjoin(state);
					assert disjoinedState != null;
				}
			}
			arrayToVPState.put(array, disjoinedState);
		}
		
		/*
		 * Compute the actual partitioning for each array.
		 */
		RCFGArrayIndexCollector vpPreAnalysis = ((VPDomain) vpDomainResult.getUsedDomain()).getPreAnalysis();
		NewArrayIdProvider newArrayIdProvider = new NewArrayIdProvider(mManagedScript);
		for (Entry<IProgramVarOrConst, VPState> en : arrayToVPState.entrySet()) {
			IProgramVarOrConst currentArray = en.getKey();
			VPState state = en.getValue();
			
			/*
			 * For an index i to be in its own partition (along with its =-equivalence class) for array
			 * a, we have to know that it _must_ be different from all other indices (eq-class representatives)
			 *   that are used for array a
			 * 
			 * (would be nice here, if the EQNodes in the disequality pairs would be only the 
			 *  representatives of each equivalence class.)
			 */
			for (EqNode ind1 : arrayToVPState.get(currentArray).getEquivalenceRepresentatives()) {
				if (!vpPreAnalysis.isArrayAccessedAt(currentArray, ind1)) {
					// we don't need an entry for ind1 in our partitioning map because 
					// it is never used to access the currentArray
					continue;
				}

				/*
				 * 	Check if ind1 is known to be unequal to all the other indices (equality representatives) 
				 * that the array "array" is accessed with?
				 */
				boolean indUneqAllOthers = true;
				for (EqNode ind2 : arrayToVPState.get(currentArray).getEquivalenceRepresentatives()) {
					if (!vpPreAnalysis.isArrayAccessedAt(currentArray, ind2)) {
						// the currentArray is never accessed at ind2
						// --> it does not matter if ind2 may alias with ind1
						continue;
					}
					if (ind2 == ind1) {
						continue;
					}
					if (!state.getDisEqualitySet().contains(new VPDomainSymmetricPair<EqNode>(ind1, ind2))) {
						// ind1 and ind2 may be equal
						indUneqAllOthers = false;
						break;
					}
				}
				
				if (indUneqAllOthers) {
					// ind1 and all EqNodes that are known to be equal get 1 partition.
					newArrayIdProvider.registerDisjunctSinglePointer(currentArray, ind1);
				}
			}
		}
		
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
