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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.BoogieVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.RCFGArrayIndexCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.VPState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.VPStateBottom;
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
		RCFGArrayIndexCollector preAnalysis = vpDomain.getPreAnalysis();
		
		/*
		 * process AI result
		 *  - bring result into partition-form (if it is not yet)
		 *  - do sanity preprocessing: 
		 *    if, at any point in the program, two arrays are assigned to each other, then their partitionings
		 *    must be made compatible
		 *     (equal?, through union of partitions?)
		 */
		HeapSepPreAnalysisVisitor hspav = null;
		{
			final ObserverDispatcher od = new ObserverDispatcherSequential(mLogger);
			final RCFGWalkerBreadthFirst walker = new RCFGWalkerBreadthFirst(od, mLogger);
			od.setWalker(walker);

			hspav = new HeapSepPreAnalysisVisitor(mLogger);
			walker.addObserver(hspav);
			walker.run(initialEdges.iterator().next().getTarget()); // TODO: which location to take really??
		}

		NestedMap2<IProgramVar, IProgramVar, IProgramVar> oldArrayToPointerToNewArray = 
				processAbstractInterpretationResult(abstractInterpretationResult, hspav);

	

		/*
		 * do the transformation itself..
		 */
		
		final ObserverDispatcher od = new ObserverDispatcherSequential(mLogger);
		final RCFGWalkerBreadthFirst walker = new RCFGWalkerBreadthFirst(od, mLogger);
		od.setWalker(walker);

		final HeapSepRcfgVisitor hsv = new HeapSepRcfgVisitor(mLogger, oldArrayToPointerToNewArray, mManagedScript);
		walker.addObserver(hsv);
		walker.run(initialEdges.iterator().next().getTarget()); // TODO: whih location to take really??
	

		return null;
	}

	/**
	 * 
	 * @param result
	 * @param hspav
	 * @return a map of the form (unseparated array --> index --> separated array)
	 */
	private NestedMap2<BoogieVarOrConst, BoogieVarOrConst, BoogieVarOrConst> processAbstractInterpretationResult(
			IAbstractInterpretationResult<VPState, CodeBlock, IProgramVar, ?> result, 
			HeapSepPreAnalysisVisitor hspav) {

		VPDomain vpDomain = (VPDomain) result.getUsedDomain();
		
		/*
		 * disjoin:
		 *  - procedurewise??
		 *  - per array? --> then only take positions where that array is used??
		 */
		// TODO: disjoin procedurewise? now: global
		Map<BoogieVarOrConst, VPState> arrayToVPState = new HashMap<>();
		
		for (BoogieVarOrConst array : hspav.getArrayToAccessLocations().getDomain()) {
			VPState disjoinedState = vpDomain.getBottomState();
			for (IcfgLocation loc : hspav.getArrayToAccessLocations().getImage(array)) {
				disjoinedState = disjoinedState.disjoin(result.getLoc2SingleStates().get(loc));
			}
			arrayToVPState.put(array, disjoinedState);
		}
		
		Map<BoogieVarOrConst, Set<EqNode>> arrayToPartition = new HashMap<>();
		
		for (Entry<BoogieVarOrConst, VPState> en : arrayToVPState.entrySet()) {
			BoogieVarOrConst array = en.getKey();
			VPState state = en.getValue();
			
			/*
			 * For an index i to be in its own partition (along with its =-equivalence class) for array
			 * a, we have to know that it _must_ be different from all other indices (eq-class representatives)
			 *   that are used for array a
			 * 
			 * (would be nice here, if the EQNodes in the disequality pairs would be only the 
			 *  representatives of each equivalence class.)
			 */
			for (EqNode ind1 : arrayToVPState.get(array).getEquivalenceRepresentatives()) {
				/*
				 * 	question: is ind known to be unequal to all the other indices (equality representatives) of array?
				 *   --> then it and its equal elements are
				 */
				boolean indUneqAllOthers = true;
				for (EqNode ind2 : arrayToVPState.get(array).getEquivalenceRepresentatives()) {
					if (ind2 == ind1) {
						continue;
					}
					if (!state.getDisEqualitySet().contains(new VPDomainSymmetricPair<EqNode>(ind1, ind2))) {
						// ind1 and ind2 may be equal
						indUneqAllOthers = false;
					}
				}
				
				if (indUneqAllOthers) {
					// ind1 and all EqNodes that are known to be equal get 1 partition.
					arrayToPartition.put(array, arrayToVPState.get(array).getEquivalentEqNodes(ind1));
					NestedMap2<BoogieVarOrConst, BoogieVarOrConst, ReplacementVar> arrayToRepresentativeToFreshArrayVar =
							new NestedMap2<>();

					arrayToRepresentativeToFreshArrayVar.put(
							array, ind1, mReplacementVarFactory.getOrConstuctReplacementVar(array));
				}
			}
		}
		
		// TODO Auto-generated method stub
		return null;
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
