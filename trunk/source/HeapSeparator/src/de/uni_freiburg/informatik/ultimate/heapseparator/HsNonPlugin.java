package de.uni_freiburg.informatik.ultimate.heapseparator;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.ObserverDispatcher;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.ObserverDispatcherSequential;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker.RCFGWalkerBreadthFirst;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class HsNonPlugin {
	
	private static final String ULTIMATE_START = "ULTIMATE.start";
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private ILogger mLogger;

	public HsNonPlugin(IUltimateServiceProvider services, ManagedScript ms, ILogger logger) {
		
		mServices = services;
		mManagedScript = ms;
		mLogger = logger;
	}
	
	public BoogieIcfgContainer separate(BoogieIcfgContainer oldBoogieIcfg ) {
		
		
//		ReplacementVarFactory rvf = new ReplacementVarFactory(ms);
		
		/*
		 * obtain partitioning from equality domain abstract interpretation run
		 */
		
		//TODO taken from CodeCheck, what timer is suitable here?
		final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		List<CodeBlock> initialEdges = getInitialEdges(oldBoogieIcfg);
		final IAbstractInterpretationResult<?, CodeBlock, IBoogieVar, BoogieIcfgLocation> result = AbstractInterpreter
			        .run(oldBoogieIcfg, initialEdges, timer, mServices);
		
		/*
		 * process AI result
		 *  - bring result into partition-form (if it is not yet)
		 *  - do sanity preprocessing: 
		 *    if, at any point in the program, two arrays are assigned to each other, then their partitionings
		 *    must be made compatible
		 *     (equal?, through union of partitions?)
		 */
		HashMap<IProgramVar, HashMap<IProgramVar, IProgramVar>> oldArrayToPointerToNewArray = null;

		{
			final ObserverDispatcher od = new ObserverDispatcherSequential(mLogger);
			final RCFGWalkerBreadthFirst walker = new RCFGWalkerBreadthFirst(od, mLogger);
			od.setWalker(walker);

			HeapSepPreAnalysisVisitor hspav = new HeapSepPreAnalysisVisitor(mLogger);
			walker.addObserver(hspav);
			walker.run(initialEdges.iterator().next().getTarget()); // TODO: whih location to take really??
		}
		

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
