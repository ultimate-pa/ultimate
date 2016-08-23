package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.paralleldfg;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.osgi.internal.messages.Msg;

import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.dataflow.DataflowState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class ParallelDfgGeneratorObserver extends BaseObserver {

	final private ILogger mLogger;
	final private IUltimateServiceProvider mServices;
	IAbstractInterpretationResult<DataflowState, CodeBlock, IProgramVar, ProgramPoint> mDataflowAnalysisResult;
	private Integer mEdgeCount;
	private Integer mNodeCount;

	public ParallelDfgGeneratorObserver(ILogger logger, IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
		mDataflowAnalysisResult = null;
		mEdgeCount = 0;
		mNodeCount = 0;
	}


	@Override
	public boolean process(IElement root) throws Throwable {
		
		// rootNode is the dummy note with edges leading to every procedure entry point
		RootNode rootNode = (RootNode) root;
		// n = number of threads. Carefull with init procedure
		int n = rootNode.getOutgoingEdges().size();
		
		

		mDataflowAnalysisResult = obtainDataflowAnalysisResult(rootNode);
		
		/*
		// the result aiRes can be queried for each state as follows
		// (replace null by a ProgramPoint)
		DataflowState dfs = dataflowAnalysisResult.getLoc2SingleStates().get(null);
		// query the state at each ProgramPoint for the dataflow results as follows 
		// (replace null by a real variable)
		Set<ProgramPoint> nwls = dfs.getNowriteLocations((IProgramVar) null);
		Set<CodeBlock> rd = dfs.getReachingDefinitions((IProgramVar) null);
		*/

		// look for asserts in the RCFG
		List<RCFGNode> nodes = new ArrayList<RCFGNode>();

		// ignore the first edge from the dummy root to the function entry
		for (RCFGEdge e: rootNode.getOutgoingEdges()){
			Set<RCFGNode> a = nodesInGraph(e.getTarget());

			nodes.addAll(a);
		}
		
		// compute end and error locations
		List<List<RCFGNode>> endError = getEndErrorLocations(nodes);
		List<RCFGNode> assertLocs = endError.get(0);
		List<RCFGNode> endLocs = endError.get(1);
		
		if (assertLocs.isEmpty()){
			// no asserts,  nothing to check
			return false;
		}
		// compute Start Locations
		List<ParallelDataflowgraph<RCFGEdge>> starts = computeStartLocs(assertLocs, endLocs);
		mNodeCount = starts.size();
		
		
		
		// Debug info before computation of DFG
		mLogger.debug("Number of Threads: " + (n-1));
		mLogger.debug("Number of Asserts: " + assertLocs.size());
		if (n == endLocs.size()){
			mLogger.debug("More than one return per Thread: False");
			}
		else {
			mLogger.debug("More than one return per Thread: True");
			}
		mLogger.debug("Number of start nodes: " + starts.size());
		mLogger.debug("Start node(s):  " );
		for (ParallelDataflowgraph<RCFGEdge> s : starts){
			mLogger.debug("  " + s.toString());
		}
		
		
		// Algorithm with the start Locations
		collectDFGEdges(starts);
		
		
		// Debug info after the algorithm
		mLogger.debug("Total number of nodes in the Parallel DFG: " + mNodeCount);
		mLogger.debug("Total number of edges in the Parallel DFG: " + mEdgeCount);
		
		
		return false;
	}


	private IAbstractInterpretationResult<DataflowState, CodeBlock, IProgramVar, ProgramPoint> obtainDataflowAnalysisResult(RootNode r) {
		List<CodeBlock> edges = new ArrayList<>();
		r.getRootAnnot().getEntryNodes();
		for (Entry<String, ProgramPoint> en : r.getRootAnnot().getEntryNodes().entrySet())
			edges.add((CodeBlock) en.getValue().getOutgoingEdges().get(0));
		
		final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		return AbstractInterpreter.runFuture(r, edges, timer, mServices, false);
	}
	
	
	// Algorithm
	private void collectDFGEdges(List<ParallelDataflowgraph<RCFGEdge>> starts){
		// compute the edges
		List<ParallelDataflowgraph<RCFGEdge>> Q = starts;
		Set<ParallelDataflowgraph<RCFGEdge>> visited = new HashSet<ParallelDataflowgraph<RCFGEdge>>();
		while(!Q.isEmpty()){
			ParallelDataflowgraph<RCFGEdge> node = Q.get(0);
			Q.remove(0);
			// get the use of the Reaching Definition
			CodeBlock cb = (CodeBlock) node.getNodeLabel();
			// better would be .entrySet();
			Set<IProgramVar> use = cb.getTransitionFormula().getInVars().keySet(); 
			mLogger.debug("Explain " + use.size() + " variable(s) for the statement " + cb.toString());
			for (IProgramVar x: use){
				mLogger.debug("   explain the variable " + x.toString());
				List<ParallelDataflowgraph<RCFGEdge>> sources = explain(x, node);
				for (ParallelDataflowgraph<RCFGEdge> s : sources){
					if (!visited.contains(s)){
						Q.add(s);
						visited.add(s);
					}
					// Add an edge
					s.addOutgoingNode(node, x);
					node.addIncomingNode(s);
					mEdgeCount++;
				}
			}	
		}
	}

	private List<ParallelDataflowgraph<RCFGEdge>> explain(IProgramVar var, ParallelDataflowgraph node){
		// TODO handle the special case init in the Reaching Definition
		// init is only inserted as an edge, if init is in all the Reaching Definitions of threads
		// otherwise there is a thread which overwrites the variable and init does not reach this oint.
		List<ParallelDataflowgraph<RCFGEdge>> sources = new ArrayList<ParallelDataflowgraph<RCFGEdge>>();
		Map< String, Set<ProgramPoint>> nowriteLocs = computeLocationSets(var, node.getLocations());
		Set<String> procedures =  node.getLocations().keySet();
		for (String proc: procedures){
			Set<ProgramPoint> locations = node.getLocations(proc);
			for (ProgramPoint pp : locations){
				// TODO Reaching Definition
				// statements = RD(x, pp);
				Map<ProgramPoint, DataflowState> singleState = mDataflowAnalysisResult.getLoc2SingleStates();
				mLogger.debug("ProgramPoint " + pp.toString());

				for(Entry<ProgramPoint, DataflowState> entry : singleState.entrySet()){
					mLogger.debug("In Map " + entry.getKey().toString());
					if (entry.getValue() == null){
						mLogger.debug("  NULL");
					}
					else {
						mLogger.debug("  " + entry.getValue().toString());
					}
				}

				// DataflowState dfs = mDataflowAnalysisResult.getLoc2SingleStates().get(pp);
				// Set<CodeBlock> rd = dfs.getReachingDefinitions((IProgramVar) var);
				
				Set<RCFGEdge> rd = new HashSet<RCFGEdge>();
				for (RCFGEdge s: rd){
					mLogger.debug("      by the statement " + s.toString());
					Map< String, Set<ProgramPoint>> loc = new HashMap< String, Set<ProgramPoint>>(nowriteLocs);
					Set<ProgramPoint> srcSet = new HashSet<ProgramPoint>();
					ProgramPoint sourceLoc = (ProgramPoint) s.getSource();
					srcSet.add(sourceLoc);
					loc.put(proc, srcSet);
				}
			}
		}
		
		return sources;
	}
	
	
	private Map< String, Set<ProgramPoint>> computeLocationSets(IProgramVar var, Map< String, Set<ProgramPoint>> locations){
		Map< String, Set<ProgramPoint>> nowriteLocs = new HashMap< String, Set<ProgramPoint>>();
		for (String procedue: locations.keySet()){
			Set<ProgramPoint> L = new HashSet<ProgramPoint>(locations.get(procedue));
			// TODO compute L with nowrites
			Set<ProgramPoint> Lnew = new HashSet<ProgramPoint>();
			nowriteLocs.put(procedue, Lnew);
		}
		return nowriteLocs;
	}
	
	
	
	// Functions for the procedure
	
	
	
	private Set<RCFGNode> nodesInGraph(RCFGNode root){
		// Returns a list of all the nodes in the graph
		// memorize, which elements have been visited
		Set<RCFGNode> visited = new HashSet<RCFGNode>();
		List<RCFGNode> tovisit = new ArrayList<RCFGNode>();
		tovisit.add(root);
		// iterate over tovisit node list
		while(!tovisit.isEmpty()){
			// get the first element and insert in visited
			RCFGNode node = tovisit.get(0);
			visited.add(node);
			tovisit.remove(0);
			// for all outgoing edges of node
			List<RCFGEdge> out1 = node.getOutgoingEdges();
			for(RCFGEdge e: out1){
				// check it target node is already in visited/tovisit
				RCFGNode trgNode = e.getTarget();
				if((!visited.contains(trgNode)) && (!tovisit.contains(trgNode)) ){
					tovisit.add(trgNode);
				}
			}
		}
		return visited;
	}
	
	
	private List<List<RCFGNode>> getEndErrorLocations(List<RCFGNode> nodes){
		// getAsserts and getEndLocations in one function
		// first return: asserts, second return: end locations
		// given a list of nodes, all asserts and errors are returned
		List<RCFGNode> asserts = new ArrayList<RCFGNode>();
		// given a list of nodes, all end locations are returned
		List<RCFGNode> endLocations = new ArrayList<RCFGNode>();
		for(RCFGNode node : nodes){
			// CHeck if the node has outgoing edges and is no Error location
			ProgramPoint pp = (ProgramPoint) node;
			if(pp.isErrorLocation()){
				asserts.add(node);
			}
			if(node.getOutgoingEdges().size() == 0 && !pp.isErrorLocation()){
				endLocations.add(node);
			}
		}
		List<List<RCFGNode>> list = new ArrayList<List<RCFGNode>>();
		list.add(asserts);
		list.add(endLocations);
		return list;
	}
	
	
	
	private List<ParallelDataflowgraph<RCFGEdge>> computeStartLocs(List<RCFGNode> assertLocs, List<RCFGNode> endLocs){
		List<ParallelDataflowgraph<RCFGEdge>> starts = new ArrayList<ParallelDataflowgraph<RCFGEdge>>();
		Map< String, Set<ProgramPoint>> locations = new HashMap< String, Set<ProgramPoint>>();
		// compute all mappings procedure -> set of all end locations
		for (RCFGNode node: endLocs){
			ProgramPoint pp = (ProgramPoint) node;
			// if the procedure is already in the map
			if (locations.containsKey( pp.getProcedure())){
				// add the found end Location to the set in the mapping
				locations.get(pp.getProcedure()).add(pp);
			}
			else if(pp.getProcedure() != "~init"){
				// the init procedure is ignored
				Set<ProgramPoint> loc = new HashSet<ProgramPoint>();
				loc.add(pp);
				locations.put(pp.getProcedure(), loc);
			}
		}
		// compute the start nodes
		for (RCFGNode error: assertLocs){
			ProgramPoint pp = (ProgramPoint) error;
			// assume each error location has exactly one incoming edge
			assert error.getIncomingEdges().size() == 1;
			RCFGEdge stmt = error.getIncomingEdges().get(0);
			Map< String, Set<ProgramPoint>> locMap = new HashMap< String, Set<ProgramPoint>>(locations);
			// construct a set with only the error location
			Set<ProgramPoint> value = new HashSet<ProgramPoint>();
			value.add(pp);
			// overwrite the end location set with the set of the error location
			locMap.put(pp.getProcedure(), value);
			ParallelDataflowgraph<RCFGEdge> newNode = new ParallelDataflowgraph<RCFGEdge>(stmt, locMap);
			starts.add(newNode);
		}
		return starts;
	}
	
	

}
