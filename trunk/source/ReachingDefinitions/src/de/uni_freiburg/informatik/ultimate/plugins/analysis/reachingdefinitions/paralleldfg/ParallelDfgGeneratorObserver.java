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
			mLogger.debug("Exactly one return per Thread");
			}
		else {
			mLogger.debug("More than one return per Thread.");
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
		Set<RCFGEdge> visitedStmts = new HashSet<RCFGEdge>();
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
					mLogger.debug("      by the statement " + s.getNodeLabel().toString());
					Boolean sourceInGraph = false;
					if (visitedStmts.contains(s.getNodeLabel())){
						for (ParallelDataflowgraph<RCFGEdge> n : visited){
							// is it already in the graph?
							if (n.compare(s)){
								// the node is already there
								// the constructed sourceNode s is set to this node.
								// TODO does this work to set s to n?
								s = n;
								sourceInGraph = true;
							}
						}
					}
					if (sourceInGraph == false){
						Q.add(s);
						visited.add(s);
						visitedStmts.add(s.getNodeLabel());
						mLogger.debug("       Added a Node!");
						mNodeCount++;
					}
					// Add an edge
					s.addOutgoingNode(node, x);
					node.addIncomingNode(s);
					mLogger.debug("       Added an Edge!");
					mEdgeCount++;
				}
			}	
		}
	}

	private List<ParallelDataflowgraph<RCFGEdge>> explain(IProgramVar var, ParallelDataflowgraph<RCFGEdge> node){
		// TODO handle the special case init in the Reaching Definition
		// init is only inserted as an edge, if init is in all the Reaching Definitions of threads
		// otherwise there is a thread which overwrites the variable and init does not reach this point.
		// idea: init is not in the RD, but can be determined by nowrites
		// make a special init node a member var of this class and check in 
		List<ParallelDataflowgraph<RCFGEdge>> sources = new ArrayList<ParallelDataflowgraph<RCFGEdge>>();
		Map< String, Set<ProgramPoint>> nowriteLocs = computeLocationSets(var, node.getLocations());
		Boolean initInRD = true;
		for (Entry<String, Set<ProgramPoint>> entry: node.getLocations().entrySet()){
			// check for every Procedure if there exists a pp which has init in nowrtie(x,pp)
			Boolean initInRDProc = false;
			for (ProgramPoint pp : entry.getValue()){
				// get the RD
				DataflowState dfs = mDataflowAnalysisResult.getLoc2SingleStates().get(pp);
				if (pp.toString().contains("ENTRY")){
					// mLogger.debug("Do not compute RD for " + pp.toString());
					continue;
				}
				Set<CodeBlock> rd = dfs.getReachingDefinitions((IProgramVar) var);
				for (RCFGEdge s: rd){
					// mLogger.debug("      by the statement(explain) " + s.toString());
					// construct a new node
					Map< String, Set<ProgramPoint>> loc = new HashMap< String, Set<ProgramPoint>>(nowriteLocs);
					Set<ProgramPoint> srcSet = new HashSet<ProgramPoint>();
					ProgramPoint sourceLoc = (ProgramPoint) s.getSource();
					srcSet.add(sourceLoc);
					loc.put(entry.getKey(), srcSet);
					ParallelDataflowgraph<RCFGEdge> sourceNode = new ParallelDataflowgraph<RCFGEdge>(s, loc);
					sources.add(sourceNode);
				}
				// this pp has init in nowrite(x,pp)
				// if (mInitNode.getLocations(proc) in nowrite(x, pp)){initRDProc=true}
			}
			// if there was no pp which set the varaiable initInRDProc for the procedure to true
			// then init is not a source node
			if(initInRDProc == false){
				initInRD = false;
			}
		}
		if (initInRD){
			// insert init as a sourceNode
			// sources.add(mInit);
		}
		
		return sources;
	}
	
	
	private Map< String, Set<ProgramPoint>> computeLocationSets(IProgramVar var, Map< String, Set<ProgramPoint>> locations){
		Map< String, Set<ProgramPoint>> nowriteLocs = new HashMap< String, Set<ProgramPoint>>();
		for (Entry<String, Set<ProgramPoint>> entry : locations.entrySet()){
			Set<ProgramPoint> L = new HashSet<ProgramPoint>();
			// L always includes the old L set.
			L.addAll(entry.getValue());
			// compute with nowrites
			for (ProgramPoint pp : entry.getValue()){
				if (!pp.toString().contains("ENTRY")){
					DataflowState dfs = mDataflowAnalysisResult.getLoc2SingleStates().get(pp);
					Set<ProgramPoint> nwls = dfs.getNowriteLocations((IProgramVar) var);
					L.addAll(nwls);
				}
				else {
					// mLogger.debug("Do not compute nowrite for "+pp.toString() );
				}
				
			}
			nowriteLocs.put(entry.getKey(), L);
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
			value.add((ProgramPoint) stmt.getSource());
			// overwrite the end location set with the set of the error location
			locMap.put(pp.getProcedure(), value);
			ParallelDataflowgraph<RCFGEdge> newNode = new ParallelDataflowgraph<RCFGEdge>(stmt, locMap);
			starts.add(newNode);
		}
		return starts;
	}
	
	

}
