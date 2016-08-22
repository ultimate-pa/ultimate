package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.paralleldfg;

import java.util.ArrayList;
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

	public ParallelDfgGeneratorObserver(ILogger logger, IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
	}


	@Override
	public boolean process(IElement root) throws Throwable {
		
		// rootNode is the dummy note with edges leading to every procedure entry point
		RootNode rootNode = (RootNode) root;
		// n = number of threads. Carefull with init procedure
		int n = rootNode.getOutgoingEdges().size();
		mLogger.debug("Number of Threads: " + (n-1));
		
		IAbstractInterpretationResult<DataflowState, CodeBlock, IProgramVar, ProgramPoint> dataflowAnalysisResult = 
				obtainDataflowAnalysisResult(rootNode);
		
		
		// the result aiRes can be queried for each state as follows
		// (replace null by a ProgramPoint)
		DataflowState dfs = dataflowAnalysisResult.getLoc2State().get(null);
		// query the state at each ProgramPoint for the dataflow results as follows 
		// (replace null by a real variable)
		Set<ProgramPoint> nwls = dfs.getNowriteLocations((IProgramVar) null);
		Set<CodeBlock> rd = dfs.getReachingDefinitions((IProgramVar) null);
		
		
		
		// look for asserts in the RCFG
		List<RCFGNode> nodes = new ArrayList<RCFGNode>();
		for (RCFGEdge e: rootNode.getOutgoingEdges()){
			List<RCFGNode> a = nodesInGraph(e.getTarget());
			nodes.addAll(a);
		}
		
		// function that computes both error locations and then end locations
		List<List<RCFGNode>> endError = getEndErrorLocations(nodes);
		List<RCFGNode> assertLocs = endError.get(0);
		List<RCFGNode> endLocs = endError.get(1);
		mLogger.debug("Number of Asserts: " + assertLocs.size());
		if (n == endLocs.size()){mLogger.debug("More than one return per Thread: False");}
		else{mLogger.debug("More than one return per Thread: True");}
		
		if (assertLocs.size() == 0){
			// no asserts,  nothing to check
			return false;
		}
		
		// compute the List of starting nodes for the parallel DFG
		List<ParallelDataflowgraph<RCFGEdge>> starts = new ArrayList<ParallelDataflowgraph<RCFGEdge>>();
		for (RCFGNode error: assertLocs){
			// for every error location in the found asserts
			// compute the locations for the node
			List<ProgramPoint> locs = computeLocVector(error, endLocs);
			// assume each error location has exactly one incoming edge
			assert error.getIncomingEdges().size() == 1;
			RCFGEdge stmt = error.getIncomingEdges().get(0);
			ParallelDataflowgraph<RCFGEdge> newNode = new ParallelDataflowgraph<RCFGEdge>(stmt, locs);
			starts.add(newNode);
		}
		
		collectDFGEdges(starts);
		
		
		
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
		List<ParallelDataflowgraph<RCFGEdge>> Q = starts;
		Set<ParallelDataflowgraph<RCFGEdge>> visited = new HashSet<ParallelDataflowgraph<RCFGEdge>>();
		while(!Q.isEmpty()){
			ParallelDataflowgraph<RCFGEdge> node = Q.get(0);
			Q.remove(0);
			
			IAnnotations annot = node.getNodeLabel().getPayload().getAnnotations().get("ReachingDefinition Default");
			// get the use!
			List<ScopedBoogieVar> use = new ArrayList<ScopedBoogieVar>();
			
			for (ScopedBoogieVar x: use){
				List<ParallelDataflowgraph<RCFGEdge>> sources = explain(x, node);
				for (ParallelDataflowgraph<RCFGEdge> s : sources){
					if (!visited.contains(s)){
						Q.add(s);
						visited.add(s);
					}
					// Add an edge
					s.addOutgoingNode(node, x);
					node.addIncomingNode(s);
				}
			}
			
			
			
			mLogger.debug("Annotation " + annot.toString());
			
		}

	}

	private List<ParallelDataflowgraph<RCFGEdge>> explain(ScopedBoogieVar x, ParallelDataflowgraph<RCFGEdge> node){
		List<ParallelDataflowgraph<RCFGEdge>> sources = new ArrayList<ParallelDataflowgraph<RCFGEdge>>();
		for (ProgramPoint loc: node.getLocations()){
			ProgramPoint pp = (ProgramPoint) node.getNodeLabel().getSource();
			if (loc.getProcedure() == pp.getProcedure()){
				// old Reaching Definition
				
			}
			else {
				// new Reaching Definition
				
			}
			// special case init?
			
		}
		return sources;
	}
	
	private List<ProgramPoint> insertLocation(List<ProgramPoint> locations, ProgramPoint loc){
		// can be optimized!
		// for the case that there are several returns in the thread of loc
		for (ProgramPoint l: locations){
			if (l.getProcedure() == loc.getProcedure()){
				locations.remove(l);
			}
		}
		locations.add(loc);
		return locations;
	}
	
	
	// Functions for the procedure
	
	private List<RCFGNode> nodesInGraph(RCFGNode root){
		// Returns a list of all the nodes in the graph
		// memorize, which elements have been visited
		List<RCFGNode> visited = new ArrayList<RCFGNode>();
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
		// Function getAsserts and getEndLocations in one
		// given a list of nodes, all asserts are returned
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
	
	private List<RCFGNode> getAsserts(List<RCFGNode> nodes){
		// given a list of nodes, all asserts are returned
		List<RCFGNode> asserts = new ArrayList<RCFGNode>();
		for(RCFGNode node : nodes){
			// Check if the node is an Assert Violation = error location
			ProgramPoint pp = (ProgramPoint) node;
			if(pp.isErrorLocation()){
				asserts.add(node);
			}
		}
		return asserts;
	}

	private List<RCFGNode> getEndLocations(List<RCFGNode> nodes){
		// given a list of nodes, all end locations are returned
		List<RCFGNode> endLocations = new ArrayList<RCFGNode>();
		for(RCFGNode node : nodes){
			// CHeck if the node has outgoing edges and is no Error location
			ProgramPoint pp = (ProgramPoint) node;
			if(node.getOutgoingEdges().size() == 0 && !pp.isErrorLocation()){
				endLocations.add(node);
			}
		}
		return endLocations;
	}
	
	
	
	private List<ProgramPoint> computeLocVector(RCFGNode errorLoc, List<RCFGNode> endLoc){
		// given an vector of endLocations return the set of locations
		// necessary for the initialization of the node of the Parallel DFG
		// convert to ProgramPoints
		List<ProgramPoint> points = new ArrayList<ProgramPoint>();
		ProgramPoint  errorPoint= (ProgramPoint) errorLoc;
		points.add(errorPoint);
		
		for (RCFGNode node : endLoc){
			ProgramPoint pp = (ProgramPoint) node;
			if (pp.getProcedure() != "~init"){
				// ignore init procedure
				if (pp.getProcedure() != errorPoint.getProcedure()){
					// all other procedures take their end location.
					points.add(pp);
				}
			}
		}
		return points;
	}
	
	
	
	

}
