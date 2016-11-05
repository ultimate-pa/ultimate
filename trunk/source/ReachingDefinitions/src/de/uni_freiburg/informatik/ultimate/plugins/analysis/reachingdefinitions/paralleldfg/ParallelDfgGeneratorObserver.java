package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.paralleldfg;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.dataflow.DataflowState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class ParallelDfgGeneratorObserver extends BaseObserver {
	
	final private ILogger mLogger;
	final private IUltimateServiceProvider mServices;
	IAbstractInterpretationResult<DataflowState, CodeBlock, IProgramVar, BoogieIcfgLocation> mDataflowAnalysisResult;
	private Integer mEdgeCount;
	private Integer mNodeCount;
	private Integer mCFGEdgeCount;
	private Integer mCFGNodeCount;
	private ParallelDataflowgraph<IcfgEdge> mInitNode;
	private final Map<String, Integer> mStmtsPerThread;
	private final Map<String, Integer> mLocsPerThread;
	
	public ParallelDfgGeneratorObserver(final ILogger logger, final IUltimateServiceProvider services) {
		mLogger = logger;
		mServices = services;
		mDataflowAnalysisResult = null;
		mEdgeCount = 0;
		mNodeCount = 0;
		mCFGEdgeCount = 0;
		mCFGNodeCount = 0;
		mInitNode = null;
		mStmtsPerThread = new HashMap<>();
		mLocsPerThread = new HashMap<>();
	}
	
	@Override
	public boolean process(final IElement root) throws Throwable {
		
		// rootNode is the dummy note with edges leading to every procedure entry point
		final BoogieIcfgContainer rootNode = (BoogieIcfgContainer) root;
		// n = number of threads. Carefull with init procedure
		final int n = BoogieIcfgContainer.extractStartEdges(rootNode).size();
		mDataflowAnalysisResult = obtainDataflowAnalysisResult(rootNode);
		
		computeInitNode(rootNode);
		// look for asserts in the RCFG
		final List<IcfgLocation> nodes = new ArrayList<>();
		// add entry nodes of all procedures to nodes
		for (final Entry<String, BoogieIcfgLocation> entry : rootNode.getEntryNodes().entrySet()) {
			final Set<IcfgLocation> a = nodesInGraph(entry.getValue());
			nodes.addAll(a);
		}
		// compute end and error locations
		final List<List<IcfgLocation>> endError = getEndErrorLocations(nodes);
		final List<IcfgLocation> assertLocs = endError.get(0);
		final List<IcfgLocation> endLocs = endError.get(1);
		
		if (assertLocs.isEmpty()) {
			// no asserts,  nothing to check
			return false;
		}
		// compute Start Locations
		final List<ParallelDataflowgraph<IcfgEdge>> starts = computeStartLocs(assertLocs, endLocs);
		mNodeCount += starts.size();
		
		// Debug info before computation of DFG
		mLogger.debug("The init Node is " + mInitNode.toString());
		mLogger.debug("Number of Threads: " + (n - 1));
		mLogger.debug("Number of Asserts: " + assertLocs.size());
		if (n == endLocs.size()) {
			mLogger.debug("Exactly one return per Thread");
		} else {
			mLogger.debug("More than one return per Thread.");
		}
		mLogger.debug("Number of start nodes: " + starts.size());
		mLogger.debug("Start node(s):  ");
		for (final ParallelDataflowgraph<IcfgEdge> s : starts) {
			mLogger.debug("  " + s.toString());
		}
		
		// Algorithm with the start Locations
		collectDFGEdges(starts);
		
		// Debug info after the algorithm
		
		mLogger.debug("Information of the orignial CFG of the program: ");
		mLogger.debug("Total number of control flow nodes: " + mCFGNodeCount);
		mLogger.debug("Total number of control flowe edges: " + mCFGEdgeCount);
		mLogger.debug("Maximal number of nodes in the Parallel DFG: " + computeMaxNodes());
		
		mLogger.debug("Information of the Parallel DFG:");
		mLogger.debug("Total number of data flow nodes: " + mNodeCount);
		mLogger.debug("Total number of data flow edges: " + mEdgeCount);
		return false;
	}
	
	private IAbstractInterpretationResult<DataflowState, CodeBlock, IProgramVar, BoogieIcfgLocation>
			obtainDataflowAnalysisResult(final BoogieIcfgContainer r) {
		final List<CodeBlock> edges = new ArrayList<>();
		r.getEntryNodes();
		for (final Entry<String, BoogieIcfgLocation> en : r.getEntryNodes().entrySet()) {
			edges.add((CodeBlock) en.getValue().getOutgoingEdges().get(0));
		}
		
		final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		return AbstractInterpreter.runFuture(r, edges, timer, mServices, false);
	}
	
	// Algorithm
	private void collectDFGEdges(final List<ParallelDataflowgraph<IcfgEdge>> starts) {
		// compute the edges
		final List<ParallelDataflowgraph<IcfgEdge>> Q = starts;
		final Set<ParallelDataflowgraph<IcfgEdge>> visited = new HashSet<>();
		final Set<IcfgEdge> visitedStmts = new HashSet<>();
		while (!Q.isEmpty()) {
			final ParallelDataflowgraph<IcfgEdge> node = Q.get(0);
			Q.remove(0);
			// get the use of the Reaching Definition
			final CodeBlock cb = (CodeBlock) node.getNodeLabel();
			// better would be .entrySet();
			final Set<IProgramVar> use = cb.getTransitionFormula().getInVars().keySet();
			mLogger.debug("Explain " + use.size() + " variable(s) for the statement " + cb.toString());
			for (final IProgramVar x : use) {
				mLogger.debug("   explain the variable " + x.toString());
				final List<ParallelDataflowgraph<IcfgEdge>> sources = explain(x, node);
				for (ParallelDataflowgraph<IcfgEdge> s : sources) {
					mLogger.debug("      by the statement " + s.getNodeLabel().toString());
					Boolean sourceInGraph = false;
					if (mInitNode.compare(s)) {
						// s is the init node
						sourceInGraph = true;
					} else if (visitedStmts.contains(s.getNodeLabel())) {
						for (final ParallelDataflowgraph<IcfgEdge> n : visited) {
							// is it already in the graph?
							if (n.compare(s)) {
								// the node is already there
								// the constructed sourceNode s is set to this node.
								// TODO does this work to set s to n?
								s = n;
								sourceInGraph = true;
							}
						}
					}
					if (!sourceInGraph) {
						Q.add(s);
						visited.add(s);
						visitedStmts.add(s.getNodeLabel());
						mLogger.debug("       Added a node " + s.toString());
						mNodeCount++;
					}
					// Add an edge
					s.addOutgoingNode(node, x);
					node.addIncomingNode(s);
					mLogger.debug("       Added an edge " + node.toString() + "->" + x + " " + s.toString());
					mEdgeCount++;
				}
			}
		}
	}
	
	private List<ParallelDataflowgraph<IcfgEdge>> explain(final IProgramVar var,
			final ParallelDataflowgraph<IcfgEdge> node) {
		// TODO handle the special case init in the Reaching Definition
		// init is only inserted as an edge, if init is in all the Reaching Definitions of threads
		// otherwise there is a thread which overwrites the variable and init does not reach this point.
		// idea: init is not in the RD, but can be determined by nowrites
		// make a special init node a member var of this class and check in
		final List<ParallelDataflowgraph<IcfgEdge>> sources = new ArrayList<>();
		final Map<String, Set<BoogieIcfgLocation>> nowriteLocs = computeLocationSets(var, node.getLocations());
		Boolean initInRD = true;
		for (final Entry<String, Set<BoogieIcfgLocation>> entry : node.getLocations().entrySet()) {
			// check for every Procedure if there exists a pp which has init in nowrtie(x,pp)
			Boolean initInRDProc = false;
			if (!var.isGlobal() && var.getProcedure() != entry.getKey()) {
				// if var is local and not in the procedure, continue to the next procedure
				continue;
			}
			for (final BoogieIcfgLocation pp : entry.getValue()) {
				// get the RD
				final DataflowState dfs = mDataflowAnalysisResult.getLoc2SingleStates().get(pp);
				if (pp.toString().contains("ENTRY")) {
					initInRDProc = true;
					continue;
				}
				
				// this pp has init in nowrite(x,pp)
				final Set<BoogieIcfgLocation> nwls = dfs.getNowriteLocations(var);
				final Set<BoogieIcfgLocation> entryPoint = mInitNode.getLocations(entry.getKey());
				BoogieIcfgLocation en = null;
				for (final BoogieIcfgLocation e : entryPoint) {
					en = e;
				}
				if (nwls.contains(en)) {
					initInRDProc = true;
				}
				
				// Reaching Definition
				final Set<CodeBlock> rd = dfs.getReachingDefinitions(var);
				for (final IcfgEdge s : rd) {
					// mLogger.debug("      by the statement(explain) " + s.toString());
					// construct a new node
					final Map<String, Set<BoogieIcfgLocation>> loc = new HashMap<>(nowriteLocs);
					final Set<BoogieIcfgLocation> srcSet = new HashSet<>();
					final BoogieIcfgLocation sourceLoc = (BoogieIcfgLocation) s.getSource();
					srcSet.add(sourceLoc);
					loc.put(entry.getKey(), srcSet);
					final ParallelDataflowgraph<IcfgEdge> sourceNode = new ParallelDataflowgraph<>(s, loc);
					sources.add(sourceNode);
				}
			}
			// if there was no pp which set the variable initInRDProc for the procedure to true
			// then init is not a source node
			if (initInRDProc.equals(false)) {
				initInRD = false;
			}
		}
		if (initInRD) {
			// insert init as a sourceNode
			sources.add(mInitNode);
		}
		
		return sources;
	}
	
	private Map<String, Set<BoogieIcfgLocation>> computeLocationSets(final IProgramVar var,
			final Map<String, Set<BoogieIcfgLocation>> locations) {
		final Map<String, Set<BoogieIcfgLocation>> nowriteLocs = new HashMap<>();
		for (final Entry<String, Set<BoogieIcfgLocation>> entry : locations.entrySet()) {
			final Set<BoogieIcfgLocation> L = new HashSet<>();
			// L always includes the old L set.
			L.addAll(entry.getValue());
			// compute with nowrites
			if (!var.isGlobal() && var.getProcedure() != entry.getKey()) {
				// if var is local and not in the procedure, continue to the next procedure
				continue;
			}
			for (final BoogieIcfgLocation pp : entry.getValue()) {
				if (!pp.toString().contains("ENTRY")) {
					final DataflowState dfs = mDataflowAnalysisResult.getLoc2SingleStates().get(pp);
					final Set<BoogieIcfgLocation> nwls = dfs.getNowriteLocations(var);
					L.addAll(nwls);
				} else {
					// mLogger.debug("Do not compute nowrite for "+pp.toString() );
				}
				
			}
			nowriteLocs.put(entry.getKey(), L);
		}
		return nowriteLocs;
	}
	
	// Functions for the procedure
	
	private Set<IcfgLocation> nodesInGraph(final IcfgLocation root) {
		// Called for every Thread, where root is the entry point of the thread.
		// Returns a list of all the nodes in the graph
		// memorize, which elements have been visited
		Integer countEdges = 0;
		final Set<IcfgLocation> visited = new HashSet<>();
		final List<IcfgLocation> tovisit = new ArrayList<>();
		tovisit.add(root);
		// iterate over tovisit node list
		while (!tovisit.isEmpty()) {
			// get the first element and insert in visited
			final IcfgLocation node = tovisit.get(0);
			visited.add(node);
			tovisit.remove(0);
			// for all outgoing edges of node
			final List<IcfgEdge> out1 = node.getOutgoingEdges();
			for (final IcfgEdge e : out1) {
				countEdges++;
				// check it target node is already in visited/tovisit
				final IcfgLocation trgNode = e.getTarget();
				if ((!visited.contains(trgNode)) && (!tovisit.contains(trgNode))) {
					tovisit.add(trgNode);
				}
			}
		}
		mCFGEdgeCount += countEdges;
		mCFGNodeCount += visited.size();
		final BoogieIcfgLocation pp = (BoogieIcfgLocation) root;
		mStmtsPerThread.put(pp.getProcedure(), visited.size());
		mLocsPerThread.put(pp.getProcedure(), countEdges);
		return visited;
	}
	
	private static List<List<IcfgLocation>> getEndErrorLocations(final List<IcfgLocation> nodes) {
		// getAsserts and getEndLocations in one function
		// first return: asserts, second return: end locations
		// given a list of nodes, all asserts and errors are returned
		final List<IcfgLocation> asserts = new ArrayList<>();
		// given a list of nodes, all end locations are returned
		final List<IcfgLocation> endLocations = new ArrayList<>();
		for (final IcfgLocation node : nodes) {
			// CHeck if the node has outgoing edges and is no Error location
			final BoogieIcfgLocation pp = (BoogieIcfgLocation) node;
			if (pp.isErrorLocation()) {
				asserts.add(node);
			}
			if (node.getOutgoingEdges().size() == 0 && !pp.isErrorLocation()) {
				endLocations.add(node);
			}
		}
		final List<List<IcfgLocation>> list = new ArrayList<>();
		list.add(asserts);
		list.add(endLocations);
		return list;
	}
	
	private static List<ParallelDataflowgraph<IcfgEdge>> computeStartLocs(final List<IcfgLocation> assertLocs,
			final List<IcfgLocation> endLocs) {
		final List<ParallelDataflowgraph<IcfgEdge>> starts = new ArrayList<>();
		final Map<String, Set<BoogieIcfgLocation>> locations = new HashMap<>();
		// compute all mappings procedure -> set of all end locations
		for (final IcfgLocation node : endLocs) {
			final BoogieIcfgLocation pp = (BoogieIcfgLocation) node;
			// if the procedure is already in the map
			if (locations.containsKey(pp.getProcedure())) {
				// add the found end Location to the set in the mapping
				locations.get(pp.getProcedure()).add(pp);
			} else if (pp.getProcedure() != "~init") {
				// the init procedure is ignored
				final Set<BoogieIcfgLocation> loc = new HashSet<>();
				loc.add(pp);
				locations.put(pp.getProcedure(), loc);
			}
		}
		// compute the start nodes
		for (final IcfgLocation error : assertLocs) {
			final BoogieIcfgLocation pp = (BoogieIcfgLocation) error;
			// assume each error location has exactly one incoming edge
			assert error.getIncomingEdges().size() == 1;
			final IcfgEdge stmt = error.getIncomingEdges().get(0);
			final Map<String, Set<BoogieIcfgLocation>> locMap = new HashMap<>(locations);
			// construct a set with only the error location
			final Set<BoogieIcfgLocation> value = new HashSet<>();
			value.add((BoogieIcfgLocation) stmt.getSource());
			// overwrite the end location set with the set of the error location
			locMap.put(pp.getProcedure(), value);
			final ParallelDataflowgraph<IcfgEdge> newNode = new ParallelDataflowgraph<>(stmt, locMap);
			starts.add(newNode);
		}
		return starts;
	}
	
	private void computeInitNode(final BoogieIcfgContainer r) {
		final Map<String, Set<BoogieIcfgLocation>> locations = new HashMap<>();
		IcfgEdge stmt = null;
		for (final Entry<String, BoogieIcfgLocation> entry : r.getEntryNodes().entrySet()) {
			final IcfgLocation s = entry.getValue();
			final BoogieIcfgLocation pp = (BoogieIcfgLocation) s;
			if (pp.getProcedure() == "~init") {
				// walk to the last statement?
				stmt = s.getOutgoingEdges().get(0);
				while (!stmt.getTarget().getOutgoingEdges().isEmpty()) {
					stmt = stmt.getTarget().getOutgoingEdges().get(0);
				}
			} else {
				final Set<BoogieIcfgLocation> set = new HashSet<>();
				set.add(pp);
				locations.put(pp.getProcedure(), set);
			}
		}
		mInitNode = new ParallelDataflowgraph<>(stmt, locations);
		mNodeCount++;
	}
	
	private Integer computeMaxNodes() {
		Integer count = 0;
		for (final Entry<String, Integer> entry : mStmtsPerThread.entrySet()) {
			if (entry.getKey() == "~init") {
				continue;
			}
			for (final Entry<String, Integer> other : mLocsPerThread.entrySet()) {
				if (entry.getKey() != other.getKey() && other.getKey() != "~init") {
					count += entry.getValue() * other.getValue();
				}
			}
		}
		return count;
	}
}
