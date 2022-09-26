package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class PreferenceOrderHeuristic<L extends IIcfgTransition<?>> {
	
	private Deque<IcfgEdge> mBFSWorklist;
	private Set<IcfgEdge> mFinished;
	private IIcfg<?> mIcfg;
	private ArrayList<String> mProcedures;
	private HashMap<String, ArrayList<Deque<IcfgEdge>>> mPathMap;
	
	private enum SearchType {
		MAIN, THREAD, LOOP
	}
	

	public PreferenceOrderHeuristic(final IIcfg<?> icfg){
		this(icfg.getInitialNodes().stream().flatMap(a -> a.getOutgoingEdges().stream()).collect(Collectors.toSet()));
		mIcfg = icfg;
		mProcedures = new ArrayList<>();
		mProcedures.addAll(icfg.getCfgSmtToolkit().getProcedures());
		mProcedures.remove("ULTIMATE.start");
	}
	
	public <T extends IcfgEdge> PreferenceOrderHeuristic(final Collection<T> edges) {
		mBFSWorklist = new ArrayDeque<>();
		mBFSWorklist.addAll(edges);
		mBFSWorklist = new ArrayDeque<>();
		mFinished.addAll(mBFSWorklist);
	}

	private void BFS(IcfgLocation start, SearchType searchType) {
		Deque<IcfgEdge> worklist = new ArrayDeque<>();
		Set<IcfgEdge> outgoingEdges = new HashSet<>();
		//for the Loop-Search, only consider the body, the exit will be considered afterwards
		if (searchType.equals(SearchType.LOOP)) {
			start.getOutgoingEdges().stream()/*.filter(x -> x is the edge into the loop body)*/.filter(mFinished::add).forEachOrdered(outgoingEdges::add);
		} else {
			start.getOutgoingEdges().stream().filter(mFinished::add).forEachOrdered(outgoingEdges::add);
		}
		worklist.addAll(outgoingEdges);
		HashMap<IcfgEdge, IcfgEdge> parentMap = new HashMap<>();
		for (IcfgEdge edge : outgoingEdges) {
			parentMap.put(edge, null);
		}
		String currentProcedure = start.getProcedure();
		while (!worklist.isEmpty()) {
			IcfgEdge current = worklist.removeFirst();
			final IcfgLocation target = current.getTarget();
			if (isGoal(current, searchType)) {
				switch(searchType) {
				case MAIN:
					BFS(target, SearchType.THREAD);
				case THREAD:
					BFS(target, SearchType.LOOP);
				case LOOP:
					//save the path and do the computation at the end
					Deque<IcfgEdge> path = buildPath(parentMap, current);
					ArrayList<Deque<IcfgEdge>> pathList = new ArrayList<>();
					if (mPathMap.get(currentProcedure) != null) {
						pathList = mPathMap.get(currentProcedure);

					}
					pathList.add(path);
					mPathMap.put(currentProcedure, pathList);
					
					BFS(target, SearchType.THREAD);
				default:
					
				}
			} else if (target.getProcedure()==currentProcedure) {
				//continue the search within the current Procedure
				target.getOutgoingEdges().stream().filter(mFinished::add).forEachOrdered(worklist::add);
				for (IcfgEdge edge : target.getOutgoingEdges()) {
					parentMap.put(edge, current);
				}
			}
		}
	}
	
	private boolean isGoal(IcfgEdge current, SearchType searchType) {
		switch(searchType) {
		case MAIN:
			return !current.getSucceedingProcedure().equals(current.getPrecedingProcedure());
		case THREAD:
			return mIcfg.getLoopLocations().contains(current.getTarget());
		case LOOP:
			return mIcfg.getLoopLocations().contains(current.getTarget()) && mFinished.contains(current);
		default:
			return false;
		}
	}

	private Deque<IcfgEdge> buildPath(HashMap<IcfgEdge, IcfgEdge> parentMap, IcfgEdge current) {
		Deque<IcfgEdge> path = new ArrayDeque<>();
		while (current != null) {
			path.addFirst(current);
			current = parentMap.get(current);
		}
		return null;
	}

	
	public void computeParameterizedOrder() {
		//start by searching for the thread's subgraphs, others will be called recursively
		/*maybe we can also do the following end remove SearchType.MAIN
		for (String Procedure : mIcfg.getProcedureEntryNodes().keySet()){
			IcfgLocation initialLocation = mIcfg.getProcedureEntryNodes().get(Procedure);
			BFS(initialLocation, SearchType.THREAD);
		}*/
		IcfgLocation initialNode = mIcfg.getInitialNodes().iterator().next();
		BFS(initialNode, SearchType.MAIN);
		
		//Afterwards, compute the sequence by using the paths in mPathMap
		for (String procedure : mPathMap.keySet()) {
			ArrayList<Deque<IcfgEdge>> pathList = mPathMap.get(procedure);
			//do stuff
		}
	}

	public ParameterizedPreferenceOrder<L, IPredicate> getParameterizedOrder() {
		return null;	
	}
	
	public Set<IProgramVar> getEffectiveGlobalVars(){
		
		return null;
	}


}
