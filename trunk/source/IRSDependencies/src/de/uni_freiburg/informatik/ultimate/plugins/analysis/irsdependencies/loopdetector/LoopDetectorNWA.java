package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Transitionlet;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * 
 * {@link LoopDetectorNWA} computes for each Loophead of an RCFG the edge which is
 * used to enter the loop body and the corresponding edge that leads back to the
 * loop head.
 * 
 * If your graph looks like this and L1 and L2 are loop heads,
 * 
 * <pre>
 * 		 e1              e4 
 * 		+--+            +--+
 * 		\  v     e2     \  v
 * 		 L1  --------->  L2 
 * 		     <---------     
 * 		         e3
 * </pre>
 * 
 * you will get the following map:<br>
 * L1 -> (e2 -> e3, e1 -> e1)<br>
 * L2 -> (e4 -> e4) <br>
 * <br>
 * 
 * You should call {@link #process(IElement)} on the root element of your RCFG
 * and then get the resulting map via {@link #getResult()}.
 * 
 * @author schillif@informatik.uni-freiburg.de
 * 
 */
public class LoopDetectorNWA extends BaseObserver {

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;
	//                                          RCFGEdge, RCFGEdge
	private final HashMap<ProgramPoint, HashMap<Object, Object>> mLoopEntryExit;
	
	INestedWordAutomaton m_nwa;
	int m_maxLength;
	Map<Object, List> m_incomingEdgesMap = new HashMap<Object, List>();

	public LoopDetectorNWA(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLoopEntryExit = new HashMap<>();
	}

	//public HashMap<ProgramPoint, HashMap<RCFGEdge, RCFGEdge>> getResult() {
	public HashMap<ProgramPoint, HashMap<Object, Object>> getResult() {
		return mLoopEntryExit;
	}

	public boolean process(INestedWordAutomaton nwa, Map<Object, ProgramPoint> ppMap) throws Throwable {
		m_nwa = nwa;
		m_maxLength = nwa.getStates().size();
		List<Object> possibleLoopHeads = new ArrayList<Object>();
		
		//check which States could be loophead (the have to have more than one incoming edge)
		for (Object state : m_nwa.getStates()){
			LinkedList<Object> incomingEdges = new LinkedList<Object>();
			int edges = 0;
			for (Object c : m_nwa.callPredecessors(state)){
				incomingEdges.add(c);
				edges++;
			}
			for (Object r : m_nwa.returnPredecessors(state)){
				incomingEdges.add(r);
				edges++;
			}
			for (Object i : m_nwa.internalPredecessors(state)){
				incomingEdges.add(i);
				edges++;
			}
			m_incomingEdgesMap.put(state, incomingEdges);
			if (edges > 1){
				possibleLoopHeads.add(state);
			}
		}
		if (possibleLoopHeads.size() > 0) {
			HashMap<Object, Object> inout = new HashMap();
			for (Object p : possibleLoopHeads) {
				List<Transitionlet> transitions = new LinkedList<Transitionlet>();
				List<Object> visitedStates = new LinkedList<Object>();
				List<Transitionlet> result = processState(p, p, transitions, visitedStates);
				if ((result != null) && (!result.isEmpty())) {
					inout.put(transitions.get(0).getLetter(), transitions.get(transitions.size()-1).getLetter());
					mLoopEntryExit.put(ppMap.get(p), inout);
				}
			}
		}
		return false;
	}
	
	private List<Transitionlet> processState(Object actualState, Object loopEntryState, List<Transitionlet> path, List<Object> visitedStates)
	{
		List<Transitionlet> emptyPath = new LinkedList<Transitionlet>();
		
		if ((visitedStates.contains(actualState)) || (path.size() > m_maxLength)) {
			return emptyPath;
		}
		if (actualState != loopEntryState) {
			visitedStates.add(actualState);
		}
		for (Object pred : m_incomingEdgesMap.get(actualState)) {
			if (pred instanceof IncomingInternalTransition) {
				IncomingInternalTransition p = (IncomingInternalTransition) pred;
				Object pre = p.getPred();
				if (pre == loopEntryState) {
					return path;
				} else if (visitedStates.contains(pre)) {
					return emptyPath;
				}
				path.add(p);
				path = processState(pre, loopEntryState, path, visitedStates);
			} else if (pred instanceof IncomingCallTransition) {
				IncomingCallTransition p = (IncomingCallTransition) pred;
				Object pre = p.getPred();
				if (pre == loopEntryState) {
					return path;
				} else if (visitedStates.contains(pre)) {
					return emptyPath;
				}
				path.add(p);
				path = processState(pre, loopEntryState, path, visitedStates);
			} else if (pred instanceof IncomingReturnTransition) {
				IncomingReturnTransition p = (IncomingReturnTransition) pred;
				Object pre = p.getHierPred();
				if (pre == loopEntryState) {
					return path;
				} else if (visitedStates.contains(pre)) {
					return emptyPath;
				}
				path.add(p);
				path = processState(pre, loopEntryState, path, visitedStates);
			} else {
				return emptyPath;
			}
		}
		return path;
	}

	private List<ProgramPoint> orderLoopHeads(HashSet<ProgramPoint> loopHeads, RootNode programStart) {
		List<ProgramPoint> rtr = new ArrayList<>();

		Stack<RCFGNode> open = new Stack<>();
		HashSet<RCFGNode> closed = new HashSet<>();

		open.push(programStart);
		while (!open.isEmpty()) {
			RCFGNode current = open.pop();
			if (closed.contains(current)) {
				continue;
			}
			closed.add(current);
			for (RCFGEdge edge : current.getOutgoingEdges()) {
				open.push(edge.getTarget());
			}
			if (loopHeads.contains(current)) {
				rtr.add((ProgramPoint) current);
			}
		}

		return rtr;
	}

	/*private void process(ProgramPoint loopHead, HashMap<RCFGEdge, RCFGEdge> map, List<RCFGEdge> forbiddenEdges) {
		RCFGAStar walker = new RCFGAStar(mLogger, loopHead, loopHead, getZeroHeuristic(), forbiddenEdges);

		List<RCFGEdge> path = walker.findPath();
		if (path == null || path.isEmpty()) {
			// throw new RuntimeException();
		}

		// got first path, add it to the results and get the edge starting this
		// path to find different entry/exits for this loop
		while (path != null) {
			RCFGEdge forbiddenEdge = addToResult(path, map);
			forbiddenEdges.add(forbiddenEdge);
			walker = new RCFGAStar(mLogger, loopHead, loopHead, getZeroHeuristic(), forbiddenEdges);
			path = walker.findPath();

		}
	}*/

	private RCFGEdge addToResult(List<RCFGEdge> path, HashMap<RCFGEdge, RCFGEdge> map) {
		RCFGEdge first = path.get(0);
		RCFGEdge last = path.get(path.size() - 1);
		assert first.getSource().equals(last.getTarget());
		map.put(first, last);
		return first;
	}

	/*private IHeuristic getZeroHeuristic() {
		return new IHeuristic() {

			@Override
			public int getHeuristicValue(RCFGNode from, RCFGNode to) {
				return 0;
			}

			@Override
			public int getConcreteCost(RCFGEdge e) {
				return 1;
			}
		};
	}*/

	private void printResult(HashMap<ProgramPoint, HashMap<RCFGEdge, RCFGEdge>> result) {
		if (!mLogger.isDebugEnabled()) {
			return;
		}
		mLogger.debug("---------------");
		for (ProgramPoint p : result.keySet()) {
			mLogger.debug("Loophead " + p);
			HashMap<RCFGEdge, RCFGEdge> map = result.get(p);
			for (Entry<RCFGEdge, RCFGEdge> entry : map.entrySet()) {
				mLogger.debug("* " + entry.getKey().hashCode() + " >< " + entry.getValue().hashCode());
			}
		}
		mLogger.debug("---------------");
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		// TODO Auto-generated method stub
		return false;
	}

}
