package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Transitionlet;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RCFGAStar.IHeuristic;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
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
		List<Object> moreIncomingEdges = new ArrayList<Object>();
		for (Object i : m_nwa.getStates()){
			int numberOfEdges = 0;
			for (Object o : m_nwa.callPredecessors(i)){
				numberOfEdges++;
			}
			for (Object o : m_nwa.returnPredecessors(i)){
				numberOfEdges++;
			}
			for (Object o : m_nwa.internalPredecessors(i)){
				numberOfEdges++;
			}
			if (numberOfEdges > 1){
				moreIncomingEdges.add(i);
			}
		}
		if (moreIncomingEdges.size() > 0) {
			List<Transitionlet> transitions = new ArrayList<Transitionlet>();
			List<Object> visitedStates = new ArrayList<Object>();
			HashMap<Object, Object> inout = new HashMap();
			Object toPut = null;
			for (Object i : moreIncomingEdges) {
				processState(i, i, transitions, visitedStates);
				if (transitions != null) {
					toPut = i;
					inout.put(transitions.get(0).getLetter(), transitions.get(transitions.size()-1).getLetter());
					mLoopEntryExit.put(ppMap.get(toPut), inout);
				}
			}
		}
		return false;
	}
	
	private List<Transitionlet> processState(Object actualState, Object loopEntryState, List<Transitionlet> path, List<Object> visitedStates)
	{
		if (visitedStates.contains(actualState))
		{
			return null;
		}
		visitedStates.add(actualState);
		for (Object o : m_nwa.internalSuccessors(actualState)) {
			OutgoingInternalTransition intSuccLet = (OutgoingInternalTransition) o;
			path.add((Transitionlet) o);
			Object succ = intSuccLet.getSucc();
			if (succ == loopEntryState) {
				return path;
			} else {
				processState(succ, loopEntryState, path, visitedStates);
			}
		}
		for (Object o : m_nwa.callSuccessors(actualState)) {
			OutgoingCallTransition callSuccLet = (OutgoingCallTransition) o;
			path.add((Transitionlet) o);
			Object succ = callSuccLet.getSucc();
			if (succ == loopEntryState) {
				return path;
			} else {
				processState(succ, loopEntryState, path, visitedStates);
			}
		}
		for (Object o : m_nwa.returnSuccessors(actualState)) {
			OutgoingReturnTransition retSuccLet = (OutgoingReturnTransition) o;
			path.add((Transitionlet) o);
			Object succ = retSuccLet.getSucc();
			if (succ == loopEntryState) {
				return path;
			} else {
				processState(succ, loopEntryState, path, visitedStates);
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

	private void process(ProgramPoint loopHead, HashMap<RCFGEdge, RCFGEdge> map, List<RCFGEdge> forbiddenEdges) {
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
	}

	private RCFGEdge addToResult(List<RCFGEdge> path, HashMap<RCFGEdge, RCFGEdge> map) {
		RCFGEdge first = path.get(0);
		RCFGEdge last = path.get(path.size() - 1);
		assert first.getSource().equals(last.getTarget());
		map.put(first, last);
		return first;
	}

	private IHeuristic getZeroHeuristic() {
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
	}

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
