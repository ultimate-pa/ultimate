package de.uni_freiburg.informatik.ultimate.irsdependencies.loopdetector;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.irsdependencies.Activator;
import de.uni_freiburg.informatik.ultimate.irsdependencies.loopdetector.RCFGAStar.IHeuristic;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * 
 * {@link LoopDetector} computes for each Loophead of an RCFG the edge which is
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
 * @author dietsch
 * 
 */
public class LoopDetector extends BaseObserver {

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;
	private final HashMap<ProgramPoint, HashMap<RCFGEdge, RCFGEdge>> mLoopEntryExit;

	public LoopDetector(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLoopEntryExit = new HashMap<>();
	}

	public HashMap<ProgramPoint, HashMap<RCFGEdge, RCFGEdge>> getResult() {
		return mLoopEntryExit;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (!(root instanceof RootNode)) {
			return true;
		}
		RootNode rootNode = (RootNode) root;
		RootAnnot annot = rootNode.getRootAnnot();

		// get a hashset of all loop heads
		HashSet<ProgramPoint> loopHeadsSet = new HashSet<>(annot.getLoopLocations().keySet());

		// order the loopheads after their occurance in the program
		List<ProgramPoint> loopHeads = orderLoopHeads(loopHeadsSet, rootNode);

		// compute the edges that constitute the loop for one loophead while
		// ignoring loops that result from nesting
		List<RCFGEdge> forbiddenEdges = new ArrayList<>();
		for (ProgramPoint p : loopHeads) {
			HashMap<RCFGEdge, RCFGEdge> map = new HashMap<>();
			mLoopEntryExit.put(p, map);
			process(p, map, forbiddenEdges);
			forbiddenEdges = new ArrayList<>();
			forbiddenEdges.addAll(map.values());
		}
		// print result if debug is enabled
		printResult(mLoopEntryExit);
		return false;
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

}
