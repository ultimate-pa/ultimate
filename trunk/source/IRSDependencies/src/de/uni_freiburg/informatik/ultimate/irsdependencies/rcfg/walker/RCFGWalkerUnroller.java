package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Stack;

import org.apache.log4j.Level;

import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.annotations.IRSDependenciesAnnotation;
import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.annotations.RCFGUnrollWalkerAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class RCFGWalkerUnroller extends RCFGWalker {

	protected final String sMainProcedureName = "main";
	protected int mUnrollings;
	protected HashMap<RCFGEdge, ARTEdge> mGraph;
	protected List<List<ARTEdge>> mPaths;
	protected Stack<RCFGEdge> mCalls;
	protected Stack<RCFGEdge> mNestedLoops;
	protected Stack<HashMap<RCFGEdge, ARTEdge>> mGraphs;

	protected List<List<RCFGEdge>> mFinalPaths;

	protected List<RCFGEdge> mCurrentPath;

	public RCFGWalkerUnroller(ObserverDispatcher dispatcher, int unrollings) {
		super(dispatcher);
		mUnrollings = unrollings;
		sLogger.setLevel(Level.INFO);
	}

	@Override
	public void processProgram(RootNode node) {
		init();
		RCFGEdge start = searchMainEdge(node);
		if (start == null) {
			sLogger.error("No main procedure found");
			return;
		}
		process(start, new ArrayList<ARTEdge>());
		finish();
	}

	public List<List<RCFGEdge>> getPaths() {
		return mFinalPaths;
	}

	public List<RCFGEdge> getCurrentPrefix() {
		return mCurrentPath;
	}

	protected void init() {
		mFinalPaths = null;
		mGraph = new HashMap<>();
		mPaths = new ArrayList<>();
		mCalls = new Stack<>();
		mNestedLoops = new Stack<>();
		mGraphs = new Stack<>();
		mCurrentPath = new ArrayList<>();
	}

	protected void finish() {
		mFinalPaths = new ArrayList<>();

		for (List<ARTEdge> path : mPaths) {
			List<RCFGEdge> newPath = new ArrayList<>();
			for (ARTEdge edge : path) {
				newPath.add(edge.mBacking);
			}
			mFinalPaths.add(newPath);
		}
		sLogger.info("Processed "+mFinalPaths.size()+" traces");

		mGraph = null;
		mPaths = null;
		mCalls = null;
		mGraphs = null;
		mNestedLoops = null;
		mCurrentPath = null;
	}

	protected void printPath(List<ARTEdge> path) {
		sLogger.debug(path.get(0).getSource());
		for (ARTEdge e : path) {
			sLogger.debug(e.mBacking);
			sLogger.debug(e.getTarget());
		}
	}

	protected RCFGEdge searchMainEdge(final RootNode node) {
		sLogger.debug("Searching for procedure \"" + sMainProcedureName + "\"");
		for (RCFGEdge edge : node.getOutgoingEdges()) {
			ProgramPoint possibleMain = (ProgramPoint) edge.getTarget();
			sLogger.debug("Candidate: \"" + possibleMain.getProcedure() + "\"");
			if (possibleMain.getProcedure()
					.equalsIgnoreCase(sMainProcedureName)) {
				sLogger.debug("Found match");
				return edge;
			}
		}
		return null;
	}

	public void process(RCFGEdge currentEdge, List<ARTEdge> processed) {
		ARTEdge current = createEdge(currentEdge);
		if (current.getAnnotation() == null) {
			findLoopEntryExit(currentEdge.getTarget());
		}

		sLogger.debug("processing: " + current);

		if (current.isVisited(mUnrollings)) {
			sLogger.debug("--reached unrolling limit");
			sLogger.debug("");
			return;
		} else {
			current.visit();
		}

		if (currentEdge instanceof Call) {
			mCalls.push(currentEdge);
			sLogger.debug("--push (call) " + currentEdge);
			sLogger.debug("----old mGraph: " + mGraph.values());
			sLogger.debug("----new mGraph: fresh");

			mGraphs.push(mGraph);
			mGraph = new HashMap<>();

			if (isMaxCallDepth(currentEdge)) {
				sLogger.debug("--reached unrolling limit (call)");
				sLogger.debug("");
				return;
			}
		} else if (currentEdge instanceof Return) {
			mCalls.pop();
			String old = mGraph.values().toString();
			mGraph = mGraphs.pop();
			current.mLastGraphState = mGraph;
			sLogger.debug("--pop (return) " + currentEdge);
			sLogger.debug("----old mGraph: " + old);
			sLogger.debug("----new mGraph: " + mGraph.values());
		}

		if (current.isNestedLoopEntry()) {
			sLogger.debug("--push (nestedLoop) " + currentEdge);
			mNestedLoops.push(currentEdge);
			if (isMaxLoopDepth(current)) {
				sLogger.debug("--reached unrolling limit (nestedLoop)");
				sLogger.debug("----mNestedLoops: " + mNestedLoops);
				mNestedLoops.pop();
				sLogger.debug("----pop mNestedLoops: " + mNestedLoops);
				sLogger.debug("");
				return;
			}
			sLogger.debug("----old mGraph: " + mGraph.values());
			sLogger.debug("----new mGraph: fresh");
			mGraphs.push(mGraph);
			mGraph = new HashMap<>();

		} else if (current.isNestedLoopExit()) {
			mNestedLoops.push(currentEdge);
			String old = mGraph.values().toString();
			mGraph = mGraphs.pop();
			current.mLastGraphState = mGraph;
			sLogger.debug("--push (nestedLoop) " + currentEdge);
			sLogger.debug("----old mGraph: " + old);
			sLogger.debug("----new mGraph: " + mGraph.values());
		}

		processed.add(current);
		mCurrentPath.add(current.mBacking);
		pre(current.mBacking);
		pre(current.mBacking.getTarget());

		if (current.getTarget().getOutgoingEdges().isEmpty()) {
			mPaths.add(new ArrayList<>(processed));
			sLogger.debug("");
			sLogger.debug("Trace: " + traceToString(processed));
			sLogger.debug("mCalls: " + mCalls);
			sLogger.debug("mNestedLoops: " + mNestedLoops);
			sLogger.debug("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@ End @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@");
			sLogger.debug("");
			programExitReached();
			return;
		}

		for (RCFGEdge next : current.getTarget().getOutgoingEdges()) {
			if (isFeasible(next)) {
				process(next, processed);
				post(current.mBacking);
				post(current.mBacking.getTarget());

			} else {
				sLogger.debug("--infeasible: " + next);
			}
		}
		backtrack(current, processed);
	}

	protected void backtrack(ARTEdge stop, List<ARTEdge> processed) {
		sLogger.debug("--backtracking--");
		for (int i = processed.size() - 1; i >= 0; --i) {
			ARTEdge current = processed.get(i);
			sLogger.debug("----remove from trace prefix: " + current);
			processed.remove(i);
			mCurrentPath.remove(i);

			if (current.isNestedLoopExit()) {
				mNestedLoops.pop();
				mGraphs.push(mGraph);
				String old = mGraph.values().toString();
				mGraph = current.mLastGraphState;
				sLogger.debug("----pop (nestedLoopExit) " + current.mBacking);
				sLogger.debug("------old mGraph: " + old);
				sLogger.debug("------new mGraph: " + mGraph.values());
			} else if (current.isNestedLoopEntry()) {
				mNestedLoops.pop();
				String old = mGraph.values().toString();
				mGraph = mGraphs.pop();
				sLogger.debug("----pop (nestedLoopEntry) " + current.mBacking);
				sLogger.debug("------old mGraph: " + old);
				sLogger.debug("------new mGraph: " + mGraph.values());
			}

			if (current.mBacking instanceof Return) {
				mCalls.push(((Return) current.mBacking)
						.getCorrespondingCall());
				mGraphs.push(mGraph);
				String old = mGraph.values().toString();
				mGraph = current.mLastGraphState;
				sLogger.debug("----push (return) " + current.mBacking);
				sLogger.debug("------old mGraph: " + old);
				sLogger.debug("------new mGraph: " + mGraph.values());
			} else if (current.mBacking instanceof Call) {
				mCalls.pop();
				String old = mGraph.values().toString();
				mGraph = mGraphs.pop();
				sLogger.debug("----pop (call) " + current.mBacking);
				sLogger.debug("------old mGraph: " + old);
				sLogger.debug("------new mGraph: " + mGraph.values());
			}

			sLogger.debug("----change visit counter in mGraph: "
					+ current.mBacking);
			if (!mGraph.containsKey(current.mBacking)) {
				sLogger.debug("------not in current mGraph (so visit is 0): "
						+ current.mBacking);
			} else {
				// instead of removing, just reduce the visit counter by one
				// mGraph.remove(current.mBacking);
				mGraph.get(current.mBacking).mVisited--;
			}

			if (stop.equals(current)) {
				break;
			}
		}
		sLogger.debug("--trace prefix: " + traceToString(processed));
		sLogger.debug("--mCalls: " + mCalls);
		sLogger.debug("--mNestedLoops: " + mNestedLoops);
		sLogger.debug("--end backtracking--");
		sLogger.debug("");
	}

	protected void findLoopEntryExit(RCFGNode loopNode) {
		if (loopNode.getPayload().getLocation().isLoop()) {
			for (RCFGEdge potentialSelfLoop : loopNode.getOutgoingEdges()) {
				if (potentialSelfLoop.getTarget().equals(loopNode)) {
					addAnnotation(potentialSelfLoop, loopNode, true, true);
					return;
				}
			}

			for (RCFGEdge potentialEntryEdge : loopNode.getOutgoingEdges()) {
				RCFGEdge potentialBackEdge = findBackedge(potentialEntryEdge,
						loopNode, new HashSet<RCFGEdge>());
				if (potentialBackEdge != null) {
					addAnnotation(potentialEntryEdge, loopNode, true, false);
					addAnnotation(potentialBackEdge, loopNode, false, true);
				}
			}
		}
	}

	protected void addAnnotation(RCFGEdge edge, RCFGNode honda,
			boolean isEntry, boolean isExit) {
		new RCFGUnrollWalkerAnnotation(honda, isEntry, isExit)
				.addAnnotation(edge);
	}

	protected RCFGEdge findBackedge(RCFGEdge current, RCFGNode target,
			HashSet<RCFGEdge> visited) {
		if (current.getTarget().equals(target)) {
			return current;
		} else {
			visited.add(current);
			for (RCFGEdge succ : current.getTarget().getOutgoingEdges()) {
				if (!visited.contains(succ)) {
					RCFGEdge potential = findBackedge(succ, target, visited);
					if (potential != null
							&& potential.getTarget().equals(target)) {
						return potential;
					}
				}
			}
			return null;
		}
	}

	protected boolean isMaxCallDepth(RCFGEdge c) {
		int i = 0;
		for (RCFGEdge call : mCalls) {
			if (c.equals(call)) {
				++i;
			}
		}
		return i > mUnrollings;
	}

	protected boolean isMaxLoopDepth(ARTEdge c) {
		// c is nestedLoopEntry
		int i = 0;
		for (RCFGEdge loopEntries : mNestedLoops) {
			if (c.mBacking.equals(loopEntries)) {
				++i;
			}
		}
		return i > mUnrollings;
	}

	protected boolean isFeasible(RCFGEdge next) {
		if (next instanceof Summary) {
			return false;
		} else if (next instanceof Return) {
			if (mCalls.isEmpty()) {
				return false;
			} else {
				// TODO: search for the last return; necessary?
				return ((Return) next).getCorrespondingCall().equals(
						mCalls.peek());
			}
		}
		return true;
	}

	protected String traceToString(List<ARTEdge> trace) {
		StringBuilder sb = new StringBuilder();
		for (ARTEdge e : trace) {
			sb.append(e.mBacking);
			sb.append(" ");
		}
		return sb.toString();
	}

	protected ARTEdge createEdge(RCFGEdge edge) {
		ARTEdge currentNode;
		if (mGraph.containsKey(edge)) {
			currentNode = mGraph.get(edge);
		} else {
			currentNode = new ARTEdge(edge);
			mGraph.put(edge, currentNode);
		}
		return currentNode;
	}

	private class ARTEdge {
		private RCFGEdge mBacking;
		private int mVisited;
		private HashMap<RCFGEdge, ARTEdge> mLastGraphState;

		public ARTEdge(RCFGEdge backing) {
			mBacking = backing;
			mVisited = 1;
		}

		public void visit() {
			++mVisited;
		}

		public boolean isVisited(int unrolling) {
			return mVisited > unrolling;
		}

		public RCFGNode getTarget() {
			return mBacking.getTarget();
		}

		public RCFGNode getSource() {
			return mBacking.getSource();
		}

		@Override
		public String toString() {
			if (isLoopEntry() && isLoopExit()) {
				return mBacking.toString() + " (visited=" + mVisited
						+ ", isLoopEntry&Exit, honda=" + getLoopHead() + ")";
			}

			if (isLoopEntry()) {
				return mBacking.toString() + " (visited=" + mVisited
						+ ", isLoopEntry, honda=" + getLoopHead() + ")";
			}

			if (isLoopExit()) {
				return mBacking.toString() + " (visited=" + mVisited
						+ ", isLoopExit, honda=" + getLoopHead() + ")";
			}

			return mBacking.toString() + " (visited=" + mVisited + ")";

		}

		private boolean isLoopEntry() {
			RCFGUnrollWalkerAnnotation annot = getAnnotation();
			if (annot != null) {
				return annot.isLoopEntry();
			} else {
				return false;
			}
		}

		private boolean isLoopExit() {
			RCFGUnrollWalkerAnnotation annot = getAnnotation();
			if (annot != null) {
				return annot.isLoopExit();
			} else {
				return false;
			}
		}

		private boolean isNestedLoopEntry() {
			RCFGUnrollWalkerAnnotation annot = getAnnotation();
			if (annot != null) {
				return !annot.isLoopExit() && annot.isLoopEntry();
			} else {
				return false;
			}
		}

		private boolean isNestedLoopExit() {
			RCFGUnrollWalkerAnnotation annot = getAnnotation();
			if (annot != null) {
				return annot.isLoopExit() && !annot.isLoopEntry();
			} else {
				return false;
			}
		}

		private RCFGNode getLoopHead() {
			RCFGUnrollWalkerAnnotation annot = getAnnotation();
			if (annot != null) {
				return annot.getHonda();
			} else {
				return null;
			}
		}

		private RCFGUnrollWalkerAnnotation getAnnotation() {
			return IRSDependenciesAnnotation.getAnnotation(mBacking,
					IRSDependenciesAnnotation.class);
		}
	}

}
