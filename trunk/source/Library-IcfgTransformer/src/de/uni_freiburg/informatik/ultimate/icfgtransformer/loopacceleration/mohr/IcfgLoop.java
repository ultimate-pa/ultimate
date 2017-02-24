package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.mohr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class IcfgLoop<INLOC extends IcfgLocation> {

	private final Set<IcfgLoop<INLOC>> mNestedLoops;
	private final Set<INLOC> mLoopbody;
	private final INLOC mHead;
	private final Set<INLOC> mNestedNodes;
	private final Set<ArrayList<IcfgEdge>> mPaths;

	public IcfgLoop() {
		mNestedLoops = new HashSet<>();
		mLoopbody = new HashSet<>();
		mHead = null;
		mNestedNodes = new HashSet<>();
		mPaths = new HashSet<>();
	}

	public IcfgLoop(final Set<INLOC> loopNodes, final INLOC head) {
		mNestedLoops = new HashSet<>();
		mLoopbody = new HashSet<>(loopNodes);
		mHead = head;
		mNestedNodes = new HashSet<>();
		mPaths = new HashSet<>();
	}

	public void addAll(final Set<INLOC> loopNodes) {
		mLoopbody.addAll(loopNodes);
	}

	public void addNestedLoop(final IcfgLoop<INLOC> loopNodes) {
		for (final IcfgLoop<INLOC> nestedLoop : mNestedLoops) {
			if (nestedLoop.contains(loopNodes.getHead())) {
				nestedLoop.addNestedLoop(loopNodes);
				mNestedNodes.addAll(loopNodes.getLoopbody());
				return;
			}
		}

		mNestedLoops.add(loopNodes);
	}

	public boolean hasNestedLoops() {
		return !mNestedLoops.isEmpty();
	}

	public Set<IcfgLoop<INLOC>> getNestedLoops() {
		return mNestedLoops;
	}

	public Set<INLOC> getLoopbody() {
		return mLoopbody;
	}

	public INLOC getHead() {
		return mHead;
	}

	public boolean contains(final INLOC node) {
		return mLoopbody.contains(node);
	}

	public Set<ArrayList<IcfgEdge>> getPaths() {
		if (mPaths.isEmpty()) {
			loopPaths();
		}

		return mPaths;
	}

	@SuppressWarnings("unchecked")
	private void loopPaths() {
		final Deque<ArrayList<IcfgEdge>> queue = new ArrayDeque<>();
		for (final IcfgEdge edge : mHead.getOutgoingEdges()) {
			if (mLoopbody.contains(edge.getTarget())) {
				final ArrayList<IcfgEdge> a = new ArrayList<>();
				a.add(edge);
				queue.add(a);
			}
		}

		while (!queue.isEmpty()) {
			final ArrayList<IcfgEdge> path = queue.removeFirst();
			final INLOC destination = (INLOC) path.get(path.size() - 1).getTarget();
			if (destination.equals(mHead)) {
				mPaths.add(path);
				continue;
			}
			for (final IcfgEdge edge : destination.getOutgoingEdges()) {
				if (!mNestedNodes.contains(edge.getTarget()) && mLoopbody.contains(edge.getTarget())) {
					final ArrayList<IcfgEdge> addPath = new ArrayList<>(path);
					addPath.add(edge);
					queue.add(addPath);
				}
			}
		}
	}

}
