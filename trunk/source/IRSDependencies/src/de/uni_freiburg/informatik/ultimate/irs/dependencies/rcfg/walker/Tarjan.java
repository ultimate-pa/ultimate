package de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.walker;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class Tarjan {
	private HashMap<RCFGNode, VerticeDecorator> mVerticeIndices;
	private HashSet<RCFGNode> mUnfinishedVertices;
	private int mCurrentIndex;
	private Stack<RCFGNode> mCurrentComponent;
	private LinkedList<SCC> mComponents;
	private HashSet<RCFGEdge> mForbiddenEdges;

	public Tarjan() {
		init();
	}

	public Tarjan(List<RCFGEdge> forbiddenEdges) {
		init();
		mForbiddenEdges.addAll(forbiddenEdges);
	}

	private void init() {
		mVerticeIndices = new HashMap<RCFGNode, VerticeDecorator>();
		mUnfinishedVertices = new HashSet<>();
		mCurrentIndex = 0;
		mCurrentComponent = new Stack<>();
		mComponents = new LinkedList<>();
		mForbiddenEdges = new HashSet<>();
	}

	public LinkedList<SCC> computeStronglyConnectedComponents(RCFGNode node) {
		if (!mComponents.isEmpty()) {
			init();
		}

		computeVertices(node);

		for (RCFGNode currentVertice : mUnfinishedVertices) {
			VerticeDecorator currentVerticeDecorator = mVerticeIndices
					.get(currentVertice);
			if (currentVerticeDecorator.index == -1) {
				computeComponents(currentVertice, currentVerticeDecorator);
			}
		}

		return mComponents;
	}

	/**
	 * Collects all vertices reachable from a given root node with a recursive
	 * depth-first preorder search.
	 * 
	 * Initializes mUnfinishedVertices and mVerticeIndices.
	 * 
	 * @param node
	 */
	private void computeVertices(RCFGNode node) {
		if (mUnfinishedVertices.contains(node)) {
			return;
		}

		mUnfinishedVertices.add(node);
		mVerticeIndices.put(node, new VerticeDecorator());

		for (RCFGEdge edge : node.getOutgoingEdges()) {
			if (!mForbiddenEdges.contains(edge)) {
				computeVertices(edge.getTarget());
			}
		}
	}

	private void computeComponents(RCFGNode currentVertice,
			VerticeDecorator currentVerticeDecorator) {
		// Set the depth index for currentVertice to the smallest unused index
		currentVerticeDecorator.index = mCurrentIndex;
		currentVerticeDecorator.lowlink = mCurrentIndex;
		++mCurrentIndex;
		mCurrentComponent.push(currentVertice);

		// Consider successors of currentVertice
		for (RCFGEdge possibleSuccessorEdge : currentVertice.getOutgoingEdges()) {
			if (!isAdmissible(possibleSuccessorEdge)) {
				continue;
			}

			RCFGNode succesor = possibleSuccessorEdge.getTarget();
			VerticeDecorator succesorVerticeDecorator = mVerticeIndices
					.get(succesor);
			if (succesorVerticeDecorator.index == -1) {
				// Successor has not yet been visited; recurse on it
				// First, save call correspondence
				// preserveCallReturnCorrespondence(possibleSuccessorEdge);
				computeComponents(succesor, succesorVerticeDecorator);
				currentVerticeDecorator.lowlink = Math.min(
						currentVerticeDecorator.lowlink,
						succesorVerticeDecorator.lowlink);
			} else if (mCurrentComponent.contains(succesor)) {
				// Successor is on the stack and hence in the current SCC
				currentVerticeDecorator.lowlink = Math.min(
						currentVerticeDecorator.lowlink,
						succesorVerticeDecorator.index);
			}
		}

		// If currentVertice is a root node, pop the stack and generate an SCC
		if (currentVerticeDecorator.lowlink == currentVerticeDecorator.index) {
			SCC newComponent = new SCC();
			RCFGNode member = null;
			while (member != currentVertice) {
				member = mCurrentComponent.pop();
				newComponent.add(member);
			}
			mComponents.add(newComponent);
		}
	}

	private boolean isAdmissible(RCFGEdge possibleSuccessorEdge) {
		if (possibleSuccessorEdge instanceof Summary) {
			return false;
		}
		if(mForbiddenEdges.contains(possibleSuccessorEdge)){
			return false;
		}
		return true;
	}

	private class VerticeDecorator {

		private VerticeDecorator() {
			index = -1;
			lowlink = -1;
		}

		public int index;
		public int lowlink;
	}
}
