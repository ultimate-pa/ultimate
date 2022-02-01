/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.walker;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

public class Tarjan {
	private HashMap<IcfgLocation, VerticeDecorator> mVerticeIndices;
	private HashSet<IcfgLocation> mUnfinishedVertices;
	private int mCurrentIndex;
	private Stack<IcfgLocation> mCurrentComponent;
	private LinkedList<SCC> mComponents;
	private HashSet<IcfgEdge> mForbiddenEdges;

	public Tarjan() {
		init();
	}

	public Tarjan(final List<IcfgEdge> forbiddenEdges) {
		init();
		mForbiddenEdges.addAll(forbiddenEdges);
	}

	private void init() {
		mVerticeIndices = new HashMap<IcfgLocation, VerticeDecorator>();
		mUnfinishedVertices = new HashSet<>();
		mCurrentIndex = 0;
		mCurrentComponent = new Stack<>();
		mComponents = new LinkedList<>();
		mForbiddenEdges = new HashSet<>();
	}

	public LinkedList<SCC> computeStronglyConnectedComponents(final IcfgLocation node) {
		if (!mComponents.isEmpty()) {
			init();
		}

		computeVertices(node);

		for (final IcfgLocation currentVertice : mUnfinishedVertices) {
			final VerticeDecorator currentVerticeDecorator = mVerticeIndices
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
	private void computeVertices(final IcfgLocation node) {
		if (mUnfinishedVertices.contains(node)) {
			return;
		}

		mUnfinishedVertices.add(node);
		mVerticeIndices.put(node, new VerticeDecorator());

		for (final IcfgEdge edge : node.getOutgoingEdges()) {
			if (!mForbiddenEdges.contains(edge)) {
				computeVertices(edge.getTarget());
			}
		}
	}

	private void computeComponents(final IcfgLocation currentVertice,
			final VerticeDecorator currentVerticeDecorator) {
		// Set the depth index for currentVertice to the smallest unused index
		currentVerticeDecorator.index = mCurrentIndex;
		currentVerticeDecorator.lowlink = mCurrentIndex;
		++mCurrentIndex;
		mCurrentComponent.push(currentVertice);

		// Consider successors of currentVertice
		for (final IcfgEdge possibleSuccessorEdge : currentVertice.getOutgoingEdges()) {
			if (!isAdmissible(possibleSuccessorEdge)) {
				continue;
			}

			final IcfgLocation succesor = possibleSuccessorEdge.getTarget();
			final VerticeDecorator succesorVerticeDecorator = mVerticeIndices
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
			final SCC newComponent = new SCC();
			IcfgLocation member = null;
			while (member != currentVertice) {
				member = mCurrentComponent.pop();
				newComponent.add(member);
			}
			mComponents.add(newComponent);
		}
	}

	private boolean isAdmissible(final IcfgEdge possibleSuccessorEdge) {
		if (possibleSuccessorEdge instanceof Summary) {
			return false;
		}
		return (!(mForbiddenEdges.contains(possibleSuccessorEdge)));
	}

	private static final class VerticeDecorator {

		VerticeDecorator() {
			index = -1;
			lowlink = -1;
		}

		public int index;
		public int lowlink;
	}
}
