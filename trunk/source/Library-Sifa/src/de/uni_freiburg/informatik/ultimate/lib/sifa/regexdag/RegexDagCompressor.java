/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.models.IDirectedGraph;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;

/**
 * Compresses RegexDags by merging nodes while conserving the DAG's language.
 * Use {@link #compress(RegexDag)} to compress a single DAG in-place.
 *
 * @author schaetzc@tf.uni-freiburg.de
 *
 * @param <L> Type of letters that are used inside regex literals
 */
public class RegexDagCompressor<L> {

	/**
	 * Temporary table for grouping predecessors/successors of a node before merging each group.
	 * Could also be a local variable, but recycling an existing map is more efficient than
	 * creating a new one each time.
	 */
	private final Map<IRegex<L>, Set<RegexDagNode<L>>> mMergetable = new LinkedHashMap<>();

	/**
	 * Some nodes where merged in the last iteration over the whole graph.
	 */
	private boolean mMergedFlag;

	/**
	 * The RegexDag currently being compressed in-place.
	 */
	private RegexDag<L> mDag;

	/**
	 * Compresses a single DAG in-place by merging nodes while conserving the DAG's language.
	 * <p>
	 * The compression is just "best effort":
	 * <ul>
	 * <li> The resulting DAG is not necessarily the minimum DAG.
	 *      Sometimes an equivalent DAG with less nodes exists.
	 * <li> The resulting DAG has no canonical form.
	 *      Compressing two equivalent (but different) DAGs can yield different (but equivalent) results.
	 * </ul>
	 * However, the compression is idempotent. In other words, compressing an already compressed DAG again has no effect.
	 *
	 *
	 * @param dag DAG to be compressed in-place
	 * @return The same DAG (now compressed)
	 */
	public RegexDag<L> compress(final RegexDag<L> dag) {
		mDag = dag;
		mMergedFlag = true;
		while (mMergedFlag) {
			mMergedFlag = false;
			searchAndMerge(mDag.getSource(), RegexDagNode::getOutgoingNodes, RegexDagNode::getIncomingNodes);
			searchAndMerge(mDag.getSink(), RegexDagNode::getIncomingNodes, RegexDagNode::getOutgoingNodes);
		}
		return mDag;
	}

	private void searchAndMerge(final RegexDagNode<L> startNode,
			final Function<RegexDagNode<L>, Collection<RegexDagNode<L>>> neighborsInSearchDirection,
			final Function<RegexDagNode<L>, Collection<RegexDagNode<L>>> neighborsInOtherDirection) {
		final Set<RegexDagNode<L>> visited = new HashSet<>();
		final Queue<RegexDagNode<L>> worklist = new ArrayDeque<>();
		visited.add(startNode);
		worklist.add(startNode);
		while (!worklist.isEmpty()) {
			final RegexDagNode<L> predator = worklist.remove();
			mergeInDirection(predator, neighborsInSearchDirection, neighborsInOtherDirection);
			neighborsInSearchDirection.apply(predator).stream().filter(visited::add).forEach(worklist::add);
			eliminateIfEpsilon(predator);
		}
	}

	private void mergeInDirection(final RegexDagNode<L> baseNode,
			final Function<RegexDagNode<L>, Collection<RegexDagNode<L>>> directionBaseToCandidates,
			final Function<RegexDagNode<L>, Collection<RegexDagNode<L>>> directionCandidatesToBase) {
		mMergetable.clear();
		safeCandidates(baseNode, directionBaseToCandidates)
				.forEach(this::addToMergetable);
		mMergetable.entrySet().stream()
				.forEach(this::groupToSingleNode);
	}

	/**
	 * Selects a group of candidates that never creates cycles when being merged in any way.
	 * <p>
	 * For example, consider the following graph during forward merging.
	 * <pre>
	 *     ,––→ a ·············.
	 *   base → b → c –,→ d ·····→ sink
	 *     `––––––––––´
	 * </pre>
	 * Here the candidates {a, b} are selected. If d was also selected we could merge it with b which would
	 * result in graph with cycles. Our selection process is just one of many. We could also select {a, d}, just {a},
	 * or even {} – more research is needed on what to select to get the best compression results.
	 *
	 * @return Either successors or predecessors (depending on direction) of a base node that can be merged without
	 *         creating a cycle. Whether to merge or not still has to be decided based on the node labels.
	 */
	private Set<RegexDagNode<L>> safeCandidates(final RegexDagNode<L> base,
			final Function<RegexDagNode<L>, Collection<RegexDagNode<L>>> directionBaseToCandidates) {
		final Set<RegexDagNode<L>> candidates = new LinkedHashSet<>(directionBaseToCandidates.apply(base));
		candidates.removeAll(IDirectedGraph.transitiveNodes(candidates, directionBaseToCandidates));
		return candidates;
	}

	private void addToMergetable(final RegexDagNode<L> node) {
		mMergetable.computeIfAbsent(node.getContent(), key -> new LinkedHashSet<>()).add(node);
	}

	private RegexDagNode<L> groupToSingleNode(final Map.Entry<IRegex<L>, Set<RegexDagNode<L>>> labelToMergeGroup) {
		if (labelToMergeGroup.getValue().size() == 1) {
			return labelToMergeGroup.getValue().iterator().next();
		}
		return groupToNewNode(labelToMergeGroup.getKey(), labelToMergeGroup.getValue());
	}

	private RegexDagNode<L> groupToNewNode(final IRegex<L> newLabel, final Set<RegexDagNode<L>> mergeGroup) {
		final RegexDagNode<L> merged = new RegexDagNode<>(newLabel);
		mergeGroup.forEach(nodeToBeMerged -> merge(merged, nodeToBeMerged));
		return merged;
	}

	/**
	 * Merges two nodes by contracting one node (prey) into another (predator).
	 * <p>
	 * Copies incoming and outgoing edges from the pray node to the predator
	 * without creating new parallel edges or selfloops.
	 * <p>
	 * Unlinks the pray node from all its neighbors but not vice versa, that is,
	 * the prey node still has references to its former neighbors
	 * but the neighbors don't have references to the prey node.
	 *
	 * @param predator Node surviving the merge
	 * @param prey Node to be consumed by the predator
	 */
	private void merge(final RegexDagNode<L> predator, final RegexDagNode<L> prey) {
		mMergedFlag = true;

		prey.getIncomingNodes().stream().forEach(in -> in.removeOutgoing(prey));
		prey.getOutgoingNodes().stream().forEach(out -> out.removeIncoming(prey));
		// no need to delete prey's references to incoming and outgoing nodes -- prey is deleted anyway

		final Set<RegexDagNode<L>> ignore = new HashSet<>(predator.getIncomingNodes());
		ignore.add(predator);
		prey.getIncomingNodes().stream().filter(n -> !ignore.contains(n)).forEach(predator::connectIncoming);
		ignore.clear();

		ignore.addAll(predator.getOutgoingNodes());
		ignore.add(predator);
		prey.getOutgoingNodes().stream().filter(n -> !ignore.contains(n)).forEach(predator::connectOutgoing);

		if (prey == mDag.getSink()) {
			mDag.setSink(predator);
		}
		if (prey == mDag.getSource()) {
			mDag.setSource(predator);
		}
	}

	private void eliminateIfEpsilon(final RegexDagNode<L> epsilon) {
		if (!epsilon.isEpsilon()) {
			return;
		}
		List<RegexDagNode<L>> in = epsilon.getIncomingNodes();
		List<RegexDagNode<L>> out = epsilon.getOutgoingNodes();
		if (in.isEmpty() && out.isEmpty()) {
			return;
		} else if (epsilon == mDag.getSource()) {
			if (out.size() > 1) {
				// this epsilon cannot be eliminated
				return;
			}
			mDag.setSource(out.get(0));
		} else if (epsilon == mDag.getSink()) {
			if (in.size() > 1) {
				// this epsilon cannot be eliminated
				return;
			}
			mDag.setSink(in.get(0));
		}
		// copy lists to allow concurrent iteration and modification
		in = new ArrayList<>(in);
		out = new ArrayList<>(out);
		for (final RegexDagNode<L> inNode : in) {
			for (final RegexDagNode<L> outNode : out) {
				inNode.connectOutgoing(outNode);
			}
		}
		in.forEach(epsIn -> epsIn.removeOutgoing(epsilon));
		out.forEach(epsOut -> epsOut.removeIncoming(epsilon));
		// no need to delete epsilon's references to incoming and outgoing nodes -- epsilon is deleted anyway
	}

}

















