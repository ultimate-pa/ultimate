package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;

public class RegexDagCompressor<L> {

	private Map<IRegex<L>, Set<RegexDagNode<L>>> mMergetable = new HashMap<>();
	private boolean mMergedFlag;

	public RegexDag<L> compress(final RegexDag<L> dag) {
		mMergedFlag = true;
		while (mMergedFlag) {
			mMergedFlag = false;
			searchAndMerge(dag.getSource(), RegexDagNode::getOutgoingNodes, RegexDagNode::getIncomingNodes);
			searchAndMerge(dag.getSink(), RegexDagNode::getIncomingNodes, RegexDagNode::getOutgoingNodes);
		}
		return dag;
	}

	private void searchAndMerge(RegexDagNode<L> startNode,
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
		}
	}

	private void mergeInDirection(final RegexDagNode<L> baseNode,
			final Function<RegexDagNode<L>, Collection<RegexDagNode<L>>> directionBaseToCandidates,
			final Function<RegexDagNode<L>, Collection<RegexDagNode<L>>> directionCandidatesToBase) {
		mMergetable.clear();
		directionBaseToCandidates.apply(baseNode).stream()
				// ignore nodes that would result in a cycle after merge
				// also ensures that merges don't affect the workinglist
				.filter(prey -> directionCandidatesToBase.apply(prey).size() <= 1)
				.forEach(this::addToMergetable);
		mMergetable.entrySet().stream()
				.map(this::groupToSingleNode)
				.filter(RegexDagNode::isEpsilon).findFirst()
				.ifPresent(mergedEpsilonCandidates -> merge(baseNode, mergedEpsilonCandidates));
	}

	private void addToMergetable(final RegexDagNode<L> node) {
		mMergetable.computeIfAbsent(node.getContent(), key -> new HashSet<>()).add(node);
	}

	private RegexDagNode<L> groupToSingleNode(Map.Entry<IRegex<L>, Set<RegexDagNode<L>>> labelToMergeGroup) {
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
	 * Unlinks the pray node from all its neighbors but not vice verca, that is,
	 * the prey node still has references to its former neighbors
	 * but the neighbors don't have references to the prey node.
	 * 
	 * @param predator Node surviving the merge
	 * @param prey Node to be consumed by the predator
	 */
	private void merge(final RegexDagNode<L> predator, final RegexDagNode<L> prey) {
		mMergedFlag = true;

		prey.getIncomingNodes().stream().forEach(in -> in.removeOutgoing(this));
		prey.getOutgoingNodes().stream().forEach(out -> out.removeIncoming(this));
		// no need to delete prey's references to incoming and outgoing nodes -- prey is delete anyway

		Set<RegexDagNode<L>> ignore = new HashSet<>(predator.getIncomingNodes());
		ignore.add(predator);
		prey.getIncomingNodes().stream().filter(ignore::contains).forEach(predator::connectIncoming);
		ignore.clear();

		ignore.addAll(predator.getOutgoingNodes());
		ignore.add(predator);
		prey.getOutgoingNodes().stream().filter(ignore::contains).forEach(predator::connectOutgoing);
	}

}






















