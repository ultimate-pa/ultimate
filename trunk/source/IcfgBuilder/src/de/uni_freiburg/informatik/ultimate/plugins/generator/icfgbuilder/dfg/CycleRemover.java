package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.dfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultStronglyConnectedComponentFactory;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

public class CycleRemover {

	public static List<IcfgEdge> computeFeedbackVertexSet(final DfgContainer dfg, final ILogger logger) {
		if (isCyclic(dfg, logger)) {
			logger.debug("Cycles found");
			logger.debug(feedbackVertexBruteForce(dfg, logger));
			logger.debug("Erfolg, found Nodes");
		} else {
			logger.debug("No cycles found");
		}
		return null;
	}

	// returns whether the given Dfg is cyclic, if the number of SCCs of the Dfg are the trivial size then it is not
	// cyclic
	private static boolean isCyclic(final DfgContainer dfg, final ILogger logger) {
		// TODO Auto-generated method stub
		final ISuccessorProvider<DfgNode> successors = node -> {
			final Collection<DfgNode> successorsOfNode = dfg.getEdgeRelation().getImage(node);
			return successorsOfNode != null ? successorsOfNode.iterator() : Collections.emptyIterator();
		};
		final SccComputation<DfgNode, StronglyConnectedComponent<DfgNode>> scc = new SccComputation<>(logger,
				successors, new DefaultStronglyConnectedComponentFactory<>(), dfg.getNodeList().size(),
				dfg.getNodeList());
		return scc.getBalls().size() > 0;
	}

	// naive implementation of the feedbackVertexSet Problem, Brute Force all possible subsets and check for acyclity
	// starting from least nodes removed so I can terminate early
	private static Set<DfgNode> feedbackVertexBruteForce(final DfgContainer originalDfg, final ILogger logger) {
		final Set<DfgNode> nodes = originalDfg.getNodeList();
		final List<DfgNode> nodeList = new ArrayList<>(nodes);
		final int n = nodeList.size();
		final Set<DfgNode> bestSolution;
		// try all subsets in increasing size
		for (int size = 1; size <= n; size++) {
			final List<List<DfgNode>> subsets = generateSubsetsOfSize(nodeList, size);
			for (final List<DfgNode> subset : subsets) {
				final DfgContainer cloned = cloneDfg(originalDfg);
				for (final DfgNode node : subset) {
					cloned.getEdgeRelation().removeDomainElement(node);
					cloned.getEdgeRelation().removeRangeElement(node);
					cloned.getNodeList().remove(node);
				}
				if (!isCyclic(cloned, logger)) {
					bestSolution = new HashSet<>(subset);
					return bestSolution;
				}
			}
		}

		return null;
	}

	// maybe refactorn so i dont have to clone and just delete and add nodes directly on the copied
	// edgerelation/nodelist?
	private static DfgContainer cloneDfg(final DfgContainer originalDfg) {
		final Set<DfgNode> newNodeList = new HashSet<>(originalDfg.getNodeList());
		final HashRelation<DfgNode, DfgNode> originalEdges = originalDfg.getEdgeRelation();
		final HashRelation<DfgNode, DfgNode> newEdgeRelation = new HashRelation<>();
		newEdgeRelation.addAll(originalEdges);
		return new DfgContainer(newEdgeRelation, newNodeList);
	}

	// recursively generate all subsets of size "size"
	private static List<List<DfgNode>> generateSubsetsOfSize(final List<DfgNode> nodeList, final int size) {
		final List<List<DfgNode>> result = new ArrayList<>();
		backtrack(nodeList, size, 0, new ArrayList<>(), result);
		return result;
	}

	// helper function to recursively generate all subsets of size "size"
	private static void backtrack(final List<DfgNode> nodeList, final int size, final int index,
			final ArrayList current, final List<List<DfgNode>> result) {
		if (current.size() == size) {
			result.add(new ArrayList<>(current));
			return;
		}
		for (int i = index; i < nodeList.size(); i++) {
			current.add(nodeList.get(i));
			backtrack(nodeList, size, index + 1, current, result);
			current.remove(current.size() - 1);
		}

	}

}
