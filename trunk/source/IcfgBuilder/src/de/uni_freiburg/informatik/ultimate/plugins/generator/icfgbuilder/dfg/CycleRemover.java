package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.dfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultStronglyConnectedComponentFactory;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

public class CycleRemover {

	// computes the feedback vertex Set for the given Dfg. Returns a List of IcfgEdges that can be removed in the
	// original Trace. Returns empty Set if no cycles are found.

	public static Set<IcfgEdge> computeFeedbackVertexSet(final DfgContainer dfg, final ILogger logger) {
		final Set<IcfgEdge> fvsHeuristic = computeFeedbackVertexHeuristic(dfg, logger);
		logger.info("Heuristic FVS found: Size: " + fvsHeuristic.size() + "and fvs = " + fvsHeuristic);

		if (isCyclic(dfg, logger)) {
			logger.debug("Cycles found");
			final Set<DfgNode> fvs = feedbackVertexBruteForce(dfg, logger);
			final Set<IcfgEdge> fvsEdges = fvs.stream().map(node -> node.getCorrespondingDFGEdge())
					.collect(Collectors.toSet());
			logger.info("Found Edges to remove:" + fvsEdges.size() + "and fvs = " + fvsEdges);
			logger.info("Heuristic is Same as optimal? " + fvsHeuristic.equals(fvsEdges));
			return fvsEdges;
		}
		logger.debug("No cycles found. Returning empty Set");
		return new HashSet<>();
	}

	private static Set<IcfgEdge> computeFeedbackVertexHeuristic(final DfgContainer dfg, final ILogger logger) {
		final ISuccessorProvider<DfgNode> successors = node -> {
			final Collection<DfgNode> successorsOfNode = dfg.getEdgeRelation().getImage(node);
			return successorsOfNode != null ? successorsOfNode.iterator() : Collections.emptyIterator();
		};
		final SccComputation<DfgNode, StronglyConnectedComponent<DfgNode>> scc = new SccComputation<>(logger,
				successors, new DefaultStronglyConnectedComponentFactory<>(), dfg.getNodeList().size(),
				dfg.getNodeList());
		final Set<IcfgEdge> fvs = new HashSet<>();
		for (final StronglyConnectedComponent<DfgNode> ball : scc.getBalls()) {
			// choose just any node of the ball
			final DfgNode node = ball.getNodes().iterator().next();
			fvs.add(node.getCorrespondingDFGEdge());
		}
		return fvs;
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
			logger.info(size);
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

	// clones the given Dfg
	// TODO maybe remove/refactor to work on copied edgeRelation/nodelist?
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
			final ArrayList<DfgNode> current, final List<List<DfgNode>> result) {
		if (current.size() == size) {
			result.add(new ArrayList<>(current));
			return;
		}
		for (int i = index; i < nodeList.size(); i++) {
			current.add(nodeList.get(i));
			backtrack(nodeList, size, i + 1, current, result);
			current.remove(current.size() - 1);
		}

	}

}
