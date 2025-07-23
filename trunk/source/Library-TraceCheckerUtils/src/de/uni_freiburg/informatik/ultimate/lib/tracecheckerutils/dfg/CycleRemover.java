package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.dfg;

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

/**
 * This class is used to solve the feedback vertex problem of Boogie Data Flow Graphs. It does so by only considering
 * nodes that are in cycles. A heuristic and an exact solution are provided as a list of the IcfgEdges of the Data Flow
 * Graph Nodes.
 *
 * @author christof.schuster@gmx.de
 */
public class CycleRemover {

	/**
	 * Computes all IcfgEdges that are in any loop in the given Dfg
	 *
	 * @param dfg    the Data Flow Graph to work on
	 * @param logger the Logger
	 * @return all IcfgEdges of the original Cfg that are in contained in some Dfg loop
	 */
	public static Set<IcfgEdge> getBallEdges(final DfgContainer dfg, final ILogger logger) {
		final ISuccessorProvider<DfgNode> successors = node -> {
			final Collection<DfgNode> successorsOfNode = dfg.getEdgeRelation().getImage(node);
			return successorsOfNode != null ? successorsOfNode.iterator() : Collections.emptyIterator();
		};
		final SccComputation<DfgNode, StronglyConnectedComponent<DfgNode>> scc = new SccComputation<>(logger,
				successors, new DefaultStronglyConnectedComponentFactory<>(), dfg.getNodeList().size(),
				dfg.getNodeList());

		final Set<DfgNode> cyclicNodes = new HashSet<>();
		for (final StronglyConnectedComponent<DfgNode> ball : scc.getBalls()) {
			cyclicNodes.addAll(ball.getNodes());
		}
		return cyclicNodes.stream().map(node -> node.getCorrespondingDFGEdge()).collect(Collectors.toSet());
	}

	/**
	 * Computes all IcfgEdges that are NOT in any loop in the given Dfg
	 *
	 * @param dfg    the Data Flow Graph to work on
	 * @param logger the Logger
	 * @return all IcfgEdges of the original Cfg that are NOT in contained in some Dfg loop
	 */
	public static Set<IcfgEdge> getOutsideBallEdges(final DfgContainer dfg, final ILogger logger) {
		final Set<IcfgEdge> ballEdges = getBallEdges(dfg, logger);
		final Set<DfgNode> nodeList = dfg.getNodeList();
		final Set<IcfgEdge> outsideBallEdges = nodeList.stream()
				.filter(node -> !ballEdges.contains(node.getCorrespondingDFGEdge()))
				.map(node -> node.getCorrespondingDFGEdge()).collect(Collectors.toSet());
		return outsideBallEdges;
	}

	/**
	 * Computes a (possibly non-optimal) feedback Vertex Set of the Data Flow Graph, by removing nodes iteratively from
	 * every non-trivial SCC of the graph, checking if the graph becomes cycle-free at every step
	 *
	 * @param dfg    the Data Flow Graph to work on
	 * @param logger the Logger
	 * @return the feedback Vertex Set as a Set of IcfgEdges that can be removed
	 */
	public static Set<IcfgEdge> computeFeedbackVertexHeuristic(final DfgContainer dfg, final ILogger logger) {
		final ISuccessorProvider<DfgNode> successors = node -> {
			final Collection<DfgNode> successorsOfNode = dfg.getEdgeRelation().getImage(node);
			return successorsOfNode != null ? successorsOfNode.iterator() : Collections.emptyIterator();
		};
		final SccComputation<DfgNode, StronglyConnectedComponent<DfgNode>> scc = new SccComputation<>(logger,
				successors, new DefaultStronglyConnectedComponentFactory<>(), dfg.getNodeList().size(),
				dfg.getNodeList());
		final Set<IcfgEdge> fvs = new HashSet<>();
		Collection<StronglyConnectedComponent<DfgNode>> balls = scc.getBalls();
		final DfgContainer cloned = cloneDfg(dfg);
		while (balls.size() > 0) {
			for (final StronglyConnectedComponent<DfgNode> ball : balls) {
				// choose just any node of the ball
				final DfgNode node = ball.getNodes().iterator().next();
				fvs.add(node.getCorrespondingDFGEdge());
				cloned.getEdgeRelation().removeDomainElement(node);
				cloned.getEdgeRelation().removeRangeElement(node);
				cloned.getNodeList().remove(node);
			}
			final ISuccessorProvider<DfgNode> successorsCloned = node -> {
				final Collection<DfgNode> successorsOfNode = cloned.getEdgeRelation().getImage(node);
				return successorsOfNode != null ? successorsOfNode.iterator() : Collections.emptyIterator();
			};
			final SccComputation<DfgNode, StronglyConnectedComponent<DfgNode>> sccCloned = new SccComputation<>(logger,
					successorsCloned, new DefaultStronglyConnectedComponentFactory<>(), cloned.getNodeList().size(),
					cloned.getNodeList());
			balls = sccCloned.getBalls();
		}

		return fvs;
	}

	/**
	 * Computes the optimal feedback Vertex Set of the Data Flow Graph, by trying every combination of nodes that can be
	 * removed
	 *
	 * @param originalDfg the Data Flow Graph to work on
	 * @param logger      the Logger
	 * @return the feedback Vertex Set as a Set of IcfgEdges that can be removed
	 */
	public static Set<IcfgEdge> computeFeedbackVertexBruteForce(final DfgContainer originalDfg, final ILogger logger) {
		final ISuccessorProvider<DfgNode> successors = node -> {
			final Collection<DfgNode> successorsOfNode = originalDfg.getEdgeRelation().getImage(node);
			return successorsOfNode != null ? successorsOfNode.iterator() : Collections.emptyIterator();
		};
		final SccComputation<DfgNode, StronglyConnectedComponent<DfgNode>> scc = new SccComputation<>(logger,
				successors, new DefaultStronglyConnectedComponentFactory<>(), originalDfg.getNodeList().size(),
				originalDfg.getNodeList());

		final Set<DfgNode> cyclicNodes = new HashSet<>();
		if (scc.getBalls().size() == 0) {
			logger.info("Found no Cycles, returning empty Set");
			return new HashSet<>();
		}
		for (final StronglyConnectedComponent<DfgNode> ball : scc.getBalls()) {
			cyclicNodes.addAll(ball.getNodes());
		}
		final List<DfgNode> cyclicNodeList = new ArrayList<>(cyclicNodes);
		final int n = cyclicNodeList.size();
		final Set<DfgNode> bestSolution;
		// try all subsets in increasing size
		for (int size = 1; size <= n; size++) {
			logger.debug("Checking all subsets of size " + size);
			final List<List<DfgNode>> subsets = generateSubsetsOfSize(cyclicNodeList, size);
			for (final List<DfgNode> subset : subsets) {
				final DfgContainer cloned = cloneDfg(originalDfg);
				for (final DfgNode node : subset) {
					cloned.getEdgeRelation().removeDomainElement(node);
					cloned.getEdgeRelation().removeRangeElement(node);
					cloned.getNodeList().remove(node);
				}
				if (!isCyclic(cloned, logger)) {
					bestSolution = new HashSet<>(subset);
					final Set<IcfgEdge> fvsEdges = bestSolution.stream().map(node -> node.getCorrespondingDFGEdge())
							.collect(Collectors.toSet());
					return fvsEdges;
				}
			}
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

	// clones the given Dfg
	// TODO maybe remove/refactor to work on copied edgeRelation/nodelist to save memory?
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
