package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.dfg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class DfgBuilder {

	public static DfgContainer buildDfg(final IcfgLocation cfgRoot, final ILogger logger) {
		final BuildContext context = new BuildContext(cfgRoot, logger);
		final DfgContainer dfg = context.buildDfg();
		return dfg;
	}

	// private static class that represents the buildcontext, containing auxiliary datastructures => so I dont have to
	// clear them every time I call buildDfg

	private static class BuildContext {
		private final Set<DfgNode> nodeList = new HashSet<>();
		private final Map<DfgNode, Set<IProgramVar>> defMap = new HashMap<>();
		private final Map<DfgNode, Set<IProgramVar>> useMap = new HashMap<>();
		private final Map<IcfgEdge, DfgNode> edgeBacklinks = new HashMap<>();
		private final HashRelation<DfgNode, DfgNode> edgeRelation = new HashRelation<>();
		private final ILogger logger;
		private final IcfgLocation cfgRootNode;

		public BuildContext(final IcfgLocation cfgRootNode, final ILogger logger) {
			this.cfgRootNode = cfgRootNode;
			this.logger = logger;
		}

		public DfgContainer buildDfg() {
			buildNodeList();
			logger.info("Built Nodelist");
			defUseAnalysis();
			logger.info("Completed DefUseAnalysis");
			generateEdges();
			logger.info("Generated Edges");
			return new DfgContainer(edgeRelation, nodeList);
		}

		// traverses the CFG edges and creates a corresponding Node in the node list
		private void buildNodeList() {
			logger.debug("Handling " + cfgRootNode.toString());
			// traverse CFG edges depth-first and get a list of DFG nodes
			final Set<IcfgEdge> visited = new HashSet<>();
			final Stack<IcfgLocation> stack = new Stack<>();
			stack.add(cfgRootNode);
			while (!stack.isEmpty()) {
				final IcfgLocation node = stack.pop();
				for (final IcfgEdge edge : node.getOutgoingEdges()) {
					if (!visited.contains(edge)) {
						visited.add(edge);
						final IcfgLocation target = edge.getTarget();
						stack.push(target);
					}
				}
			}
			// we also keep a mapping backwards so its easier generating edges in the dfg
			for (final IcfgEdge edge : visited) {
				final DfgNode node = new DfgNode(edge);
				nodeList.add(node);
				edgeBacklinks.put(edge, node);
			}
		}

		/*
		 * determines for each node whether it uses or redefines a program variable Use(x) ==> x is in InVars Def(x) ==>
		 * x is in OutVars(x) or x is in InVars but not in OutVars (havoc x)
		 *
		 */
		private void defUseAnalysis() {
			for (final DfgNode node : nodeList) {
				final IcfgEdge edge = node.getCorrespondingDFGEdge();
				final UnmodifiableTransFormula transformula = edge.getTransformula();
				final Set<IProgramVar> InVars = transformula.getInVars().keySet();
				for (final IProgramVar programVar : InVars) {
					useMap.computeIfAbsent(node, (k -> new HashSet<>())).add(programVar);
					if (transformula.getOutVars().get(programVar) != null) {
						defMap.computeIfAbsent(node, (k -> new HashSet<>())).add(programVar);
					}
				}
				final Set<IProgramVar> OutVars = transformula.getOutVars().keySet();
				defMap.computeIfAbsent(node, (k -> new HashSet<>())).addAll(OutVars);
			}
			logger.debug("def Map " + defMap.toString());
			logger.debug("use map " + useMap.toString());
		}

		private void generateEdges() {
			for (final DfgNode node : nodeList) {
				// very naive Algorithm: One depth-first search for every def of a variable of a node
				if (defMap.containsKey(node)) {
					for (final IProgramVar programVar : defMap.get(node)) {
						final Set<DfgNode> children = searchNeighbors(node, programVar);
						edgeRelation.addAllPairs(node, children);
					}
				}
			}
		}

		private Set<DfgNode> searchNeighbors(final DfgNode node, final IProgramVar programVar) {
			logger.debug("Searching Neighbors for Node " + node.toString() + " , ProgramVar " + programVar.toString());
			final Set<DfgNode> children = new HashSet<>();
			final IcfgEdge edge = node.getCorrespondingDFGEdge();
			final Set<IcfgEdge> visited = new HashSet<>();
			final Stack<IcfgLocation> stack = new Stack<>();
			stack.add(edge.getTarget());
			while (!stack.isEmpty()) {
				final IcfgLocation nextCFGNode = stack.pop();
				for (final IcfgEdge nextEdge : nextCFGNode.getOutgoingEdges()) {
					if (!visited.contains(nextEdge)) {
						visited.add(nextEdge);
						final DfgNode dfgNode = edgeBacklinks.get(nextEdge);
						if (useMap.containsKey(dfgNode) && useMap.get(dfgNode).contains(programVar)) {
							children.add(dfgNode);
						}
						// if we redefine it then we don't have to search here further
						if (defMap.containsKey(dfgNode) && !defMap.get(dfgNode).contains(programVar)) {
							final IcfgLocation target = nextEdge.getTarget();
							stack.push(target);
						}

					}
				}
			}
			return children;
		}

	}

}
