package de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.dfg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class DfgBuilder {
	private final Set<DFGNode> nodeList;
	private IcfgLocation cfgRootNode;
	private final Map<DFGNode, Set<IProgramVar>> defMap;
	private final Map<DFGNode, Set<IProgramVar>> useMap;
	private final Map<IcfgEdge, DFGNode> edgeBacklinks;
	private final HashRelation<DFGNode, DFGNode> edgeRelation;

	public DfgBuilder() {
		nodeList = new HashSet<>();
		edgeRelation = new HashRelation<>();
		defMap = new HashMap<>();
		useMap = new HashMap<>();
		edgeBacklinks = new HashMap<>();
	}

	public DfgContainer buildDfg(final IcfgLocation cfgRoot) {
		cfgRootNode = cfgRoot;
		clearDataStructures();
		System.out.println("Cleared DataStructures");
		buildNodeList();
		System.out.println("Built Nodelist");
		defUseAnalysis();
		System.out.println("Completed DefUseAnalysis");
		generateEdges();
		System.out.println("Generated Edges");
		return new DfgContainer(edgeRelation, nodeList);
	}

	private void clearDataStructures() {
		nodeList.clear();
		defMap.clear();
		useMap.clear();
		edgeBacklinks.clear();
		edgeRelation.clear();
	}

	// traverses the CFG edges and creates a corresponding Node in the node list
	private void buildNodeList() {
		System.out.println("Handling " + cfgRootNode.toString());
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
			final DFGNode node = new DFGNode(edge);
			nodeList.add(node);
			edgeBacklinks.put(edge, node);
		}
	}

	// determines for each node whether it uses or redefines a program variable
	private void defUseAnalysis() {
		for (final DFGNode node : nodeList) {
			final IcfgEdge edge = node.getCorrespondingDFGEdge();
			final UnmodifiableTransFormula transformula = edge.getTransformula();
			final Set<IProgramVar> InVars = transformula.getInVars().keySet();
			// start with checking InVars
			for (final IProgramVar programVar : InVars) {
				useMap.computeIfAbsent(node, (k -> new HashSet<>())).add(programVar);
				if (transformula.getInVars().get(programVar) != transformula.getOutVars().get(programVar)) {
					defMap.computeIfAbsent(node, (k -> new HashSet<>())).add(programVar);
				} else if (transformula.getAssignedVars().contains(programVar)) {
					// does this cover assume statement? => siehe dings.bpl
					defMap.computeIfAbsent(node, (k -> new HashSet<>())).add(programVar);
				}
			}
			final Set<IProgramVar> OutVars = transformula.getOutVars().keySet();
			for (final IProgramVar programVar : OutVars) {
				if (transformula.getInVars().get(programVar) == null) {
					defMap.computeIfAbsent(node, (k -> new HashSet<>())).add(programVar);
				}
			}
		}
		System.out.println("def Map " + defMap.toString());
		System.out.println("use map " + useMap.toString());
	}

	private void generateEdges() {
		for (final DFGNode node : nodeList) {
			// very naive Algorithm: One depth-first search for every def of a variable of a node
			if (defMap.containsKey(node)) {
				for (final IProgramVar programVar : defMap.get(node)) {
					final Set<DFGNode> children = searchNeighbors(node, programVar);
					edgeRelation.addAllPairs(node, children);
				}
			}
		}
	}

	private Set<DFGNode> searchNeighbors(final DFGNode node, final IProgramVar programVar) {
		System.out
				.println("Searching Neighbors for Node " + node.toString() + " , ProgramVar " + programVar.toString());
		final Set<DFGNode> children = new HashSet<>();
		final IcfgEdge edge = node.getCorrespondingDFGEdge();
		final Set<IcfgEdge> visited = new HashSet<>();
		final Stack<IcfgLocation> stack = new Stack<>();
		stack.add(edge.getTarget());
		while (!stack.isEmpty()) {
			final IcfgLocation nextCFGNode = stack.pop();
			for (final IcfgEdge nextEdge : nextCFGNode.getOutgoingEdges()) {
				if (!visited.contains(nextEdge)) {
					visited.add(nextEdge);
					final DFGNode dfgNode = edgeBacklinks.get(nextEdge);
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
