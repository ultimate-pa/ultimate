/*
 * Copyright (C) 2025 Christof Schuster (christof.schuster@gmx.de)
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.dfg;

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
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * This class is used to build a Data Flow Graph of a given Boogie Control Flow Graph. This is used for trace
 * abstraction by forwarding it to the CycleRemover and obtaining IcfgEdges to be removed from the original Control Flow
 * Graph.
 *
 * @author christof.schuster@gmx.de
 */

public class DfgBuilder {

	/**
	 * Build a Data Flow Graph from a Root Node of a boogie Control Flow Graph.
	 *
	 * @param cfgRoot the root node of a Control Flow Graph as a IcfgLocation
	 * @param logger  the Logger
	 * @return a data flow graph in form of a node List and an edge relation
	 *
	 */
	public static DfgContainer buildDfg(final IcfgLocation cfgRoot, final ILogger logger) {
		final BuildContext context = new BuildContext(cfgRoot, logger);
		final DfgContainer dfg = context.buildDfg(false);
		return dfg;
	}

	/**
	 * Build a Data Flow Graph from a Root Node of a boogie Control Flow Graph, with the difference that "Uses" now also
	 * have edges to other "Uses"
	 *
	 * @param cfgRoot the root node of a Control Flow Graph as a IcfgLocation
	 * @param logger  the Logger
	 * @return a data flow graph in form of a node List and an edge relation
	 *
	 */
	public static DfgContainer buildDfgUseToUse(final IcfgLocation cfgRoot, final ILogger logger) {
		final BuildContext context = new BuildContext(cfgRoot, logger);
		final DfgContainer dfg = context.buildDfg(true);
		return dfg;
	}

	// private static class that represents the buildcontext, containing auxiliary datastructures => so I dont have to
	// clear them every time I call buildDfg

	private static class BuildContext {
		private final Set<DfgNode> mNodeList = new HashSet<>();
		private final Map<DfgNode, Set<IProgramVar>> mDefMap = new HashMap<>();
		private final Map<DfgNode, Set<IProgramVar>> mUnDefMap = new HashMap<>();
		private final Map<DfgNode, Set<IProgramVar>> mUseMap = new HashMap<>();
		private final Map<IcfgEdge, DfgNode> mEdgeBacklinks = new HashMap<>();
		private final HashRelation<DfgNode, DfgNode> mEdgeRelation = new HashRelation<>();
		private final ILogger mLogger;
		private final IcfgLocation mCfgRootNode;

		private BuildContext(final IcfgLocation cfgRootNode, final ILogger logger) {
			mCfgRootNode = cfgRootNode;
			mLogger = logger;
		}

		private DfgContainer buildDfg(final boolean useToUse) {
			buildNodeList();
			mLogger.info("Built Nodelist");
			defUseAnalysis();
			mLogger.info("Completed DefUseAnalysis");
			if (useToUse) {
				generateEdgesUseToUse();
			} else {
				generateEdges();
			}
			mLogger.info("Generated Edges");
			return new DfgContainer(mEdgeRelation, mNodeList);
		}

		// traverses the CFG edges and creates a corresponding Node in the node list
		private void buildNodeList() {
			mLogger.debug("Handling " + mCfgRootNode.toString());
			// traverse CFG edges depth-first and get a list of DFG nodes
			final Set<IcfgEdge> visited = new HashSet<>();
			final Stack<IcfgLocation> stack = new Stack<>();
			stack.add(mCfgRootNode);
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
				mNodeList.add(node);
				mEdgeBacklinks.put(edge, node);
			}
		}

		/*
		 * determines for each node whether it uses or redefines a program variable. Use(x) ==> x is in InVars Def(x)
		 * ==> OutVar(x) != InVar(x)
		 *
		 */
		private void defUseAnalysis() {
			for (final DfgNode node : mNodeList) {
				final IcfgEdge edge = node.getCorrespondingDFGEdge();
				final UnmodifiableTransFormula transformula = edge.getTransformula();
				final Map<IProgramVar, TermVariable> inVars = transformula.getInVars();
				final Map<IProgramVar, TermVariable> outVars = transformula.getOutVars();
				for (final IProgramVar programVar : inVars.keySet()) {

					final TermVariable in = inVars.get(programVar);
					final TermVariable out = outVars.get(programVar); // may be null
					if (transformula.isHavocedIn(programVar)) {
						mUnDefMap.computeIfAbsent(node, k -> new HashSet<>()).add(programVar);
					} else if (!in.equals(out)) {
						mDefMap.computeIfAbsent(node, k -> new HashSet<>()).add(programVar);
						mUseMap.computeIfAbsent(node, k -> new HashSet<>()).add(programVar);
					} else {
						mUseMap.computeIfAbsent(node, k -> new HashSet<>()).add(programVar);
					}
				}

				for (final IProgramVar programVar : outVars.keySet()) {
					final TermVariable out = outVars.get(programVar);
					final TermVariable in = inVars.get(programVar); // may be null
					if (transformula.isHavocedOut(programVar)) {
						mUnDefMap.computeIfAbsent(node, k -> new HashSet<>()).add(programVar);
					} else if (!out.equals(in)) {
						mDefMap.computeIfAbsent(node, k -> new HashSet<>()).add(programVar);
					}
				}
				mDefMap.computeIfAbsent(node, k -> new HashSet<>()); // create empty set for easier implementation later
				mUnDefMap.computeIfAbsent(node, k -> new HashSet<>()); // create empty set for easier implementation
																		// later

			}
			mLogger.debug("def Map " + mDefMap.toString());
			mLogger.debug("use map " + mUseMap.toString());
			mLogger.debug("undef map " + mUnDefMap.toString());
		}

		private void generateEdges() {
			for (final DfgNode node : mNodeList) {
				// very naive Algorithm: One depth-first search for every def of a variable of a node
				if (mDefMap.containsKey(node)) {
					for (final IProgramVar programVar : mDefMap.get(node)) {
						final Set<DfgNode> children = searchNeighbors(node, programVar);
						mEdgeRelation.addAllPairs(node, children);
					}
				}
				if (mUnDefMap.containsKey(node)) {
					for (final IProgramVar programVar : mUnDefMap.get(node)) {
						final Set<DfgNode> havocDefs = searchHavocDefs(node, programVar);
						for (final DfgNode havocDef : havocDefs) {
							final Set<DfgNode> children = searchNeighbors(havocDef, programVar);
							mEdgeRelation.addAllPairs(havocDef, children);
						}
					}
				}

			}
		}

		private void generateEdgesUseToUse() {
			for (final DfgNode node : mNodeList) {
				// very naive Algorithm: One depth-first search for every def of a variable of a node
				if (mDefMap.containsKey(node)) {
					for (final IProgramVar programVar : mDefMap.get(node)) {
						final Set<DfgNode> children = searchNeighbors(node, programVar);
						mEdgeRelation.addAllPairs(node, children);
					}
				}
				if (mUnDefMap.containsKey(node)) {
					for (final IProgramVar programVar : mUnDefMap.get(node)) {
						final Set<DfgNode> havocDefs = searchHavocDefs(node, programVar);

						for (final DfgNode havocDef : havocDefs) {
							final Set<DfgNode> children = searchNeighbors(havocDef, programVar);
							mEdgeRelation.addAllPairs(havocDef, children);
						}
					}
				}
				if (mUseMap.containsKey(node)) {
					for (final IProgramVar programVar : mUseMap.get(node)) {
						final Set<DfgNode> children = searchNeighbors(node, programVar);
						mEdgeRelation.addAllPairs(node, children);
					}
				}
			}
		}

		private Set<DfgNode> searchNeighbors(final DfgNode node, final IProgramVar programVar) {
			mLogger.debug("Searching Neighbors for Node " + node.toString() + " , ProgramVar " + programVar.toString());
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
						final DfgNode dfgNode = mEdgeBacklinks.get(nextEdge);
						if (mUseMap.containsKey(dfgNode) && mUseMap.get(dfgNode).contains(programVar)) {
							children.add(dfgNode);
						}
						if (mDefMap.containsKey(dfgNode) && !mDefMap.get(dfgNode).contains(programVar)
								&& !mUnDefMap.get(dfgNode).contains(programVar)) {
							final IcfgLocation target = nextEdge.getTarget();
							stack.push(target);
						}

					}
				}
			}
			return children;
		}

		// for havocs, the next use is counted as a def
		private Set<DfgNode> searchHavocDefs(final DfgNode node, final IProgramVar programVar) {

			mLogger.debug(
					"Searching Havoc Defs for Node " + node.toString() + " , ProgramVar " + programVar.toString());
			final Set<DfgNode> havocDefs = new HashSet<>();
			final IcfgEdge edge = node.getCorrespondingDFGEdge();
			final Set<IcfgEdge> visited = new HashSet<>();
			final Stack<IcfgLocation> stack = new Stack<>();
			stack.add(edge.getTarget());
			while (!stack.isEmpty()) {
				final IcfgLocation nextCFGNode = stack.pop();
				for (final IcfgEdge nextEdge : nextCFGNode.getOutgoingEdges()) {
					if (!visited.contains(nextEdge)) {
						visited.add(nextEdge);
						final DfgNode dfgNode = mEdgeBacklinks.get(nextEdge);
						if (mUseMap.containsKey(dfgNode) && mUseMap.get(dfgNode).contains(programVar)) {
							havocDefs.add(dfgNode);
						} else if (mDefMap.containsKey(dfgNode) && !mDefMap.get(dfgNode).contains(programVar)
								&& !mUnDefMap.get(dfgNode).contains(programVar)) {
							final IcfgLocation target = nextEdge.getTarget();
							stack.push(target);
						}

					}
				}
			}
			return havocDefs;
		}

	}

}
